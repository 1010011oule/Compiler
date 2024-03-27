open Program
open Error

(* our symbol table will be a mapping from 'string' to 'ctype_entry'. *)
type ctype_entry =
  | VarType of ctype
  | FuncType of ctype * ctype list (* return type * argument type list *)

module SymbolMap = Map.Make(String)

(*
 * the reasons we need this, even though 'ctype' is already defined:
 * if you encounter a wrong expression during the semantic analysis (for example "1 + true"),
 * we cannot decide its type but still may have to return something.
 *)

type typ = Void | Int | Bool | Unknown

let ctyp_to_typ ctyp =
  match ctyp with
  | CVoid -> Void
  | CInt -> Int
  | CBool -> Bool

let typ_to_ctyp ctyp =
  match ctyp with
  | Void -> CVoid
  | Int -> CInt
  | Bool -> CBool
  | Unknown -> (* raising exception *)
      failwith "Not allowed (You should not call this in such situation)"

(* recording the type of variables into the symbol table *)
let rec collect_vars decls sym_tab =
  match decls with
  | [] -> sym_tab
  | head_decl :: tail_decls ->
      let (ctyp, vname) = head_decl in
      let sym_tab = SymbolMap.add vname (VarType ctyp) sym_tab in
      collect_vars tail_decls sym_tab

(* recording the type of functions into the symbol table *)
let rec collect_functions funcs sym_tab =
  match funcs with
  | [] -> sym_tab
  | (fname, ret_typ, args, _) :: tail_funcs ->
    if SymbolMap.mem fname sym_tab then
      failwith ("Function '" ^ fname ^ "' already declared.")
    else
      let arg_types = List.map (fun (arg_type, _) -> arg_type) args in
      let func_type = FuncType (ret_typ, arg_types) in
      let sym_tab' = SymbolMap.add fname func_type sym_tab in collect_functions tail_funcs sym_tab'

(*
 * checking the expression 'e' and return detected semantic errors along with the
 * decided type of 'e'. If the type of the expression cannot be decided due to
 * semantic error, return 'Unknown' as its type
 *)

let rec check_exp sym_tab e =
  match e with
  | ConstBool b -> ([], Bool)
  | ConstInt i -> ([], Int)
  | Var vname ->
    (try (match SymbolMap.find vname sym_tab with
      | VarType ctyp -> ([], ctyp_to_typ ctyp)
      | FuncType (_, _) -> ([UsingFunctionAsVar vname], Unknown))
    with Not_found -> ([UndefinedName vname], Unknown))
  | Add (e1, e2) | Sub (e1, e2) | Mul (e1, e2) | Div (e1, e2) ->
    let (errors1, typ1) = check_exp sym_tab e1 in
    let (errors2, typ2) = check_exp sym_tab e2 in
    if typ1 = Int && typ2 = Int then
      (errors1 @ errors2, Int)
    else
      (errors1 @ errors2 @ [OperandMismatch], Unknown)
  | Neg e ->
    let (errors, typ) = check_exp sym_tab e in
    if typ = Int then
      (errors, Int)
    else
      (errors @ [OperandMismatch], Unknown)
  | Equal (e1, e2) | NotEq (e1, e2) ->
    let (errors1, typ1) = check_exp sym_tab e1 in
    let (errors2, typ2) = check_exp sym_tab e2 in
    if (typ1 = Int && typ2 = Int) || (typ1 = Bool && typ2 = Bool) then
      (errors1 @ errors2, Bool)
    else
      (errors1 @ errors2 @ [OperandMismatch], Unknown)
  | LessEq (e1, e2) | LessThan (e1, e2) | GreaterEq (e1, e2) | GreaterThan (e1, e2) ->
    let (errors1, typ1) = check_exp sym_tab e1 in
    let (errors2, typ2) = check_exp sym_tab e2 in
    if typ1 = Int && typ2 = Int then
      (errors1 @ errors2, Bool)
    else
      (errors1 @ errors2 @ [OperandMismatch], Unknown)
  | And (e1, e2) | Or (e1, e2) ->
    let (errors1, typ1) = check_exp sym_tab e1 in
    let (errors2, typ2) = check_exp sym_tab e2 in
    if typ1 = Bool && typ2 = Bool then
      (errors1 @ errors2, Bool)
    else
      (errors1 @ errors2 @ [OperandMismatch], Unknown)
  | Not e ->
    let (errors, typ) = check_exp sym_tab e in
    if typ = Bool then (errors, Bool)
    else (errors @ [OperandMismatch], Unknown)
  | CallExp (fname, args) ->
    let (args_errors, args_types) = List.fold_left
      (fun (acc_errors, acc_types) expr ->
        let (errs, typ) = check_exp sym_tab expr in
        (acc_errors @ errs, acc_types @ [typ]))
      ([], []) args in
    (try (match SymbolMap.find fname sym_tab with
      | FuncType (return_typ, decl_args_types) ->
        if List.length args != List.length decl_args_types then
          (args_errors @ [ArgNumMismatch], Unknown)
        else
          List.fold_left2
            (fun (acc_errors, expected_ret_typ) decl_typ arg_typ ->
              if arg_typ = Unknown then
                (acc_errors, Unknown)
              else
                let arg_ctyp = typ_to_ctyp arg_typ in
                if decl_typ != arg_ctyp then
                  (acc_errors @ [ArgTypeMismatch (decl_typ, arg_ctyp)], Unknown)
                else
                  (acc_errors, expected_ret_typ))
            (args_errors, ctyp_to_typ return_typ) decl_args_types args_types
      | VarType _ -> (args_errors @ [CallingVariable fname], Unknown))
      with Not_found -> (args_errors @ [UndefinedName fname], Unknown))
    

let rec check_stmt sym_tab stmt =
  match stmt with
  | LocalDecl (ctype, vname) ->
    if SymbolMap.mem vname sym_tab then
      (* local scope CAN and SHOULD mask the global symbol appropriately *)
      let sym_tab' = SymbolMap.remove vname sym_tab in
      ([], SymbolMap.add vname (VarType ctype) sym_tab')
    else
      let sym_tab' = SymbolMap.add vname (VarType ctype) sym_tab in
      ([], sym_tab')
  | Assign (vname, e) ->
    let (errors, etype) = check_exp sym_tab e in
    (try (match SymbolMap.find vname sym_tab with
    | VarType vtype ->
        if etype = Unknown then
          (errors, sym_tab)
        else
          let etype_c = typ_to_ctyp etype in
          if vtype = etype_c then
            (errors, sym_tab)
          else
            (errors @ [AssignMismatch (vtype, etype_c)], sym_tab)
    | FuncType (_, _) ->
      (errors @ [UsingFunctionAsVar vname], sym_tab))
    with Not_found -> (errors @ [UndefinedName vname], sym_tab))
  | Call (fname, args) ->
    let (errors, _) = check_exp sym_tab (CallExp (fname, args)) in
    (errors, sym_tab)
  | Return ->
    (try (match SymbolMap.find "return" sym_tab with
    | FuncType (ret_typ, _) ->
      if ret_typ != CVoid then
        ([ReturnMismatch (ret_typ, CVoid)], sym_tab)
      else
        ([], sym_tab)
    | _ -> failwith "Return statement outside a function")
      with Not_found -> failwith "Return statement outside a function")
  | ReturnValue e ->
    (try (match SymbolMap.find "return" sym_tab with
    | FuncType (ret_typ, _) ->
      let (errors, etype) = check_exp sym_tab e in
      if etype = Unknown then
        (errors, sym_tab)
      else
        let etype_c = typ_to_ctyp etype in
        if ret_typ = etype_c then
          (errors, sym_tab)
        else
          (errors @ [ReturnMismatch (ret_typ, etype_c)], sym_tab)
    | _ -> failwith "Return statement outside a function")
        with Not_found -> failwith "Return statement outside a function")
  | If (cond, s1, s2) ->
    let (errors, cond_type) = check_exp sym_tab cond in
    let errors = if cond_type != Bool then errors @ [OperandMismatch] else errors in
    (* symbols declared inside the if statement don't propagate to outside *)
    let (errors_s1, _) = check_stmts sym_tab s1 in
    let (errors_s2, _) = check_stmts sym_tab s2 in
    (errors @ errors_s1 @ errors_s2, sym_tab)
  | While (cond, s) ->
    let (errors, cond_type) = check_exp sym_tab cond in
    let errors = if cond_type != Bool then errors @ [OperandMismatch] else errors in
    let (errors_s, _) = check_stmts sym_tab s in
    (errors @ errors_s, sym_tab)

and check_stmts sym_tab stmts =
  List.fold_left
    (fun (e, sym_tab_acc) s ->
      let (errors, new_sym_tab) = check_stmt sym_tab_acc s in
      (e @ errors, new_sym_tab))
    ([], sym_tab) stmts

let check_func sym_tab (fname, ret_typ, args, stmts) =
  let sym_tab' = collect_vars args sym_tab in
  let arg_types = List.map (fun (t, _) -> t) args in
  let sym_tab'' = SymbolMap.add "return" (FuncType (ret_typ, arg_types)) sym_tab' in
  (* returning errors are handled within check_stmts *)
  let (errors_stmts, _) = check_stmts sym_tab'' stmts in
  (errors_stmts, SymbolMap.add fname (FuncType (ret_typ, arg_types)) sym_tab)

(*
 * more functions between here *
 *)

(* checking functions and return detected semantic errors *)
let rec check_functions sym_tab funcs =
  let (errors, _) = List.fold_left (fun (err_acc, sym_tab_acc) func ->
    let (err_func, sym_tab_new) = check_func sym_tab_acc func in
    (err_acc @ err_func, sym_tab_new))
    ([], sym_tab) funcs in
  errors

(* checking a program and return detected semantic errors *)
let run (p: program) : error list =
  let (gdecls, funcs) = p in
  let sym_tab = collect_vars gdecls SymbolMap.empty in
  let sym_tab = collect_functions funcs sym_tab in
  (* 'sym_tab' must contain global variables n functions *)
  check_functions sym_tab funcs

