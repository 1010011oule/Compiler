open Program
open Ir
open Helper

(* the module for symbol table, should carefully think about what should be stored in
 * the symbol table for this IR translation phase *)
module SymbolMap = Map.Make(String)

(* thinking that boolean is 1-byte and integer is 4-byte *)
let sizeof ctyp =
  match ctyp with
  | CInt -> 4
  | CBool -> 1
  | CIntArr n -> 4 * n
  | CBoolArr n -> n

let rec extract_names args =
  match args with
  | [] -> []
  | (arg_typ, arg_name) :: tail_args -> arg_name :: extract_names tail_args

(* adding codes for processing *)
let allocate_scratch scratch_regs =
  match SymbolMap.choose scratch_regs with
  | (reg_nam, _) -> (reg_nam, SymbolMap.remove reg_nam scratch_regs)
  | exception Not_found ->
    let xreg = create_register_name () in
    (xreg, scratch_regs)

let rec set_imm_expr reg_tab arr_tab scratch_regs dest_reg expr =
  match expr with
  | ConstBool imm -> ([Set (dest_reg, ImmBool imm)], scratch_regs)
  | ConstInt imm -> ([Set (dest_reg, ImmInt imm)], scratch_regs)
  | Var vname ->
    let rvname = SymbolMap.find vname reg_tab in
    ([Copy (rvname, dest_reg)], scratch_regs)
  | Arr (aname, index_expr) ->
    let (tmp_reg, scratch_regs') = allocate_scratch scratch_regs in
    let scratch_regs_remaining = SymbolMap.remove tmp_reg scratch_regs' in
    let (preceding_irs, added_scratch_regs) = set_imm_expr reg_tab arr_tab scratch_regs_remaining tmp_reg index_expr in
    let scratch_regs' = SymbolMap.add tmp_reg tmp_reg added_scratch_regs in
    let areg = SymbolMap.find aname reg_tab in
    (match SymbolMap.find areg arr_tab with
    | CIntArr _ ->
      (preceding_irs @ [BinOp (tmp_reg, MulOp, Reg tmp_reg, Imm (ImmInt 4));
        BinOp (tmp_reg, AddOp, Reg tmp_reg, Reg areg);
        Load (dest_reg, tmp_reg)], scratch_regs')
    | CBoolArr _ ->
      (preceding_irs @ [BinOp (tmp_reg, AddOp, Reg tmp_reg, Reg areg);
        Load (dest_reg, tmp_reg)], scratch_regs')
    | _ -> failwith "Logical bug; arr_tab must not have CInt or CBool!")
  | Add (lhs_expr, rhs_expr) | Sub (lhs_expr, rhs_expr)
  | Mul (lhs_expr, rhs_expr) | Div (lhs_expr, rhs_expr)
  | Equal (lhs_expr, rhs_expr) | NotEq (lhs_expr, rhs_expr)
  | LessEq (lhs_expr, rhs_expr) | LessThan (lhs_expr, rhs_expr)
  | GreaterEq (lhs_expr, rhs_expr) | GreaterThan (lhs_expr, rhs_expr) ->
    (* here is the evaluating lhs to the destination register. *)
    let (lhs_irs, scratch_regs) = set_imm_expr reg_tab arr_tab scratch_regs dest_reg lhs_expr in
    (* then we are evaluatiing rhs to a scratch register. *)
    let (tmp_reg, scratch_regs') =
      (match SymbolMap.choose scratch_regs with
      | (tmp_reg, _) -> (tmp_reg, scratch_regs)
      | exception Not_found ->
        let tmp_reg = create_register_name () in
        let new_scratch_regs = SymbolMap.add tmp_reg tmp_reg scratch_regs in
        (tmp_reg, new_scratch_regs)) in
    let scratch_regs_remaining = SymbolMap.remove tmp_reg scratch_regs' in
    let (rhs_irs, added_scratch_regs) = set_imm_expr reg_tab arr_tab scratch_regs_remaining tmp_reg rhs_expr in
    let scratch_regs = SymbolMap.add tmp_reg tmp_reg added_scratch_regs in
    (lhs_irs @ rhs_irs @ [BinOp (dest_reg,
      (match expr with
      | Add (_, _) -> AddOp
      | Sub (_, _) -> SubOp
      | Mul (_, _) -> MulOp
      | Div (_, _) -> DivOp
      | Equal (_, _) -> EqOp
      | NotEq (_, _) -> NeqOp
      | LessEq (_, _) -> LeqOp
      | LessThan (_, _) -> LtOp
      | GreaterEq (_, _) -> GeqOp
      | GreaterThan (_, _) -> GtOp
      | _ -> failwith "Logical bug; other operations are not supposed to be here!"),
      Reg dest_reg,
      Reg tmp_reg)], scratch_regs)
  | Neg operand_expr | Not operand_expr ->
    let (operand_irs, scratch_regs) = set_imm_expr reg_tab arr_tab scratch_regs dest_reg operand_expr in
    (operand_irs @ [UnOp (dest_reg,
      (match expr with
      | Neg _ -> NegOp
      | Not _ -> NotOp
      | _ -> failwith "Logical bug; other operations are not supposed to be here!"),
      Reg dest_reg)], scratch_regs)
  | And (lhs_expr, rhs_expr) ->
    let (lhs_irs, scratch_regs) = set_imm_expr reg_tab arr_tab scratch_regs dest_reg lhs_expr in
    let false_jump_label = create_label () in
    let (rhs_irs, scratch_regs) = set_imm_expr reg_tab arr_tab scratch_regs dest_reg rhs_expr in
    (lhs_irs @ [GotoIfNot (dest_reg, false_jump_label)] @ rhs_irs @ [Label false_jump_label], scratch_regs)
  | Or (lhs_expr, rhs_expr) ->
    let (lhs_irs, scratch_regs) = set_imm_expr reg_tab arr_tab scratch_regs dest_reg lhs_expr in
    let true_jump_label = create_label () in
    let (rhs_irs, scratch_regs) = set_imm_expr reg_tab arr_tab scratch_regs dest_reg rhs_expr in
    (lhs_irs @ [GotoIf (dest_reg, true_jump_label)] @ rhs_irs @ [Label true_jump_label], scratch_regs)

let rec transpile_stmt reg_tab arr_tab scratch_regs stmt =
  match stmt with
  | LocalDecl (ctyp, var_nam) ->
    let reg_nam = create_register_name () in
    let reg_tab = SymbolMap.add var_nam reg_nam reg_tab in
    (match ctyp with
    | CInt | CBool -> ([], reg_tab, arr_tab, scratch_regs) (* declaring register by assigning an arbitrary value *)
    | CIntArr capacity ->
      let arr_tab = SymbolMap.add reg_nam (CIntArr capacity) arr_tab in
      ([LocalAlloc (reg_nam, capacity * 4)], reg_tab, arr_tab, scratch_regs)
    | CBoolArr capacity ->
      let arr_tab = SymbolMap.add reg_nam (CBoolArr capacity) arr_tab in
      ([LocalAlloc (reg_nam, capacity)], reg_tab, arr_tab, scratch_regs))
  | Assign (lval, exp) ->
    (match lval with
    | LVar var_nam ->
      let lreg_nam = SymbolMap.find var_nam reg_tab in
      let (set_irs, scratch_regs) = set_imm_expr reg_tab arr_tab scratch_regs lreg_nam exp in
      (set_irs, reg_tab, arr_tab, scratch_regs)
    | LArr (arr_nam, index_expr) ->
      let (tmp_reg, scratch_regs) =
      (match SymbolMap.choose scratch_regs with
      | (xreg, _) -> (xreg, scratch_regs)
      | exception Not_found ->
        let xreg = create_register_name () in
        let scratch_regs' = SymbolMap.add xreg xreg scratch_regs in
        (xreg, scratch_regs')) in
      let scratch_regs_remainder = SymbolMap.remove tmp_reg scratch_regs in
      let (set_irs, added_scratch_regs) = set_imm_expr reg_tab arr_tab scratch_regs_remainder tmp_reg index_expr in
      let scratch_regs = SymbolMap.add tmp_reg tmp_reg added_scratch_regs in
      let arr_reg = SymbolMap.find arr_nam reg_tab in
      let compensate =
        (match SymbolMap.find arr_reg arr_tab with
        | CIntArr _ -> [BinOp (tmp_reg, MulOp, Reg tmp_reg, Imm (ImmInt 4))]
        | CBoolArr _ -> []
        | _ -> failwith "Logical bug; non-array stored as array!") in
      let set_irs = set_irs @ compensate @ [BinOp (tmp_reg, AddOp, Reg tmp_reg, Reg arr_reg)] in
      let (tmp_rhs_reg, added_scratch_regs) =
      (match SymbolMap.choose added_scratch_regs with
      | (xreg, _) -> (xreg, added_scratch_regs)
      | exception Not_found ->
        let xreg = create_register_name () in
        let scratch_regs' = SymbolMap.add xreg xreg scratch_regs in
        (xreg, scratch_regs')) in
      let scratch_regs_remainder = SymbolMap.remove tmp_rhs_reg added_scratch_regs in
      let (set_rhs_irs, added_scratch_regs) = set_imm_expr reg_tab arr_tab scratch_regs_remainder tmp_rhs_reg exp in
      let scratch_regs = SymbolMap.add tmp_rhs_reg tmp_rhs_reg (SymbolMap.add tmp_reg tmp_reg added_scratch_regs) in
      let set_irs = set_irs @ set_rhs_irs @ [Store (Reg tmp_rhs_reg, tmp_reg)] in
      (set_irs, reg_tab, arr_tab, scratch_regs))
  | ReturnValue expr ->
    let (tmp_reg, scratch_regs) = allocate_scratch scratch_regs in
    let (set_irs, scratch_regs) = set_imm_expr reg_tab arr_tab scratch_regs tmp_reg expr in
    let scratch_regs = SymbolMap.add tmp_reg tmp_reg scratch_regs in
    (set_irs @ [Ret (Reg tmp_reg)], reg_tab, arr_tab, scratch_regs)
  | If (cond_expr, true_stmts, false_stmts) ->
    let (cond_reg, scratch_regs) = allocate_scratch scratch_regs in
    let (cond_irs, scratch_regs) = set_imm_expr reg_tab arr_tab scratch_regs cond_reg cond_expr in
    let scratch_regs = SymbolMap.add cond_reg cond_reg scratch_regs in
    let false_label = create_label () in
    let (true_irs, _, _, scratch_regs) = transpile_stmts reg_tab arr_tab scratch_regs true_stmts in
    let end_label = create_label() in
    let (false_irs, _, _, scratch_regs) = transpile_stmts reg_tab arr_tab scratch_regs false_stmts in
    (cond_irs @ [GotoIfNot (cond_reg, false_label)] @ true_irs @ [Goto end_label] @ [Label false_label] @ false_irs @ [Label end_label],
     reg_tab, arr_tab, scratch_regs)
  | While (cond_expr, loop_stmts) ->
    let (cond_reg, scratch_regs) = allocate_scratch scratch_regs in
    let (cond_irs, scratch_regs) = set_imm_expr reg_tab arr_tab scratch_regs cond_reg cond_expr in
    let scratch_regs = SymbolMap.add cond_reg cond_reg scratch_regs in
    let false_label = create_label() in
    let cond_label = create_label () in
    let (loop_irs, _, _, scratch_regs) = transpile_stmts reg_tab arr_tab scratch_regs loop_stmts in
    ([Label cond_label] @ cond_irs @ [GotoIfNot (cond_reg, false_label)] @ loop_irs @ [Goto cond_label; Label false_label],
     reg_tab, arr_tab, scratch_regs)
  

and transpile_stmts reg_tab arr_tab scratch_regs stmts =
  List.fold_left
    (fun (irs_acc, reg_tab_acc, arr_tab_acc, scratch_regs_acc) s ->
      let (irs, reg_tab', arr_tab', scratch_regs') = transpile_stmt reg_tab_acc arr_tab_acc scratch_regs_acc s in
      (irs_acc @ irs, reg_tab', arr_tab', scratch_regs'))
    ([], reg_tab, arr_tab, scratch_regs) stmts

let rec collect_arg_regs reg_tab arg_regs =
  match arg_regs with
  | [] -> reg_tab
  | next_var :: remaining_vars ->
    let reg_tab = SymbolMap.add next_var next_var reg_tab in
    collect_arg_regs reg_tab remaining_vars

let run (p: program): ir_code =
  let (fname, ret_type, args, stmts) = p in
  let arg_regs = extract_names args in
  let reg_tab_initial = collect_arg_regs SymbolMap.empty arg_regs in
  let (irs, _, _, _) = transpile_stmts reg_tab_initial SymbolMap.empty SymbolMap.empty stmts in
  (fname, arg_regs, irs)
  (* example code for generating IR instructions:
  let r = create_register_name () in
  let set_instr = Set (r, ImmInt 0) in
  let ret_instr = Ret (Reg r) in
  let instrs = [set_instr; ret_instr] in
  (fname, arg_regs, instrs)
  *)

