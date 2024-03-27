#include <stdio.h>
#include <stdlib.h>
#include "varlist.h"
#include "ast.h"

AST* make_num_ast(int n) {
    AST* ast = (AST*)malloc(sizeof(AST));
    ast->kind = Number;
    ast->num = n;
    ast->id = NULL;
    ast->left = NULL;
    ast->right = NULL;
    return ast;
}

AST* make_id_ast(char *s) {
    AST* ast = (AST*)malloc(sizeof(AST));
    ast->kind = Identifier;
    ast->num = 0;
    ast->id = s;
    ast->left = NULL;
    ast->right = NULL;
    return ast;
}

AST* make_binop_ast(NODE_KIND kind, AST *oprnd_1, AST *oprnd_2) {
    AST* ast = (AST*)malloc(sizeof(AST));
    ast->kind = kind;
    ast->num = 0;
    ast->id = NULL;
    ast->left = oprnd_1;
    ast->right = oprnd_2;
    return ast;
}

// TODO: Fill in(filled)
AST* make_neg_ast(AST *oprnd) {
    AST* ast = (AST*)malloc(sizeof(AST));
    ast->kind= Neg;
    ast->num=0;
    ast->id=NULL;
    ast->left=oprnd;
    ast->right=NULL;  
    return ast;
}

// TODO: Fill in(filled)
int eval_ast(VarNode *vars, AST* ast) {

     if (ast == NULL) {
        return 0;
    }

    switch (ast->kind) {
        case Number:
            return ast->num;
        case Identifier:
            return lookup_var(vars, ast->id);
        case Add:
            return eval_ast(vars, ast->left) + eval_ast(vars, ast->right);
        case Sub:
            return eval_ast(vars, ast->left) - eval_ast(vars, ast->right);
        case Mul:
            return eval_ast(vars, ast->left) * eval_ast(vars, ast->right);
        case Div:
            return eval_ast(vars, ast->left) / eval_ast(vars, ast->right);
        case Neg:
            return -eval_ast(vars, ast->left);
        default:
            return 0;
    }
}


void free_ast(AST* ast) {
    switch (ast->kind) {
        case Number:
            break;
        case Identifier:
            free(ast->id);
            break;
        case Add:
        case Sub:
        case Mul:
        case Div:
            free_ast(ast->left);
            free_ast(ast->right);
            break;
        case Neg:
            free_ast(ast->left);
            break;
    }
    free(ast);
}
