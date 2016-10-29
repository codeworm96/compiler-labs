#include <stdio.h>
#include "util.h"
#include "errormsg.h"
#include "symbol.h"
#include "absyn.h"
#include "types.h"
#include "env.h"
#include "semant.h"

struct expty {Ty_ty ty;};

struct expty expTy(Ty_ty ty) {
    struct expty e;
    e.ty = ty;
    return e;
}

struct expty transExp(S_table venv, S_table tenv, A_exp a);
struct expty transVar(S_table venv, S_table tenv, A_var v);

void SEM_transProg(A_exp exp){
    transExp(E_base_venv(), E_base_tenv(), exp);
}

struct expty transExp(S_table venv, S_table tenv, A_exp a) {
    switch(a->kind) {
        case A_varExp:
            return transVar(venv, tenv, a->u.var);
        case A_nilExp:
            return expTy(Ty_Nil());
        case A_intExp:
            return expTy(Ty_Int());
        case A_stringExp:
            return expTy(Ty_String());
        case A_opExp:
            {
                A_oper oper = a->u.op.oper;
                struct expty left = transExp(venv, tenv, a->u.op.left);
                struct expty right = transExp(venv, tenv, a->u.op.right);
                if (oper == A_plusOp || oper == A_minusOp || oper == A_timesOp || oper == A_divideOp) {
                    if (left.ty->kind != Ty_int) {
                        EM_error(a->u.op.left->pos, "integer required");
                    }
                    if (right.ty->kind != Ty_int) {
                        EM_error(a->u.op.right->pos, "integer required");
                    }
                    return expTy(Ty_Int());
                } else if (oper == A_eqOp || oper == A_neqOp) {
                    if (!((left.ty->kind == Ty_int && right.ty->kind == Ty_int) ||
                          (left.ty->kind == Ty_string && right.ty->kind == Ty_string) ||
                          (left.ty->kind == Ty_record && left.ty == right.ty) ||
                          (left.ty->kind == Ty_array && left.ty == right.ty))) {
                        EM_error(a->pos, "type mismatch");
                    }
                    return expTy(Ty_Int());
                } else {
                    if (!((left.ty->kind == Ty_int && right.ty->kind == Ty_int) ||
                          (left.ty->kind == Ty_string && right.ty->kind == Ty_string))) {
                        EM_error(a->pos, "type mismatch");
                    }
                    return expTy(Ty_Int());
                }
            }
    }
}

Ty_ty actual_ty(Ty_ty ty) 
{
    if (ty->kind == Ty_name) {
        return ty->u.name.ty;
    } else {
        return ty;
    }
}

struct expty transVar(S_table venv, S_table tenv, A_var v)
{
    switch(v->kind) {
        case A_simpleVar:
            {
                E_enventry x = S_look(venv, v->u.simple);
                if (x && x->kind == E_varEntry) {
                    return expTy(actual_ty(x->u.var.ty));
                } else {
                    EM_error(v->pos, "undefined variable %s", S_name(v->u.simple));
                    return expTy(Ty_Int());
                }
            }
        case A_fieldVar:
            {
                struct expty var = transVar(venv, tenv, v->u.field.var);
                if (!(var.ty->kind == Ty_record)) {
                    EM_error(v->u.field.var->pos, "expect a record");
                    return expTy(Ty_Int());
                } else {
                    for (Ty_fieldList field = var.ty->u.record; field; field = field->tail) {
                        if (field->head->name == v->u.field.sym) {
                            return expTy(field->head->ty);
                        }
                    }
                    EM_error(v->u.field.var->pos, "field not found");
                    return expTy(Ty_Int());
                }
            }
        case A_subscriptVar:
            {
                struct expty var = transVar(venv, tenv, v->u.subscript.var);
                if (!(var.ty->kind == Ty_array)) {
                    EM_error(v->u.subscript.var->pos, "expect a array");
                    return expTy(Ty_Int());
                } else {
                    struct expty exp = transExp(venv, tenv, v->u.subscript.exp);
                    if (!(exp.ty->kind != Ty_int)) {
                        EM_error(v->u.subscript.exp->pos, "integer required");
                    }
                    return expTy(var.ty->u.array);
                }
            }
        default:
            assert(0); /* control flow should never reach here. */
    }
}
