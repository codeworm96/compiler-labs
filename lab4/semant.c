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

void SEM_transProg(A_exp exp){
    transExp(E_base_venv(), E_base_tenv(), exp);
}

struct expty transExp(S_table venv, S_table tenv, A_exp a) {
    switch(a->kind) {
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
