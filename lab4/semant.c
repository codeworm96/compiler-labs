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
void transDec(S_table venv, S_table tenv, A_dec d);

void SEM_transProg(A_exp exp){
    transExp(E_base_venv(), E_base_tenv(), exp);
}

int compatible(Ty_ty a, Ty_ty b)
{
    if (a->kind == Ty_array) {
        return a == b;
    } else if (a->kind == Ty_record) {
        return a == b || b->kind == Ty_nil;
    } else if (b->kind == Ty_record) {
        return a == b || a->kind == Ty_nil;
    } else {
        return a->kind == b->kind;
    }
}

Ty_ty S_lookType(A_pos pos, S_table tenv, S_symbol name)
{
    Ty_ty res = S_look(tenv, name);
    if (!res) {
        EM_error(pos, "undefined type %s", S_name(name));
        res = Ty_Int(0);
    }
    return res;
}

Ty_ty actual_ty(Ty_ty ty) 
{
    if (ty->kind == Ty_name) {
        return ty->u.name.ty;
    } else {
        return ty;
    }
}

struct expty transExp(S_table venv, S_table tenv, A_exp a) {
    switch(a->kind) {
        case A_varExp:
            return transVar(venv, tenv, a->u.var);
        case A_nilExp:
            return expTy(Ty_Nil());
        case A_intExp:
            return expTy(Ty_Int(0));
        case A_stringExp:
            return expTy(Ty_String());
        case A_callExp:
            {
                A_expList arg;
                Ty_tyList formal;
                struct expty exp;
                E_enventry x = S_look(venv, a->u.call.func);
                if (x && x->kind == E_funEntry) {
                    for (arg = a->u.call.args, formal = x->u.fun.formals; arg && formal; arg = arg->tail, formal = formal->tail) {
                        exp = transExp(venv, tenv, arg->head);
                        if (!compatible(formal->head, exp.ty)) {
                            EM_error(arg->head->pos, "para type mismatch");
                        }
                    }
                    if (arg) {
                        EM_error(a->pos, "too many params in function %s", S_name(a->u.call.func));
                    }
                    if (formal) {
                        EM_error(a->pos, "too less params in function %s", S_name(a->u.call.func));
                    }
                    return expTy(x->u.fun.result);
                } else {
                    EM_error(a->pos, "undefined function %s", S_name(a->u.call.func));
                    return expTy(Ty_Int(0));
                }
            }
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
                    return expTy(Ty_Int(0));
                } else if (oper == A_eqOp || oper == A_neqOp) {
                    if (!compatible(left.ty, right.ty) || left.ty->kind == Ty_void) {
                        EM_error(a->pos, "same type required");
                    }
                    return expTy(Ty_Int(0));
                } else {
                    if (!((left.ty->kind == Ty_int && right.ty->kind == Ty_int) ||
                          (left.ty->kind == Ty_string && right.ty->kind == Ty_string))) {
                        EM_error(a->pos, "same type required");
                    }
                    return expTy(Ty_Int(0));
                }
            }
        case A_recordExp:
            {
                Ty_ty ty = actual_ty(S_lookType(a->pos, tenv, a->u.record.typ));
                A_efieldList ef;
                Ty_fieldList f;
                struct expty exp;
                if (ty->kind != Ty_record) {
                    EM_error(a->pos, "record type required");
                    return expTy(Ty_Int(0));
                }
                for (ef = a->u.record.fields, f = ty->u.record; ef && f; ef = ef->tail, f = f->tail) {
                    exp = transExp(venv, tenv, ef->head->exp);
                    if (!(ef->head->name == f->head->name && compatible(f->head->ty, exp.ty))) {
                        EM_error(ef->head->exp->pos, "type mismatch");
                    }
                }
                if (f || ef) {
                    EM_error(a->pos, "type mismatch");
                }
                return expTy(ty);
            }
        case A_seqExp:
            {
                A_expList cur;
                struct expty res = expTy(Ty_Void());
                for (cur = a->u.seq; cur; cur = cur->tail) {
                    res = transExp(venv, tenv, cur->head);
                }
                return res;
            }
        case A_assignExp:
            {
                struct expty v = transVar(venv, tenv, a->u.assign.var);
                struct expty e = transExp(venv, tenv, a->u.assign.exp);
                if (v.ty->kind == Ty_int && v.ty->u.intt.is_loop_var) {
                    EM_error(a->pos, "loop variable can't be assigned");
                }
                if (!compatible(v.ty, e.ty)) {
                    EM_error(a->pos, "unmatched assign exp");
                }
                return expTy(Ty_Void());
            }
        case A_ifExp:
            {
                struct expty t = transExp(venv, tenv, a->u.iff.test);
                if (t.ty->kind != Ty_int) {
                    EM_error(a->u.iff.test->pos, "integer required");
                }
                struct expty then = transExp(venv, tenv, a->u.iff.then);
                if (a->u.iff.elsee) {
                    struct expty elsee = transExp(venv, tenv, a->u.iff.elsee);
                    if (!compatible(then.ty, elsee.ty)) {
                        EM_error(a->pos, "then exp and else exp type mismatch");
                    }
                    return expTy(then.ty);
                } else {
                    if (then.ty->kind != Ty_void) {
                        EM_error(a->pos, "if-then exp's body must produce no value");
                    }
                    return expTy(Ty_Void());
                }
            }
        case A_whileExp:
            {
                struct expty t = transExp(venv, tenv, a->u.whilee.test);
                struct expty body = transExp(venv, tenv, a->u.whilee.body);
                if (t.ty->kind != Ty_int) {
                    EM_error(a->u.whilee.test->pos, "integer required");
                }
                if (body.ty->kind != Ty_void) {
                    EM_error(a->u.whilee.body->pos, "while body must produce no value");
                }
                return expTy(Ty_Void());
            }
        case A_forExp:
            {
                struct expty lo = transExp(venv, tenv, a->u.forr.lo);
                struct expty hi = transExp(venv, tenv, a->u.forr.hi);
                struct expty body;
                if (lo.ty->kind != Ty_int) {
                    EM_error(a->u.forr.lo->pos, "for exp's range type is not integer");
                }
                if (hi.ty->kind != Ty_int) {
                    EM_error(a->u.forr.hi->pos, "for exp's range type is not integer");
                }
                S_beginScope(venv);
                S_enter(venv, a->u.forr.var, E_VarEntry(Ty_Int(1)));
                body = transExp(venv, tenv, a->u.forr.body);
                if (body.ty->kind != Ty_void) {
                    EM_error(a->u.forr.body->pos, "while body must produce no value");
                }
                S_endScope(venv);
                return expTy(Ty_Void());
            }
        case A_breakExp:
            return expTy(Ty_Void()); /* TODO: break must within while / for */
        case A_letExp:
            {
                struct expty exp;
                A_decList d;
                S_beginScope(venv);
                S_beginScope(tenv);
                for (d = a->u.let.decs; d; d = d->tail) {
                    transDec(venv, tenv, d->head);
                }
                exp = transExp(venv, tenv, a->u.let.body);
                S_endScope(tenv);
                S_endScope(venv);
                return exp;
            }
        case A_arrayExp:
            {
                Ty_ty ty = actual_ty(S_lookType(a->pos, tenv, a->u.array.typ));
                struct expty size = transExp(venv, tenv, a->u.array.size);
                struct expty init = transExp(venv, tenv, a->u.array.init);
                if (ty->kind != Ty_array) {
                    EM_error(a->pos, "array type required");
                    return expTy(Ty_Int(0));
                }
                if (size.ty->kind != Ty_int) {
                    EM_error(a->u.array.size->pos, "integer required");
                }
                if (!compatible(ty->u.array, init.ty)) {
                    EM_error(a->u.array.init->pos, "type mismatch");
                }
                return expTy(ty);
            }
    }
}

struct expty transVar(S_table venv, S_table tenv, A_var v)
{
    switch(v->kind) {
        case A_simpleVar:
            {
                E_enventry x = S_look(venv, v->u.simple);
                if (x && x->kind == E_varEntry) {
                    return expTy(x->u.var.ty);
                } else {
                    EM_error(v->pos, "undefined variable %s", S_name(v->u.simple));
                    return expTy(Ty_Int(0));
                }
            }
        case A_fieldVar:
            {
                struct expty var = transVar(venv, tenv, v->u.field.var);
                if (!(var.ty->kind == Ty_record)) {
                    EM_error(v->u.field.var->pos, "not a record type");
                    return expTy(Ty_Int(0));
                } else {
                    for (Ty_fieldList field = var.ty->u.record; field; field = field->tail) {
                        if (field->head->name == v->u.field.sym) {
                            return expTy(field->head->ty);
                        }
                    }
                    EM_error(v->u.field.var->pos, "field %s doesn't exist", S_name(v->u.field.sym));
                    return expTy(Ty_Int(0));
                }
            }
        case A_subscriptVar:
            {
                struct expty var = transVar(venv, tenv, v->u.subscript.var);
                if (!(var.ty->kind == Ty_array)) {
                    EM_error(v->u.subscript.var->pos, "array type required");
                    return expTy(Ty_Int(0));
                } else {
                    struct expty exp = transExp(venv, tenv, v->u.subscript.exp);
                    if (exp.ty->kind != Ty_int) {
                        EM_error(v->u.subscript.exp->pos, "integer required");
                    }
                    return expTy(var.ty->u.array);
                }
            }
        default:
            assert(0); /* control flow should never reach here. */
    }
}

Ty_tyList makeFormalTyList(A_pos pos, S_table tenv, A_fieldList l)
{
    if (l) {
        return Ty_TyList(actual_ty(S_lookType(pos, tenv, l->head->typ)), makeFormalTyList(pos, tenv, l->tail));
    } else {
        return NULL;
    }
}

Ty_fieldList mkTyFieldList(A_pos pos, S_table tenv, A_fieldList l)
{
    if (l) {
        return Ty_FieldList(Ty_Field(l->head->name, S_lookType(pos, tenv, l->head->typ)), mkTyFieldList(pos, tenv, l->tail));
    } else {
        return NULL;
    }
}

Ty_fieldList actual_tys(Ty_fieldList l)
{
    if (l) {
        return Ty_FieldList(Ty_Field(l->head->name, actual_ty(l->head->ty)), actual_tys(l->tail));
    } else {
        return NULL;
    }
}

int findFunc(A_fundecList fun, S_symbol name)
{
    if (!fun) {
        return 0;
    } else if (fun->head->name == name) {
        return 1;
    } else {
        return findFunc(fun->tail, name);
    }
}

int findNamety(A_nametyList ty, S_symbol name)
{
    if (!ty) {
        return 0;
    } else if (ty->head->name == name) {
        return 1;
    } else {
        return findNamety(ty->tail, name);
    }
}

void transDec(S_table venv, S_table tenv, A_dec d)
{
    switch (d->kind) {
        case A_varDec:
            {
                struct expty e = transExp(venv, tenv, d->u.var.init);
                if (d->u.var.typ) {
                    Ty_ty spec = actual_ty(S_lookType(d->pos, tenv, d->u.var.typ));
                    if (!compatible(spec, e.ty)) {
                        EM_error(d->pos, "type mismatch");
                    }
                    S_enter(venv, d->u.var.var, E_VarEntry(spec));
                } else {
                    if (e.ty->kind == Ty_nil) {
                        EM_error(d->pos, "init should not be nil without type specified");
                    }
                    S_enter(venv, d->u.var.var, E_VarEntry(e.ty));
                }
                break;
            }
        case A_functionDec:
            {
                A_fundecList fun;
                A_fieldList l;
                Ty_ty resultTy;
                Ty_tyList formalTys, t;
                E_enventry f;
                struct expty exp;
                for (fun = d->u.function; fun; fun = fun->tail) {
                    if (fun->head->result) {
                        resultTy = S_lookType(d->pos, tenv, fun->head->result);
                    } else {
                        resultTy = Ty_Void();
                    }
                    formalTys = makeFormalTyList(d->pos, tenv, fun->head->params);
                    if (findFunc(fun->tail, fun->head->name)) {
                        EM_error(d->pos, "two functions have the same name");
                    }
                    S_enter(venv, fun->head->name, E_FunEntry(formalTys, resultTy));
                }
                for (fun = d->u.function; fun; fun = fun->tail) {
                    S_beginScope(venv);
                    f = S_look(venv, fun->head->name);
                    t = f->u.fun.formals;
                    resultTy = f->u.fun.result;
                    for (l = fun->head->params; l; l = l->tail, t = t->tail) {
                        S_enter(venv, l->head->name, E_VarEntry(t->head));
                    }
                    exp = transExp(venv, tenv, fun->head->body);
                    if (!compatible(exp.ty, resultTy)) {
                        if (resultTy->kind == Ty_void) {
                            EM_error(fun->head->body->pos, "procedure returns value");
                        } else {
                            EM_error(fun->head->body->pos, "type mismatch");
                        }
                    }
                    S_endScope(venv);
                }
                break;
            }
        case A_typeDec:
            {
                A_nametyList l;
                int last, cur;
                for (l = d->u.type; l; l = l->tail) {
                    if (findNamety(l->tail, l->head->name)) {
                        EM_error(d->pos, "two types have the same name");
                    }
                    S_enter(tenv, l->head->name, Ty_Name(l->head->name, NULL));
                }
                last = 0;
                for (l = d->u.type; l; l = l->tail) {
                    switch(l->head->ty->kind) {
                        case A_nameTy:
                            {
                                Ty_ty ty = S_lookType(d->pos, tenv, l->head->name);
                                ty->u.name.sym = l->head->ty->u.name;
                                ++last;
                                break;
                            }
                        case A_recordTy:
                            {
                                Ty_ty ty = S_lookType(d->pos, tenv, l->head->name);
                                ty->kind = Ty_record;
                                ty->u.record = mkTyFieldList(d->pos, tenv, l->head->ty->u.record);
                                break;
                            }
                        case A_arrayTy:
                            {
                                Ty_ty ty = S_lookType(d->pos, tenv, l->head->name);
                                ty->kind = Ty_array;
                                ty->u.array = S_lookType(d->pos, tenv, l->head->ty->u.array);
                                break;
                            }
                    }
                }
                while (last > 0) {
                    cur = 0;
                    for (l = d->u.type; l; l = l->tail) {
                        if (l->head->ty->kind == A_nameTy) {
                            Ty_ty ty = S_lookType(d->pos, tenv, l->head->name);
                            if (!ty->u.name.ty) {
                                Ty_ty ty2 = S_lookType(d->pos, tenv, ty->u.name.sym);
                                if (ty2->kind == Ty_name) {
                                    if (ty2->u.name.ty) {
                                        ty->u.name.ty = ty2->u.name.ty;
                                    } else {
                                        ++cur;
                                    }
                                } else {
                                    ty->u.name.ty = ty2;
                                }
                            }
                        }
                    }
                    if (cur == last) {
                        EM_error(d->pos, "illegal type cycle");
                        break;
                    }
                    last = cur;
                }
                for (l = d->u.type; l; l = l->tail) {
                    switch(l->head->ty->kind) {
                        case A_nameTy:
                            break;
                        case A_recordTy:
                            {
                                Ty_ty ty = S_lookType(d->pos, tenv, l->head->name);
                                ty->u.record = actual_tys(ty->u.record);
                                break;
                            }
                        case A_arrayTy:
                            {
                                Ty_ty ty = S_lookType(d->pos, tenv, l->head->name);
                                ty->u.array = actual_ty(ty->u.array);
                                break;
                            }
                    }
                }
                break;
            }

    }
}
