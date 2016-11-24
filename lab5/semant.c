#include <stdio.h>
#include "util.h"
#include "errormsg.h"
#include "symbol.h"
#include "absyn.h"
#include "types.h"
#include "env.h"
#include "semant.h"
#include "translate.h"

struct expty {Tr_exp exp; Ty_ty ty;};

struct expty expTy(Tr_exp exp, Ty_ty ty) {
    struct expty e;
    e.exp = exp;
    e.ty = ty;
    return e;
}

struct expty transExp(S_table venv, S_table tenv, Tr_level level, Temp_label loop, A_exp a);
struct expty transVar(S_table venv, S_table tenv, Tr_level level, Temp_label loop, A_var v);
Tr_exp transDec(S_table venv, S_table tenv, Tr_level level, Temp_label loop, A_dec d);

F_fragList SEM_transProg(A_exp exp){
    Tr_level main = Tr_outermost();
    struct expty e = transExp(E_base_venv(), E_base_tenv(), main, NULL, exp);
    Tr_Func(e.exp, main);
    return Tr_getResult();
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

struct expty transExp(S_table venv, S_table tenv, Tr_level level, Temp_label loop, A_exp a) {
    switch(a->kind) {
        case A_varExp:
            return transVar(venv, tenv, level, loop, a->u.var);
        case A_nilExp:
            return expTy(Tr_Nil(), Ty_Nil());
        case A_intExp:
            return expTy(Tr_Int(a->u.intt), Ty_Int(0));
        case A_stringExp:
            return expTy(Tr_String(a->u.stringg), Ty_String());
        case A_callExp:
            {
                A_expList arg;
                Ty_tyList formal;
                struct expty exp;
                E_enventry x = S_look(venv, a->u.call.func);
                Tr_expList params = NULL;
                if (x && x->kind == E_funEntry) {
                    for (arg = a->u.call.args, formal = x->u.fun.formals; arg && formal; arg = arg->tail, formal = formal->tail) {
                        exp = transExp(venv, tenv, level, NULL, arg->head);
                        if (!compatible(formal->head, exp.ty)) {
                            EM_error(arg->head->pos, "para type mismatch");
                        }
                        params = Tr_ExpList(exp.exp, params);
                    }
                    if (arg) {
                        EM_error(a->pos, "too many params in function %s", S_name(a->u.call.func));
                    }
                    if (formal) {
                        EM_error(a->pos, "too less params in function %s", S_name(a->u.call.func));
                    }
                    return expTy(Tr_Call(x->u.fun.level, x->u.fun.label, params, level), x->u.fun.result);
                } else {
                    EM_error(a->pos, "undefined function %s", S_name(a->u.call.func));
                    return expTy(Tr_Nop(), Ty_Int(0));
                }
            }
        case A_opExp:
            {
                A_oper oper = a->u.op.oper;
                struct expty left = transExp(venv, tenv, level, loop, a->u.op.left);
                struct expty right = transExp(venv, tenv, level, loop, a->u.op.right);
                if (oper == A_plusOp || oper == A_minusOp || oper == A_timesOp || oper == A_divideOp) {
                    if (left.ty->kind != Ty_int) {
                        EM_error(a->u.op.left->pos, "integer required");
                    }
                    if (right.ty->kind != Ty_int) {
                        EM_error(a->u.op.right->pos, "integer required");
                    }
                    return expTy(Tr_OpArithm(oper, left.exp, right.exp), Ty_Int(0));
                } else if (oper == A_eqOp || oper == A_neqOp) {
                    if (!compatible(left.ty, right.ty) || left.ty->kind == Ty_void) {
                        EM_error(a->pos, "same type required");
                    }
                    return expTy(Tr_OpCmp(oper, left.exp, right.exp, left.ty->kind == Ty_string), Ty_Int(0));
                } else {
                    if (!((left.ty->kind == Ty_int && right.ty->kind == Ty_int) ||
                          (left.ty->kind == Ty_string && right.ty->kind == Ty_string))) {
                        EM_error(a->pos, "same type required");
                    }
                    return expTy(Tr_OpCmp(oper, left.exp, right.exp, left.ty->kind == Ty_string), Ty_Int(0));
                }
            }
        case A_recordExp:
            {
                Ty_ty ty = actual_ty(S_lookType(a->pos, tenv, a->u.record.typ));
                A_efieldList ef;
                Ty_fieldList f;
                Tr_expList fields = NULL;
                struct expty exp;
                int num = 0;
                if (ty->kind != Ty_record) {
                    EM_error(a->pos, "record type required");
                    return expTy(Tr_Nop(), Ty_Int(0));
                }
                for (ef = a->u.record.fields, f = ty->u.record; ef && f; ef = ef->tail, f = f->tail) {
                    exp = transExp(venv, tenv, level, loop, ef->head->exp);
                    if (!(ef->head->name == f->head->name && compatible(f->head->ty, exp.ty))) {
                        EM_error(ef->head->exp->pos, "type mismatch");
                    }
                    ++num;
                    fields = Tr_ExpList(exp.exp, fields);
                }
                if (f || ef) {
                    EM_error(a->pos, "type mismatch");
                }
                return expTy(Tr_Record(num, fields), ty);
            }
        case A_seqExp:
            {
                A_expList cur;
                Ty_ty ty = Ty_Void();
                Tr_exp exp = Tr_Nop();
                struct expty res;
                for (cur = a->u.seq; cur; cur = cur->tail) {
                    res = transExp(venv, tenv, level, loop, cur->head);
                    ty = res.ty;
                    exp = Tr_Seq(exp, res.exp);
                }
                res = expTy(exp, ty);
                return res;
            }
        case A_assignExp:
            {
                struct expty v = transVar(venv, tenv, level, loop, a->u.assign.var);
                struct expty e = transExp(venv, tenv, level, loop, a->u.assign.exp);
                if (v.ty->kind == Ty_int && v.ty->u.intt.is_loop_var) {
                    EM_error(a->pos, "loop variable can't be assigned");
                }
                if (!compatible(v.ty, e.ty)) {
                    EM_error(a->pos, "unmatched assign exp");
                }
                return expTy(Tr_Assign(v.exp, e.exp), Ty_Void());
            }
        case A_ifExp:
            {
                struct expty t = transExp(venv, tenv, level, loop, a->u.iff.test);
                if (t.ty->kind != Ty_int) {
                    EM_error(a->u.iff.test->pos, "integer required");
                }
                struct expty then = transExp(venv, tenv, level, loop, a->u.iff.then);
                if (a->u.iff.elsee) {
                    struct expty elsee = transExp(venv, tenv, level, loop, a->u.iff.elsee);
                    if (!compatible(then.ty, elsee.ty)) {
                        EM_error(a->pos, "then exp and else exp type mismatch");
                    }
                    return expTy(Tr_IfThenElse(t.exp, then.exp, elsee.exp), then.ty);
                } else {
                    if (then.ty->kind != Ty_void) {
                        EM_error(a->pos, "if-then exp's body must produce no value");
                    }
                    return expTy(Tr_IfThen(t.exp, then.exp), Ty_Void());
                }
            }
        case A_whileExp:
            {
                Temp_label done = Temp_newlabel();
                struct expty t = transExp(venv, tenv, level, loop, a->u.whilee.test);
                struct expty body = transExp(venv, tenv, level, done, a->u.whilee.body);
                if (t.ty->kind != Ty_int) {
                    EM_error(a->u.whilee.test->pos, "integer required");
                }
                if (body.ty->kind != Ty_void) {
                    EM_error(a->u.whilee.body->pos, "while body must produce no value");
                }
                return expTy(Tr_While(t.exp, body.exp, done), Ty_Void());
            }
        case A_forExp:
            {
                Temp_label done = Temp_newlabel();
                struct expty lo = transExp(venv, tenv, level, loop, a->u.forr.lo);
                struct expty hi = transExp(venv, tenv, level, loop, a->u.forr.hi);
                struct expty body;
                if (lo.ty->kind != Ty_int) {
                    EM_error(a->u.forr.lo->pos, "for exp's range type is not integer");
                }
                if (hi.ty->kind != Ty_int) {
                    EM_error(a->u.forr.hi->pos, "for exp's range type is not integer");
                }
                S_beginScope(venv);
                Tr_access access = Tr_allocLocal(level, a->u.forr.escape);
                S_enter(venv, a->u.forr.var, E_VarEntry(access, Ty_Int(1)));
                body = transExp(venv, tenv, level, done, a->u.forr.body);
                if (body.ty->kind != Ty_void) {
                    EM_error(a->u.forr.body->pos, "while body must produce no value");
                }
                S_endScope(venv);
                return expTy(Tr_For(access, level, lo.exp, hi.exp, body.exp, done), Ty_Void());
            }
        case A_breakExp:
            {
                if (loop == NULL) {
                    EM_error(a->pos, "break is not inside a loop");
                    return expTy(Tr_Nop(), Ty_Void());
                } else {
                    return expTy(Tr_Jump(loop), Ty_Void());
                }
            }
        case A_letExp:
            {
                struct expty exp;
                Tr_exp e = Tr_Nop();
                A_decList d;
                S_beginScope(venv);
                S_beginScope(tenv);
                for (d = a->u.let.decs; d; d = d->tail) {
                    e = Tr_Seq(e, transDec(venv, tenv, level, loop, d->head));
                }
                exp = transExp(venv, tenv, level, loop, a->u.let.body);
                exp.exp = Tr_Seq(e, exp.exp);
                S_endScope(tenv);
                S_endScope(venv);
                return exp;
            }
        case A_arrayExp:
            {
                Ty_ty ty = actual_ty(S_lookType(a->pos, tenv, a->u.array.typ));
                struct expty size = transExp(venv, tenv, level, loop, a->u.array.size);
                struct expty init = transExp(venv, tenv, level, loop, a->u.array.init);
                if (ty->kind != Ty_array) {
                    EM_error(a->pos, "array type required");
                    return expTy(Tr_Nop(), Ty_Int(0));
                }
                if (size.ty->kind != Ty_int) {
                    EM_error(a->u.array.size->pos, "integer required");
                }
                if (!compatible(ty->u.array, init.ty)) {
                    EM_error(a->u.array.init->pos, "type mismatch");
                }
                return expTy(Tr_Array(size.exp, init.exp), ty);
            }
    }
}

struct expty transVar(S_table venv, S_table tenv, Tr_level level, Temp_label loop, A_var v)
{
    switch(v->kind) {
        case A_simpleVar:
            {
                E_enventry x = S_look(venv, v->u.simple);
                if (x && x->kind == E_varEntry) {
                    return expTy(Tr_simpleVar(x->u.var.access, level), x->u.var.ty);
                } else {
                    EM_error(v->pos, "undefined variable %s", S_name(v->u.simple));
                    return expTy(Tr_Nop(), Ty_Int(0));
                }
            }
        case A_fieldVar:
            {
                struct expty var = transVar(venv, tenv, level, loop, v->u.field.var);
                if (!(var.ty->kind == Ty_record)) {
                    EM_error(v->u.field.var->pos, "not a record type");
                    return expTy(Tr_Nop(), Ty_Int(0));
                } else {
                    int ix = 0;
                    for (Ty_fieldList field = var.ty->u.record; field; field = field->tail) {
                        if (field->head->name == v->u.field.sym) {
                            return expTy(Tr_fieldVar(var.exp, ix), field->head->ty);
                        }
                        ++ix;
                    }
                    EM_error(v->u.field.var->pos, "field %s doesn't exist", S_name(v->u.field.sym));
                    return expTy(Tr_Nop(), Ty_Int(0));
                }
            }
        case A_subscriptVar:
            {
                struct expty var = transVar(venv, tenv, level, loop, v->u.subscript.var);
                if (!(var.ty->kind == Ty_array)) {
                    EM_error(v->u.subscript.var->pos, "array type required");
                    return expTy(Tr_Nop(), Ty_Int(0));
                } else {
                    struct expty exp = transExp(venv, tenv, level, loop, v->u.subscript.exp);
                    if (exp.ty->kind != Ty_int) {
                        EM_error(v->u.subscript.exp->pos, "integer required");
                    }
                    return expTy(Tr_subscriptVar(var.exp, exp.exp), var.ty->u.array);
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

U_boolList makeFormalBoolList(A_fieldList l)
{
    if (l) {
        return U_BoolList(l->head->escape, makeFormalBoolList(l->tail));
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

Tr_exp transDec(S_table venv, S_table tenv, Tr_level level, Temp_label loop, A_dec d)
{
    switch (d->kind) {
        case A_varDec:
            {
                struct expty e = transExp(venv, tenv, level, loop, d->u.var.init);
                Tr_access access = Tr_allocLocal(level, d->u.var.escape);
                if (d->u.var.typ) {
                    Ty_ty spec = actual_ty(S_lookType(d->pos, tenv, d->u.var.typ));
                    if (!compatible(spec, e.ty)) {
                        EM_error(d->pos, "type mismatch");
                    }
                    S_enter(venv, d->u.var.var, E_VarEntry(access, spec));
                } else {
                    if (e.ty->kind == Ty_nil) {
                        EM_error(d->pos, "init should not be nil without type specified");
                    }
                    S_enter(venv, d->u.var.var, E_VarEntry(access, e.ty));
                }
                return Tr_Assign(Tr_simpleVar(access, level), e.exp);
                break;
            }
        case A_functionDec:
            {
                A_fundecList fun;
                A_fieldList l;
                Ty_ty resultTy;
                Ty_tyList formalTys, t;
                U_boolList formalBools;
                E_enventry f;
                struct expty exp;
                Tr_accessList params;
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
                    formalBools = makeFormalBoolList(fun->head->params);
                    S_enter(venv, fun->head->name, E_FunEntry(Tr_newLevel(level, Temp_newlabel(), formalBools), Temp_newlabel(), formalTys, resultTy));
                }
                for (fun = d->u.function; fun; fun = fun->tail) {
                    S_beginScope(venv);
                    f = S_look(venv, fun->head->name);
                    t = f->u.fun.formals;
                    params = Tr_formals(f->u.fun.level);
                    for (l = fun->head->params; l; l = l->tail, t = t->tail, params = params->tail) {
                        S_enter(venv, l->head->name, E_VarEntry(params->head, t->head));
                    }
                    resultTy = f->u.fun.result;
                    exp = transExp(venv, tenv, f->u.fun.level, NULL, fun->head->body);
                    if (!compatible(exp.ty, resultTy)) {
                        if (resultTy->kind == Ty_void) {
                            EM_error(fun->head->body->pos, "procedure returns value");
                        } else {
                            EM_error(fun->head->body->pos, "type mismatch");
                        }
                    }
                    S_endScope(venv);
                    Tr_Func(exp.exp, f->u.fun.level);
                }
                return Tr_Nop();
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
                return Tr_Nop();
                break;
            }
    }
}
