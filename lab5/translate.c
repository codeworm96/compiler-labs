#include <stdio.h>
#include "util.h"
#include "table.h"
#include "symbol.h"
#include "absyn.h"
#include "temp.h"
#include "tree.h"
#include "printtree.h"
#include "frame.h"
#include "translate.h"

struct Tr_expList_ {
	Tr_exp head;
	Tr_expList tail;	
};

Tr_expList Tr_ExpList(Tr_exp head, Tr_expList tail)
{
    Tr_expList res = checked_malloc(sizeof(*res));
    res->head = head;
    res->tail = tail;
    return res;
}

struct Tr_access_ {
    Tr_level level;
    F_access access;
};

Tr_access Tr_Access(Tr_level level, F_access access)
{
    Tr_access res = checked_malloc(sizeof(*res));
    res->level = level;
    res->access = access;
    return res;
}

Tr_accessList Tr_AccessList(Tr_access head, Tr_accessList tail)
{
    Tr_accessList res = checked_malloc(sizeof(*res));
    res->head = head;
    res->tail = tail;
    return res;
}

struct Tr_level_ {
    Tr_level parent;
    F_frame frame;
    Tr_accessList formals;
};

void Tr_procEntryExit(Tr_level level, Tr_exp body, Tr_accessList formals)
{
    /* TODO */
}

static Tr_level outermost = NULL;
Tr_level Tr_outermost(void)
{
    if (outermost) {
        return outermost;
    } else {
        outermost = checked_malloc(sizeof(*outermost));
        outermost->parent = NULL;
        outermost->frame = F_newFrame(Temp_newlabel(), NULL);
        outermost->formals = NULL;
        return outermost;
    }
}

Tr_accessList makeLevelFormals(Tr_level level, F_accessList l)
{
    if (l) {
        return Tr_AccessList(Tr_Access(level, l->head), makeLevelFormals(level, l->tail));
    } else {
        return NULL;
    }
}

Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals)
{
    Tr_level res = checked_malloc(sizeof(*res));
    res->parent = parent;
    res->frame = F_newFrame(name, U_BoolList(1, formals));
    res->formals = makeLevelFormals(res, F_formals(res->frame)->tail); /* discard static link */
    return res;
}

Tr_accessList Tr_formals(Tr_level level)
{
    return level->formals;
}

Tr_access Tr_allocLocal(Tr_level level, bool escape)
{
    return Tr_Access(level, F_allocLocal(level->frame, escape));
}

static F_fragList fragList;
F_fragList Tr_getResult(void) {
    return fragList;
}

typedef struct patchList_ *patchList;
struct patchList_ { Temp_label *head; patchList tail; };
static patchList PatchList(Temp_label *head, patchList tail)
{
    patchList res = checked_malloc(sizeof(*res));
    res->head = head;
    res->tail = tail;
    return res;
}

static void doPatch(patchList tList, Temp_label label)
{
    patchList t;
    for (t = tList; t; t = t->tail) {
        *(t->head) = label;
    }
}

static patchList joinPatch(patchList first, patchList second) {
    patchList t;
    if (!first) return second;
    for (t = first; t->tail; t = t->tail)
        ;
    t->tail = second;
    return first;
}

struct Cx { patchList trues; patchList falses; T_stm stm; };

struct Tr_exp_ {
    enum { Tr_ex, Tr_nx, Tr_cx } kind;
    union {
        T_exp ex;
        T_stm nx;
        struct Cx cx;
    } u;
};

static Tr_exp Tr_Ex(T_exp ex)
{
    Tr_exp res = checked_malloc(sizeof(*res));
    res->kind = Tr_ex;
    res->u.ex = ex;
    return res;
}

static Tr_exp Tr_Nx(T_stm nx)
{
    Tr_exp res = checked_malloc(sizeof(*res));
    res->kind = Tr_nx;
    res->u.nx = nx;
    return res;
}

static Tr_exp Tr_Cx(patchList trues, patchList falses, T_stm stm)
{
    Tr_exp res = checked_malloc(sizeof(*res));
    res->kind = Tr_cx;
    res->u.cx.trues = trues;
    res->u.cx.falses = falses;
    res->u.cx.stm = stm;
    return res;
}

static T_exp unEx(Tr_exp e) {
    switch(e->kind) {
        case Tr_ex:
            return e->u.ex;
        case Tr_cx:
            {
                Temp_temp r = Temp_newtemp();
                Temp_label t = Temp_newlabel();
                Temp_label f = Temp_newlabel();
                doPatch(e->u.cx.trues, t);
                doPatch(e->u.cx.falses, f);
                return T_Eseq(T_Move(T_Temp(r), T_Const(1)),
                           T_Eseq(e->u.cx.stm,
                               T_Eseq(T_Label(f),
                                   T_Eseq(T_Move(T_Temp(r), T_Const(0)),
                                       T_Eseq(T_Label(t), T_Temp(r))))));
            }
        case Tr_nx:
            return T_Eseq(e->u.nx, T_Const(0));
    }
    assert(0); /* can't get here */
}

static T_stm unNx(Tr_exp e) {
    switch(e->kind) {
        case Tr_ex:
            return T_Exp(e->u.ex);
        case Tr_cx:
            {
                Temp_label l = Temp_newlabel();
                doPatch(e->u.cx.trues, l);
                doPatch(e->u.cx.falses, l);
                return T_Seq(e->u.cx.stm, T_Label(l));
            }
        case Tr_nx:
            return e->u.nx;
    }
    assert(0); /* can't get here */
}

static struct Cx unCx(Tr_exp e) {
    switch(e->kind) {
        case Tr_ex:
            {
                struct Cx res;
                res.stm = T_Cjump(T_ne, unEx(e), T_Const(0), NULL, NULL);
                res.trues = PatchList(&(res.stm->u.CJUMP.true), NULL);
                res.falses = PatchList(&(res.stm->u.CJUMP.false), NULL);
                return res;
            }
        case Tr_cx:
            return e->u.cx;
        case Tr_nx:
            assert(0); /* can't get here */
    }
    assert(0); /* can't get here */
}

static T_exp staticLink(Tr_level now, Tr_level target)
{
    T_exp res = T_Temp(F_FP());
    Tr_level cur = now;
    while (cur && cur != target) {
        res = F_Exp(F_formals(cur->frame)->head, res);
        cur = cur->parent;
    }
    return res;
}

Tr_exp Tr_Nop()
{
    return Tr_Ex(T_Const(0));
}

Tr_exp Tr_Nil()
{
    return Tr_Ex(T_Const(0)); /* TODO */
}

Tr_exp Tr_Int(int v)
{
    return Tr_Ex(T_Const(v));
}

Tr_exp Tr_String(string s)
{
    Temp_label l = Temp_newlabel();
    F_frag frag = F_StringFrag(l, s);
    fragList = F_FragList(frag, fragList);
    return Tr_Ex(T_Name(l));
}

T_expList makeCallParams(Tr_expList params)
{
    T_expList res = NULL;
    Tr_expList cur = params;
    while (cur) {
        res = T_ExpList(unEx(cur->head), res);
        cur = cur->tail;
    }
    return res;
}

Tr_exp Tr_Call(Tr_level level, Temp_label label, Tr_expList params, Tr_level cur)
{
    return Tr_Ex(T_Call(T_Name(label), T_ExpList(staticLink(cur, level->parent), makeCallParams(params))));
}

Tr_exp Tr_OpArithm(A_oper oper, Tr_exp left, Tr_exp right)
{
    T_exp l = unEx(left);
    T_exp r = unEx(right);
    T_exp res;
    switch (oper) {
        case A_plusOp:
            res = T_Binop(T_plus, l, r);
            break;
        case A_minusOp:
            res = T_Binop(T_minus, l, r);
            break;
        case A_timesOp:
            res = T_Binop(T_mul, l, r);
            break;
        case A_divideOp:
            res = T_Binop(T_div, l, r);
            break;
    }
    return Tr_Ex(res);
}

Tr_exp Tr_OpCmp(A_oper oper, Tr_exp left, Tr_exp right, int isStr)
{
    T_exp l;
    T_exp r;
    struct Cx res;
    if (isStr) {
        l = F_externalCall("StrCmp", T_ExpList(unEx(left), T_ExpList(unEx(right), NULL)));
        r = T_Const(0);
    } else {
        l = unEx(left);
        r = unEx(right);
    }
    switch (oper) {
        case A_eqOp:
            res.stm = T_Cjump(T_eq, l, r, NULL, NULL);
            break;
        case A_neqOp:
            res.stm = T_Cjump(T_ne, l, r, NULL, NULL);
            break;
        case A_ltOp:
            res.stm = T_Cjump(T_lt, l, r, NULL, NULL);
            break;
        case A_gtOp:
            res.stm = T_Cjump(T_gt, l, r, NULL, NULL);
            break;
        case A_leOp:
            res.stm = T_Cjump(T_le, l, r, NULL, NULL);
            break;
        case A_geOp:
            res.stm = T_Cjump(T_ge, l, r, NULL, NULL);
            break;
    }
    res.trues = PatchList(&(res.stm->u.CJUMP.true), NULL);
    res.falses = PatchList(&(res.stm->u.CJUMP.false), NULL);
    return Tr_Cx(res.trues, res.falses, res.stm);
}

Tr_exp Tr_Jump(Temp_label l)
{
    return Tr_Nx(T_Jump(T_Name(l), Temp_LabelList(l, NULL)));
}

Tr_exp Tr_Assign(Tr_exp var, Tr_exp value)
{
    return Tr_Nx(T_Move(unEx(var), unEx(value)));
}

Tr_exp Tr_Seq(Tr_exp seq, Tr_exp e)
{
    return Tr_Ex(T_Eseq(unNx(seq), unEx(e)));
}

Tr_exp Tr_IfThen(Tr_exp test, Tr_exp then)
{
    Temp_label t = Temp_newlabel();
    Temp_label f = Temp_newlabel();
    struct Cx cx = unCx(test);
    doPatch(cx.trues, t);
    doPatch(cx.falses, f);
    /*
    cx.stm
    T_Label(t)
    unNx(then)
    T_Label(f)
    */
    return Tr_Nx(T_Seq(cx.stm,
                T_Seq(T_Label(t),
                    T_Seq(unNx(then),
                        T_Label(f)))));
}

Tr_exp Tr_IfThenElse(Tr_exp test, Tr_exp then, Tr_exp elsee)
{
    Temp_temp r = Temp_newtemp();
    Temp_label t = Temp_newlabel();
    Temp_label f = Temp_newlabel();
    Temp_label done = Temp_newlabel();
    struct Cx cx = unCx(test);
    doPatch(cx.trues, t);
    doPatch(cx.falses, f);
    /*
    cx.stm
    T_Label(t)
    T_Move(T_Temp(r), unEx(then))
    T_Jump(T_Name(done), Temp_LabelList(done, NULL))
    T_Label(f)
    T_Move(T_Temp(r), unEx(elsee))
    T_Jump(T_Name(done), Temp_LabelList(done, NULL))
    T_Label(done)
    T_Temp(r)
    */
    return Tr_Ex(T_Eseq(cx.stm,
            T_Eseq(T_Label(t),
                T_Eseq(T_Move(T_Temp(r), unEx(then)),
                    T_Eseq(T_Jump(T_Name(done), Temp_LabelList(done, NULL)),
                        T_Eseq(T_Label(f),
                            T_Eseq(T_Move(T_Temp(r), unEx(elsee)),
                                T_Eseq(T_Jump(T_Name(done), Temp_LabelList(done, NULL)),
                                    T_Eseq(T_Label(done), T_Temp(r))))))))));
}

Tr_exp Tr_While(Tr_exp test, Tr_exp body, Temp_label done)
{
    Temp_label t = Temp_newlabel();
    Temp_label b = Temp_newlabel();
    struct Cx cx = unCx(test);
    doPatch(cx.trues, b);
    doPatch(cx.falses, done);
    /*
    T_Label(t)
    cx.stm
    T_Label(b)
    unNx(body)
    T_Jump(T_Name(t), Temp_LabelList(t, NULL))
    T_Label(done)
    */
    return Tr_Nx(T_Seq(T_Label(t),
                T_Seq(cx.stm,
                    T_Seq(T_Label(b),
                        T_Seq(unNx(body),
                            T_Seq(T_Jump(T_Name(t), Temp_LabelList(t, NULL)),
                                T_Label(done)))))));
}

Tr_exp Tr_For(Tr_access access, Tr_level level, Tr_exp lo, Tr_exp hi, Tr_exp body, Temp_label done)
{
    Tr_exp i = Tr_simpleVar(access, level);
    Temp_temp limit = Temp_newtemp();
    Temp_label b = Temp_newlabel();
    Temp_label inc = Temp_newlabel();
    /*
    T_Move(unEx(i), unEx(lo))
    T_Move(T_Temp(limit), unEx(hi))
    T_Cjump(T_gt, unEx(i), T_Temp(limit), done, b)
    T_Label(b)
    unNx(body)
    T_Cjump(T_eq, unEx(i), T_Temp(limit), done, inc)
    T_Label(inc)
    T_Move(unEx(i), T_Binop(T_plus, unEx(i), T_Const(1)))
    T_Jump(T_Name(b), Temp_LabelList(b, NULL))
    T_Label(done)
    */
    return Tr_Nx(T_Seq(T_Move(unEx(i), unEx(lo)),
                T_Seq(T_Move(T_Temp(limit), unEx(hi)),
                    T_Seq(T_Cjump(T_gt, unEx(i), T_Temp(limit), done, b),
                        T_Seq(T_Label(b),
                            T_Seq(unNx(body),
                                T_Seq(T_Cjump(T_eq, unEx(i), T_Temp(limit), done, inc),
                                    T_Seq(T_Label(inc),
                                        T_Seq(T_Move(unEx(i), T_Binop(T_plus, unEx(i), T_Const(1))),
                                            T_Seq(T_Jump(T_Name(b), Temp_LabelList(b, NULL)),
                                                T_Label(done)))))))))));
}

static T_stm assign_field(Temp_temp r, int num, Tr_expList fields)
{
    if (fields) {
        return T_Seq(T_Move(T_Mem(T_Binop(T_plus, T_Temp(r), T_Const(F_wordSize * num))), unEx(fields->head)),
                assign_field(r, num - 1, fields->tail));
    } else {
        return T_Exp(T_Const(0));
    }
}

Tr_exp Tr_Record(int num, Tr_expList fields)
{
    Temp_temp r = Temp_newtemp();
    /*
    T_Move(T_Temp(r), F_externalCall("Malloc", T_ExpList(T_Const(F_wordSize * num)), NULL))
    assign_field(r, 0, fields)
    T_Temp(r)
    */
    return Tr_Ex(T_Eseq(T_Move(T_Temp(r), F_externalCall("Malloc", T_ExpList(T_Const(F_wordSize * num), NULL))),
                T_Eseq(assign_field(r, num - 1, fields),
                    T_Temp(r))));
}

Tr_exp Tr_Array(Tr_exp size, Tr_exp init)
{
    Temp_temp r = Temp_newtemp();
    Temp_temp i = Temp_newtemp();
    Temp_temp limit = Temp_newtemp();
    Temp_temp v = Temp_newtemp();
    Temp_label t = Temp_newlabel();
    Temp_label b = Temp_newlabel();
    Temp_label done = Temp_newlabel();
    /*
    T_Move(T_Temp(limit), unEx(size))
    T_Move(T_Temp(v), unEx(init))
    T_Move(T_Temp(r), F_externalCall("Malloc", T_ExpList(T_Binop(T_mul, T_Temp(limit), T_Const(F_wordSize)), NULL)))
    T_Move(T_Temp(i), T_Const(0))
    T_Label(t)
    T_Cjump(T_lt, T_Temp(i), T_Temp(limit), b, done)
    T_Label(b)
    T_Move(T_Mem(T_Binop(T_plus, T_Temp(r), T_Binop(T_mul, T_Temp(i), T_Const(F_wordSize)))), T_Temp(v))
    T_Move(T_Temp(i), T_Binop(T_plus, T_Temp(i), T_Const(1)))
    T_Jump(T_Name(t), Temp_LabelList(t, NULL))
    T_Label(done)
    T_Temp(r)
    */
    return Tr_Ex(T_Eseq(T_Move(T_Temp(limit), unEx(size)),
                T_Eseq(T_Move(T_Temp(v), unEx(init)),
                        T_Eseq(T_Move(T_Temp(r), F_externalCall("Malloc", T_ExpList(T_Binop(T_mul, T_Temp(limit), T_Const(F_wordSize)), NULL))),
                            T_Eseq(T_Move(T_Temp(i), T_Const(0)),
                                T_Eseq(T_Label(t),
                                    T_Eseq(T_Cjump(T_lt, T_Temp(i), T_Temp(limit), b, done),
                                        T_Eseq(T_Label(b),
                                            T_Eseq(T_Move(T_Mem(T_Binop(T_plus, T_Temp(r), T_Binop(T_mul, T_Temp(i), T_Const(F_wordSize)))), T_Temp(v)),
                                                T_Eseq(T_Move(T_Temp(i), T_Binop(T_plus, T_Temp(i), T_Const(1))),
                                                    T_Eseq(T_Jump(T_Name(t), Temp_LabelList(t, NULL)),
                                                        T_Eseq(T_Label(done),
                                                            T_Temp(r)))))))))))));
}

Tr_exp Tr_simpleVar(Tr_access access, Tr_level level)
{
    T_exp fp = staticLink(level, access->level);
    return Tr_Ex(F_Exp(access->access, fp));
}

Tr_exp Tr_fieldVar(Tr_exp addr, int off)
{
    return Tr_Ex(T_Mem(T_Binop(T_plus,
                    unEx(addr),
                    T_Const(off * F_wordSize))));
}

Tr_exp Tr_subscriptVar(Tr_exp addr, Tr_exp off)
{
    return Tr_Ex(T_Mem(T_Binop(T_plus,
                    unEx(addr),
                    T_Binop(T_mul, unEx(off), T_Const(F_wordSize)))));
}
    
void Tr_Func(Tr_exp body, Tr_level level) /* TODO */
{
    F_frag frag = F_ProcFrag(NULL, NULL);
    fragList = F_FragList(frag, fragList);
}

