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

struct Tr_access_ {
	//Lab5: your code here
};


struct Tr_accessList_ {
	Tr_access head;
	Tr_accessList tail;	
};



struct Tr_level_ {
	//Lab5: your code here
};

void Tr_procEntryExit(Tr_level level, Tr_exp body, Tr_accessList formals)
{
    /* TODO */
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
    
void Tr_Func(Tr_exp body) /* TODO */
{
    F_frag frag = F_ProcFrag(NULL, NULL);
    fragList = F_FragList(frag, fragList);
}

