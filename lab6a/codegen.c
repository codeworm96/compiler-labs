#include <stdio.h>
#include <stdlib.h>
#include "util.h"
#include "symbol.h"
#include "absyn.h"
#include "temp.h"
#include "errormsg.h"
#include "tree.h"
#include "assem.h"
#include "frame.h"
#include "codegen.h"
#include "table.h"

//Lab 6: your code here

#define MAXLINE 40

static AS_instrList iList = NULL;
static AS_instrList last = NULL;

static void emit(AS_instr inst)
{
    if (last != NULL) {
        last->tail = AS_InstrList(inst, NULL);
        last = last->tail;
    } else {
        iList = AS_InstrList(inst, NULL);
        last = iList;
    }
}

static Temp_tempList L(Temp_temp h, Temp_tempList t)
{
    return Temp_TempList(h, t);
}

static void munchStm(T_stm s);
static Temp_temp munchExp(T_exp e);

static void munchStm(T_stm s)
{
    if (s->kind == T_LABEL) {
        char *a = checked_malloc(MAXLINE * sizeof(char));
        sprintf(a, "%s:\n", Temp_labelstring(s->u.LABEL));
        emit(AS_Label(a, s->u.LABEL));
        return;
    }
    if (s->kind == T_SEQ) {
        munchStm(s->u.SEQ.left);
        munchStm(s->u.SEQ.right);
        return;
    }
    if (s->kind == T_EXP) {
        munchExp(s->u.EXP);
        return;
    }
    emit(AS_Oper("mov", NULL, NULL, NULL));
}

static void pushArgs(T_expList l)
{
    if (l) {
        Temp_temp s;
        pushArgs(l->tail);
        s = munchExp(l->head);
        emit(AS_Oper("pushl `s0\n", NULL, L(s, NULL), NULL));
    }
}

static Temp_temp munchExp(T_exp e)
{
    if (e->kind == T_CALL && e->u.CALL.fun->kind == T_NAME) {
        /* TODO: eax */
        Temp_temp r = Temp_newtemp();
        Temp_label fun = e->u.CALL.fun->u.NAME;
        char *a = checked_malloc(MAXLINE * sizeof(char));
        pushArgs(e->u.CALL.args);
        sprintf(a, "call %s\n", Temp_labelstring(fun));
        emit(AS_Oper(a, L(r, NULL), NULL, AS_Targets(Temp_LabelList(fun, NULL))));
        return r;
    }
    if (e->kind == T_CALL) {
        /* TODO: eax */
        Temp_temp r = Temp_newtemp();
        Temp_temp s = munchExp(e->u.CALL.fun);
        pushArgs(e->u.CALL.args);
        emit(AS_Oper("call *`s0\n", L(r, NULL), L(s, NULL), NULL));
        return r;
    }
    /* TODO: Binop */
    if (e->kind == T_CONST) {
        char *a = checked_malloc(MAXLINE * sizeof(char));
        Temp_temp r = Temp_newtemp();
        sprintf(a, "movl $%d, `d0\n", e->u.CONST);
        emit(AS_Oper(a, L(r, NULL), NULL, NULL));
        return r;
    }
    if (e->kind == T_NAME) {
        char *a = checked_malloc(MAXLINE * sizeof(char));
        Temp_temp r = Temp_newtemp();
        sprintf(a, "movl $%s, `d0\n", Temp_labelstring(e->u.NAME));
        emit(AS_Oper(a, L(r, NULL), NULL, NULL));
        return r;
    }
    if (e->kind == T_MEM) {
        Temp_temp r = Temp_newtemp();
        Temp_temp s = munchExp(e->u.MEM);
        emit(AS_Oper("movl (`s0), `d0\n", L(r, NULL), L(s, NULL), NULL));
        return r;
    }
    if (e->kind == T_ESEQ) {
        munchStm(e->u.ESEQ.stm);
        return munchExp(e->u.ESEQ.exp);
    }
    if (e->kind == T_TEMP) {
        return e->u.TEMP;
    }
    return Temp_newtemp();
}

AS_instrList F_codegen(F_frame f, T_stmList stmList) {
    AS_instrList list;
    T_stmList sl;
    for (sl = stmList; sl; sl = sl->tail) {
        munchStm(sl->head);
    }
    list = iList;
    iList = NULL;
    last = NULL;
    return list;
}
