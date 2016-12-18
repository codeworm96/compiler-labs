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
    if (s->kind == T_MOVE && s->u.MOVE.dst->kind == T_TEMP && s->u.MOVE.src->kind == T_TEMP) {
        Temp_temp src = s->u.MOVE.src->u.TEMP;
        Temp_temp dst = s->u.MOVE.dst->u.TEMP;
        emit(AS_Move("movl `s0, `d0\n", L(dst, NULL), L(src, NULL)));
        return;
    }
    if (s->kind == T_MOVE && s->u.MOVE.dst->kind == T_TEMP) {
        Temp_temp src = munchExp(s->u.MOVE.src);
        Temp_temp dst = s->u.MOVE.dst->u.TEMP;
        emit(AS_Move("movl `s0, `d0\n", L(dst, NULL), L(src, NULL)));
        return;
    }
    if (s->kind == T_MOVE && s->u.MOVE.dst->kind == T_MEM) {
        Temp_temp src = munchExp(s->u.MOVE.src);
        Temp_temp dst = munchExp(s->u.MOVE.dst->u.MEM);
        emit(AS_Oper("movl `s0, (`s1)\n", NULL, L(src, L(dst, NULL)), AS_Targets(NULL)));
        return;
    }
    if (s->kind == T_JUMP && s->u.JUMP.exp->kind == T_NAME) {
        Temp_label l = s->u.JUMP.exp->u.NAME;
        char *a = checked_malloc(MAXLINE * sizeof(char));
        sprintf(a, "jmp %s\n", Temp_labelstring(l));
        emit(AS_Oper(a, NULL, NULL, AS_Targets(s->u.JUMP.jumps)));
        return;
    }
    if (s->kind == T_JUMP) {
        Temp_temp t = munchExp(s->u.JUMP.exp);
        emit(AS_Oper("jmp *`s0\n", NULL, L(t, NULL), AS_Targets(s->u.JUMP.jumps)));
        return;
    }
    if (s->kind == T_CJUMP && s->u.CJUMP.op == T_eq) {
        Temp_temp l = munchExp(s->u.CJUMP.left);
        Temp_temp r = munchExp(s->u.CJUMP.right);
        char *a = checked_malloc(MAXLINE * sizeof(char));
        emit(AS_Oper("cmp `s0, `s1\n", NULL, L(r, L(l, NULL)), AS_Targets(NULL)));
        sprintf(a, "je %s\n", Temp_labelstring(s->u.CJUMP.true));
        emit(AS_Oper(a, NULL, NULL, AS_Targets(Temp_LabelList(s->u.CJUMP.true, NULL))));
        return;
    }
    if (s->kind == T_CJUMP && s->u.CJUMP.op == T_ne) {
        Temp_temp l = munchExp(s->u.CJUMP.left);
        Temp_temp r = munchExp(s->u.CJUMP.right);
        char *a = checked_malloc(MAXLINE * sizeof(char));
        emit(AS_Oper("cmp `s0, `s1\n", NULL, L(r, L(l, NULL)), AS_Targets(NULL)));
        sprintf(a, "jne %s\n", Temp_labelstring(s->u.CJUMP.true));
        emit(AS_Oper(a, NULL, NULL, AS_Targets(Temp_LabelList(s->u.CJUMP.true, NULL))));
        return;
    }
    if (s->kind == T_CJUMP && s->u.CJUMP.op == T_lt) {
        Temp_temp l = munchExp(s->u.CJUMP.left);
        Temp_temp r = munchExp(s->u.CJUMP.right);
        char *a = checked_malloc(MAXLINE * sizeof(char));
        emit(AS_Oper("cmp `s0, `s1\n", NULL, L(r, L(l, NULL)), AS_Targets(NULL)));
        sprintf(a, "jl %s\n", Temp_labelstring(s->u.CJUMP.true));
        emit(AS_Oper(a, NULL, NULL, AS_Targets(Temp_LabelList(s->u.CJUMP.true, NULL))));
        return;
    }
    if (s->kind == T_CJUMP && s->u.CJUMP.op == T_gt) {
        Temp_temp l = munchExp(s->u.CJUMP.left);
        Temp_temp r = munchExp(s->u.CJUMP.right);
        char *a = checked_malloc(MAXLINE * sizeof(char));
        emit(AS_Oper("cmp `s0, `s1\n", NULL, L(r, L(l, NULL)), AS_Targets(NULL)));
        sprintf(a, "jg %s\n", Temp_labelstring(s->u.CJUMP.true));
        emit(AS_Oper(a, NULL, NULL, AS_Targets(Temp_LabelList(s->u.CJUMP.true, NULL))));
        return;
    }
    if (s->kind == T_CJUMP && s->u.CJUMP.op == T_le) {
        Temp_temp l = munchExp(s->u.CJUMP.left);
        Temp_temp r = munchExp(s->u.CJUMP.right);
        char *a = checked_malloc(MAXLINE * sizeof(char));
        emit(AS_Oper("cmp `s0, `s1\n", NULL, L(r, L(l, NULL)), AS_Targets(NULL)));
        sprintf(a, "jle %s\n", Temp_labelstring(s->u.CJUMP.true));
        emit(AS_Oper(a, NULL, NULL, AS_Targets(Temp_LabelList(s->u.CJUMP.true, NULL))));
        return;
    }
    if (s->kind == T_CJUMP && s->u.CJUMP.op == T_ge) {
        Temp_temp l = munchExp(s->u.CJUMP.left);
        Temp_temp r = munchExp(s->u.CJUMP.right);
        char *a = checked_malloc(MAXLINE * sizeof(char));
        emit(AS_Oper("cmp `s0, `s1\n", NULL, L(r, L(l, NULL)), AS_Targets(NULL)));
        sprintf(a, "jge %s\n", Temp_labelstring(s->u.CJUMP.true));
        emit(AS_Oper(a, NULL, NULL, AS_Targets(Temp_LabelList(s->u.CJUMP.true, NULL))));
        return;
    }
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
}

static void pushArgs(T_expList l)
{
    if (l) {
        Temp_temp s;
        pushArgs(l->tail);
        s = munchExp(l->head);
        emit(AS_Oper("pushl `s0\n", NULL, L(s, NULL), AS_Targets(NULL)));
    }
}

static Temp_temp munchExp(T_exp e)
{
    if (e->kind == T_CALL && e->u.CALL.fun->kind == T_NAME) {
        Temp_temp rv = F_RV();
        Temp_temp r = Temp_newtemp();
        Temp_label fun = e->u.CALL.fun->u.NAME;
        char *a = checked_malloc(MAXLINE * sizeof(char));
        pushArgs(e->u.CALL.args);
        sprintf(a, "call %s\n", Temp_labelstring(fun));
        emit(AS_Oper(a, L(rv, L(F_ecx(), L(F_edx(), NULL))), NULL, AS_Targets(NULL)));
        emit(AS_Move("movl `s0, `d0\n", L(r, NULL), L(rv, NULL)));
        return r;
    }
    if (e->kind == T_CALL) {
        Temp_temp rv = F_RV();
        Temp_temp r = Temp_newtemp();
        Temp_temp s = munchExp(e->u.CALL.fun);
        pushArgs(e->u.CALL.args);
        emit(AS_Oper("call *`s0\n", L(rv, L(F_ecx(), L(F_edx(), NULL))), L(s, NULL), AS_Targets(NULL)));
        emit(AS_Move("movl `s0, `d0\n", L(r, NULL), L(rv, NULL)));
        return r;
    }
    if (e->kind == T_BINOP && e->u.BINOP.op == T_plus) {
        Temp_temp a = munchExp(e->u.BINOP.left);
        Temp_temp b = munchExp(e->u.BINOP.right);
        Temp_temp r = Temp_newtemp();
        emit(AS_Move("movl `s0, `d0\n", L(r, NULL), L(a, NULL)));
        emit(AS_Oper("addl `s0, `d0\n", L(r, NULL), L(b, L(r, NULL)), AS_Targets(NULL)));
        return r;
    }
    if (e->kind == T_BINOP && e->u.BINOP.op == T_minus) {
        Temp_temp a = munchExp(e->u.BINOP.left);
        Temp_temp b = munchExp(e->u.BINOP.right);
        Temp_temp r = Temp_newtemp();
        emit(AS_Move("movl `s0, `d0\n", L(r, NULL), L(a, NULL)));
        emit(AS_Oper("subl `s0, `d0\n", L(r, NULL), L(b, L(r, NULL)), AS_Targets(NULL)));
        return r;
    }
    if (e->kind == T_BINOP && e->u.BINOP.op == T_mul) {
        Temp_temp a = munchExp(e->u.BINOP.left);
        Temp_temp b = munchExp(e->u.BINOP.right);
        Temp_temp r = Temp_newtemp();
        emit(AS_Move("movl `s0, `d0\n", L(r, NULL), L(a, NULL)));
        emit(AS_Oper("imul `s0, `d0\n", L(r, NULL), L(b, L(r, NULL)), AS_Targets(NULL)));
        return r;
    }
    if (e->kind == T_BINOP && e->u.BINOP.op == T_div) {
        Temp_temp a = munchExp(e->u.BINOP.left);
        Temp_temp b = munchExp(e->u.BINOP.right);
        Temp_temp edx = F_edx();
        Temp_temp eax = F_eax();
        Temp_temp r = Temp_newtemp();
        emit(AS_Move("movl `s0, `d0\n", L(eax, NULL), L(a, NULL)));
        emit(AS_Oper("cltd\n", L(edx, L(eax, NULL)), L(eax, NULL), AS_Targets(NULL)));
        emit(AS_Oper("idivl `s0\n", L(edx, L(eax, NULL)), L(b, L(edx, L(eax, NULL))), AS_Targets(NULL)));
        emit(AS_Move("movl `s0, `d0\n", L(r, NULL), L(eax, NULL)));
        return r;
    }
    if (e->kind == T_CONST) {
        char *a = checked_malloc(MAXLINE * sizeof(char));
        Temp_temp r = Temp_newtemp();
        sprintf(a, "movl $%d, `d0\n", e->u.CONST);
        emit(AS_Oper(a, L(r, NULL), NULL, AS_Targets(NULL)));
        return r;
    }
    if (e->kind == T_NAME) {
        char *a = checked_malloc(MAXLINE * sizeof(char));
        Temp_temp r = Temp_newtemp();
        sprintf(a, "movl $%s, `d0\n", Temp_labelstring(e->u.NAME));
        emit(AS_Oper(a, L(r, NULL), NULL, AS_Targets(NULL)));
        return r;
    }
    if (e->kind == T_MEM) {
        Temp_temp r = Temp_newtemp();
        Temp_temp s = munchExp(e->u.MEM);
        emit(AS_Oper("movl (`s0), `d0\n", L(r, NULL), L(s, NULL), AS_Targets(NULL)));
        return r;
    }
    if (e->kind == T_ESEQ) {
        munchStm(e->u.ESEQ.stm);
        return munchExp(e->u.ESEQ.exp);
    }
    if (e->kind == T_TEMP) {
        return e->u.TEMP;
    }
    assert(0); /* control flow should never reach here */
}

AS_instrList F_codegen(F_frame f, T_stmList stmList) {
    AS_instrList list;
    T_stmList sl;
    for (sl = stmList; sl; sl = sl->tail) {
        munchStm(sl->head);
    }
    emit(AS_Oper("", NULL, L(F_RV(), L(F_ebx(), L(F_esi(), L(F_edi(), NULL)))), AS_Targets(NULL)));
    list = iList;
    iList = NULL;
    last = NULL;
    return list;
}
