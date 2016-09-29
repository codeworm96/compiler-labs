/* This file is not complete.  You should fill it in with your
   solution to the programming exercise. */
#include <stdio.h>
#include <string.h>
#include "prog1.h"
#include "slp.h"
#include "util.h"

int maxargs(A_stm stm);
void interp(A_stm stm);

typedef struct table *Table_;
struct table { string id; int value; Table_ tail; };
Table_ Table(string id, int value, Table_ tail)
{
    Table_ t = checked_malloc(sizeof(*t));
    t->id = id;
    t->value = value;
    t->tail = tail;
    return t;
}

struct IntAndTable { int i; Table_ t; };
struct IntAndTable makeIntAndTable(int i, Table_ t)
{
    struct IntAndTable res;
    res.i = i;
    res.t = t;
    return res;
}

Table_ update(Table_ t, string key, int value);
int lookup(Table_ t, string key);

Table_ interpPrint(A_expList es, Table_ t);
Table_ interpStm(A_stm s, Table_ t);
struct IntAndTable interpExp(A_exp e, Table_ t);

int max(int x, int y);

int countArgs(A_expList es);
int maxargsExp(A_exp e);
int maxargsExpList(A_expList es);

/*
 *Please don't modify the main() function
 */
int main()
{
	int args;

	printf("prog\n");
	args = maxargs(prog());
	printf("args: %d\n",args);
	interp(prog());

	printf("prog_prog\n");
	args = maxargs(prog_prog());
	printf("args: %d\n",args);
	interp(prog_prog());

	printf("right_prog\n");
	args = maxargs(right_prog());
	printf("args: %d\n",args);
	interp(right_prog());

	return 0;
}

Table_ update(Table_ t, string key, int value)
{
    return Table(key, value, t);
}

int lookup(Table_ t, string key)
{
    assert(t); /* table not empty */

    if (strcmp(t->id, key) == 0) {
        return t->value;
    } else {
        return lookup(t->tail, key);
    }
}

void interp(A_stm stm)
{
    interpStm(stm, NULL);
}

Table_ interpPrint(A_expList es, Table_ t)
{
    switch(es->kind) {
        case A_pairExpList:
            {
                struct IntAndTable res = interpExp(es->u.pair.head, t);
                printf("%d ", res.i);
                return interpPrint(es->u.pair.tail, res.t);
            }
            break;
        case A_lastExpList:
            {
                struct IntAndTable res = interpExp(es->u.last, t);
                printf("%d\n", res.i);
                return res.t;
            }
            break;
        default:
            assert(0); /* control flow should not reach here. */
    }
}

Table_ interpStm(A_stm s, Table_ t) {
    switch(s->kind) {
        case A_compoundStm:
            {
                Table_ table = interpStm(s->u.compound.stm1, t);
                return interpStm(s->u.compound.stm2, table);
            }
            break;
        case A_assignStm:
            {
                struct IntAndTable res = interpExp(s->u.assign.exp, t);
                return update(res.t, s->u.assign.id, res.i);
            }
            break;
        case A_printStm:
            return interpPrint(s->u.print.exps, t);
            break;
        default:
            assert(0); /* control flow should not reach here. */
    }
}

struct IntAndTable interpExp(A_exp e, Table_ t)
{
    switch(e->kind) {
        case A_idExp:
            return makeIntAndTable(lookup(t, e->u.id), t);
            break;
        case A_numExp:
            return makeIntAndTable(e->u.num, t);
            break;
        case A_opExp:
            {
                struct IntAndTable left_res = interpExp(e->u.op.left, t);
                struct IntAndTable right_res = interpExp(e->u.op.right, left_res.t);
                switch(e->u.op.oper) {
                    case A_plus:
                        return makeIntAndTable(left_res.i + right_res.i, right_res.t);
                        break;
                    case A_minus:
                        return makeIntAndTable(left_res.i - right_res.i, right_res.t);
                        break;
                    case A_times:
                        return makeIntAndTable(left_res.i * right_res.i, right_res.t);
                        break;
                    case A_div:
                        assert(right_res.i); /* check for division by zero */
                        return makeIntAndTable(left_res.i / right_res.i, right_res.t);
                        break;
                    default:
                        assert(0); /* control flow should not reach here. */
                }
            }
            break;
        case A_eseqExp:
            {
                Table_ table = interpStm(e->u.eseq.stm, t);
                return interpExp(e->u.eseq.exp, table);
            }
            break;
        default:
            assert(0); /* control flow should not reach here. */
    }
}

int max(int x, int y)
{
    return x > y ? x : y;
}

int countArgs(A_expList es)
{
    switch(es->kind) {
        case A_pairExpList:
            return 1 + countArgs(es->u.pair.tail);
            break;
        case A_lastExpList:
            return 1;
            break;
        default:
            assert(0); /* control flow should not reach here. */
    }
}

int maxargsExp(A_exp e)
{
    switch(e->kind) {
        case A_idExp:
        case A_numExp:
            return 0;
            break;
        case A_opExp:
            return max(maxargsExp(e->u.op.left), maxargsExp(e->u.op.right));
            break;
        case A_eseqExp:
            return max(maxargs(e->u.eseq.stm), maxargsExp(e->u.eseq.exp));
            break;
        default:
            assert(0); /* control flow should not reach here. */
    }
}

int maxargsExpList(A_expList es)
{
    switch(es->kind) {
        case A_pairExpList:
            return max(maxargsExp(es->u.pair.head), maxargsExpList(es->u.pair.tail));
            break;
        case A_lastExpList:
            return maxargsExp(es->u.last);
            break;
        default:
            assert(0); /* control flow should not reach here. */
    }
}

int maxargs(A_stm stm)
{
    switch(stm->kind) {
        case A_compoundStm:
            return max(maxargs(stm->u.compound.stm1), maxargs(stm->u.compound.stm2));
            break;
        case A_assignStm:
            return maxargsExp(stm->u.assign.exp);
            break;
        case A_printStm:
            return max(countArgs(stm->u.print.exps), maxargsExpList(stm->u.print.exps));
            break;
        default:
            assert(0); /* control flow should not reach here. */
    }
}

