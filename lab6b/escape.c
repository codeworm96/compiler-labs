#include "util.h"
#include "symbol.h" 
#include "absyn.h"  
#include <stdlib.h>
#include <stdio.h>
#include "table.h"

typedef struct escapeEntry_ *escapeEntry;

struct escapeEntry_ {
    int depth;
    bool *esc;
};

escapeEntry EscapeEntry(int depth, bool *esc)
{
    escapeEntry res = checked_malloc(sizeof(*res));
    res->depth = depth;
    res->esc = esc;
    return res;
}

static void traverseExp(S_table env, int depth, A_exp e);
static void traverseDec(S_table env, int depth, A_dec d);
static void traverseVar(S_table env, int depth, A_var v);

void Esc_findEscape(A_exp exp) {
    traverseExp(S_empty(), 0, exp);
}

static void traverseExp(S_table env, int depth, A_exp e)
{
    switch(e->kind) {
        case A_varExp:
            traverseVar(env, depth, e->u.var);
            break;
        case A_nilExp:
        case A_intExp:
        case A_stringExp:
        case A_breakExp:
            break;
        case A_callExp:
            for (A_expList arg = e->u.call.args; arg; arg = arg->tail) {
                traverseExp(env, depth, arg->head);
            }
            break;
        case A_opExp:
            traverseExp(env, depth, e->u.op.left);
            traverseExp(env, depth, e->u.op.right);
            break;
        case A_recordExp:
            for (A_efieldList ef = e->u.record.fields; ef; ef = ef->tail) {
                traverseExp(env, depth, ef->head->exp);
            }
            break;
        case A_seqExp:
            for (A_expList cur = e->u.seq; cur; cur = cur->tail) {
                traverseExp(env, depth, cur->head);
            }
            break;
        case A_assignExp:
            traverseVar(env, depth, e->u.assign.var);
            traverseExp(env, depth, e->u.assign.exp);
            break;
        case A_ifExp:
            traverseExp(env, depth, e->u.iff.test);
            traverseExp(env, depth, e->u.iff.then);
            if (e->u.iff.elsee) {
                traverseExp(env, depth, e->u.iff.elsee);
            }
            break;
        case A_whileExp:
            traverseExp(env, depth, e->u.whilee.test);
            traverseExp(env, depth, e->u.whilee.body);
            break;
        case A_forExp:
            traverseExp(env, depth, e->u.forr.lo);
            traverseExp(env, depth, e->u.forr.hi);
            S_beginScope(env);
            e->u.forr.escape = FALSE;
            S_enter(env, e->u.forr.var, EscapeEntry(depth, &e->u.forr.escape));
            traverseExp(env, depth, e->u.forr.body);
            S_endScope(env);
            break;
        case A_letExp:
            S_beginScope(env);
            for (A_decList d = e->u.let.decs; d; d = d->tail) {
                traverseDec(env, depth, d->head);
            }
            traverseExp(env, depth, e->u.let.body);
            S_endScope(env);
            break;
        case A_arrayExp:
            traverseExp(env, depth, e->u.array.size);
            traverseExp(env, depth, e->u.array.init);
            break;
    }
}

static void traverseVar(S_table env, int depth, A_var v)
{
    switch(v->kind) {
        case A_simpleVar:
            {
                escapeEntry esc = S_look(env, v->u.simple);
                if (esc->depth < depth) {
                    *(esc->esc) = TRUE;
                }
                break;
            }
        case A_fieldVar:
            traverseVar(env, depth, v->u.field.var);
            break;
        case A_subscriptVar:
            traverseVar(env, depth, v->u.subscript.var);
            traverseExp(env, depth, v->u.subscript.exp);
            break;
        default:
            assert(0); /* control flow should never reach here. */
    }
}

static void traverseDec(S_table env, int depth, A_dec d)
{
    switch (d->kind) {
        case A_varDec:
            traverseExp(env, depth, d->u.var.init);
            d->u.var.escape = FALSE;
            S_enter(env, d->u.var.var, EscapeEntry(depth, &d->u.var.escape));
            break;
        case A_functionDec:
            for (A_fundecList fun = d->u.function; fun; fun = fun->tail) {
                S_beginScope(env);
                for (A_fieldList l = fun->head->params; l; l = l->tail) {
                    l->head->escape = FALSE;
                    S_enter(env, l->head->name, EscapeEntry(depth + 1, &l->head->escape));
                }
                traverseExp(env, depth + 1, fun->head->body);
                S_endScope(env);
            }
            break;
        case A_typeDec:
            break;
    }
}
