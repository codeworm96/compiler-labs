#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "color.h"
#include "flowgraph.h"
#include "liveness.h"
#include "regalloc.h"
#include "table.h"

#define K 6
#define MAXLINE 40

static char *reg_names[7] = {"undef", "%eax", "%ebx", "%ecx", "%edx", "%esi", "%edi"};

static G_table degree;
static G_table color;
static G_table alias;
static G_nodeList spillWorklist;
static G_nodeList simplifyWorklist;
static G_nodeList selectStack;
static G_nodeList spillNodes;

static void build(struct Live_graph g)
{
    degree = G_empty();
    color = G_empty();
    alias = G_empty();
    G_nodeList p = G_nodes(g.graph);
    for (; p != NULL; p = p->tail) {
        int * t = checked_malloc(sizeof(int));
        *t = 0;
        for (G_nodeList cur = G_succ(p->head); cur; cur = cur->tail) {
            *t++;
        }
        G_enter(degree, p->head, t);

        int * c = checked_malloc(sizeof(int));
        Temp_temp temp = Live_gtemp(p->head);
        if (temp == F_eax()) {
            *c = 1;
        } else if (temp == F_ebx()) {
            *c = 2;
        } else if (temp == F_ecx()) {
            *c = 3;
        } else if (temp == F_edx()) {
            *c = 4;
        } else if (temp == F_esi()) {
            *c = 5;
        } else if (temp == F_edi()) {
            *c = 6;
        } else {
            *c = 0;
        }
        G_enter(color, p->head, c);

        G_node * a = checked_malloc(sizeof(G_node));
        *a = p->head;
        G_enter(alias, p->head, a);
    }
    spillWorklist = NULL;
    simplifyWorklist = NULL;
    selectStack = NULL;
}

static G_node GetAlias(G_node n)
{
    G_node * a = G_look(alias, n);
    if (*a != n) {
        *a = GetAlias(*a);
    }
    return *a;
}

static void makeWorklist(struct Live_graph g)
{
    G_nodeList p = G_nodes(g.graph);
    for (; p; p = p->tail) {
        int * deg = G_look(degree, p->head);
        int * c = G_look(color, p->head);
        if (*c == 0) {
            if (*deg >= K) {
                spillWorklist = G_NodeList(p->head, spillWorklist);
            } else {
                simplifyWorklist = G_NodeList(p->head, simplifyWorklist);
            }
        }
    }
}

static G_nodeList adjacent(G_node n)
{
    return G_SubNodeList(G_succ(n), selectStack);
}

static void decrementDegree(G_node n)
{
    int *d = G_look(degree, n);
    int *c = G_look(color, n);
    *d--;
    if (*d == K && *c == 0) {
        spillWorklist = G_SubNodeList(spillWorklist, G_NodeList(n, NULL));
        simplifyWorklist = G_NodeList(n, simplifyWorklist);
    }
}

static void simplify()
{
    while (simplifyWorklist) {
        G_node cur = simplifyWorklist->head;
        simplifyWorklist = simplifyWorklist->tail;
        selectStack = G_NodeList(cur, selectStack);
        for (G_nodeList p = adjacent(cur); p; p = p->tail) {
            decrementDegree(p->head);
        }
    }
}

static void selectSpill()
{
    simplifyWorklist = G_NodeList(spillWorklist->head, simplifyWorklist);
    spillWorklist = spillWorklist->tail;
}

static void assignColors(struct Live_graph g)
{
    bool used[K+1];
    int i;
    spillNodes = NULL;
    while (selectStack) {
        G_node cur = selectStack->head;
        selectStack = selectStack->tail;
        /* printf("coloring %d %d\n", Live_gtemp(cur)->num, G_degree(cur)); */
        for (i = 1; i <= K; ++i) {
            used[i] = FALSE;
        }
        for (G_nodeList p = G_succ(cur); p; p = p->tail) {
            int *t = G_look(color, GetAlias(p->head));
            /* printf("color of %d is %d\n", Live_gtemp(p->head)->num, *t); */
            used[*t] = TRUE;
        }
        for (i = 1; i <= K; ++i) {
            if (!used[i]) {
                break;
            }
        }
        if (i > K) {
            spillNodes = G_NodeList(cur, spillNodes);
            return;
        } else {
            int *c = G_look(color, cur);
            *c = i;
        }
    }
    for (G_nodeList p = G_nodes(g.graph); p != NULL; p = p->tail) {
        int *c0 = G_look(color, GetAlias(p->head));
        int *c = G_look(color, p->head);
        *c = *c0;
    }
}

Temp_tempList* Inst_def(AS_instr inst) {
    switch (inst->kind) {
        case I_OPER:
            return &inst->u.OPER.dst;
        case I_LABEL:
            return NULL;
        case I_MOVE:
            return &inst->u.MOVE.dst;
        default:
            assert(0);
    }
    return NULL;
}

Temp_tempList* Inst_use(AS_instr inst) {
    switch (inst->kind) {
        case I_OPER:
            return &inst->u.OPER.src;
        case I_LABEL:
            return NULL;
        case I_MOVE:
            return &inst->u.MOVE.src;
        default:
            assert(0);
    }
    return NULL;
}

static void rewriteProgram(F_frame f, AS_instrList *pil)
{
    AS_instrList il = *pil, l, last, next, new_instr;
    int off;
    while(spillNodes) {
        G_node cur = spillNodes->head;
        spillNodes = spillNodes->tail;
        Temp_temp c = Live_gtemp(cur);

        off = F_spill(f);

        l = il;
        last = NULL;
        while(l) {
            Temp_temp t = NULL;
            next = l->tail;
            Temp_tempList *def = Inst_def(l->head);
            Temp_tempList *use = Inst_use(l->head);
            if (use && Temp_inTempList(c, *use)) {
                if (t == NULL) {
                    t = Temp_newtemp();
                }
                *use = Temp_replaceTempList(*use, c, t);
                char *a = checked_malloc(MAXLINE * sizeof(char));
                sprintf(a, "movl %d(%%ebp), `d0\n", off);
                new_instr = AS_InstrList(AS_Oper(a, Temp_TempList(t, NULL), NULL, AS_Targets(NULL)), l);
                if (last) {
                    last->tail = new_instr;
                } else {
                    il = new_instr;
                }
            }
            last = l;
            if (def && Temp_inTempList(c, *def)) {
                if (t == NULL) {
                    t = Temp_newtemp();
                }
                *def = Temp_replaceTempList(*def, c, t);
                char *a = checked_malloc(MAXLINE * sizeof(char));
                sprintf(a, "movl `s0, %d(%%ebp)\n", off);
                l->tail = AS_InstrList(AS_Oper(a, NULL, Temp_TempList(t, NULL), AS_Targets(NULL)), next);
                last = l->tail;
            }
            l = next;
        }
    }
    *pil = il;
}

static Temp_map generate_map(struct Live_graph g)
{
    Temp_map res = Temp_empty();
    G_nodeList p = G_nodes(g.graph);
    for (; p != NULL; p = p->tail) {
        int * t = G_look(color, p->head);
        char * a = checked_malloc(sizeof(char) * MAXLINE);
        sprintf(a, "%s%d", reg_names[*t], Live_gtemp(p->head)->num);
        Temp_enter(res, Live_gtemp(p->head), reg_names[*t]);
    }

    /* ebp */
    Temp_enter(res, F_FP(), "%ebp");

    return res;
}

struct RA_result RA_regAlloc(F_frame f, AS_instrList il) {
    struct Live_graph live_graph;
    bool done = FALSE;
    while (!done) {
        G_graph flow_graph = FG_AssemFlowGraph(il, f);
        live_graph = Live_liveness(flow_graph);
        build(live_graph);
        makeWorklist(live_graph);
        while (simplifyWorklist || spillWorklist) {
            if (simplifyWorklist) {
                simplify();
            } else if (spillWorklist) {
                selectSpill();
            }
        }
        assignColors(live_graph);
        if (spillNodes) {
            rewriteProgram(f, &il);
        } else {
            done = TRUE;
        }
    }

    struct RA_result ret;
    ret.il = il;
    ret.coloring = generate_map(live_graph);

    return ret;
}
