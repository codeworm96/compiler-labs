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

static bool *adjSet;
static G_graph graph;
static G_table degree;
static G_table color;
static G_table alias;
static G_nodeList spillWorklist;
static G_nodeList simplifyWorklist;
static G_nodeList selectStack;
static G_nodeList spillNodes;
static G_nodeList coalescedNodes;
static G_nodeList freezeWorklist;
static Live_moveList worklistMoves;
static Live_moveList activeMoves;
static Live_moveList constrainedMoves;
static Live_moveList coalescedMoves;
static Live_moveList frozenMoves;

FILE * out;

static void build(struct Live_graph g)
{
    degree = G_empty();
    color = G_empty();
    alias = G_empty();
    for (G_nodeList p = G_nodes(g.graph); p; p = p->tail) {
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
    graph = g.graph;
    adjSet = g.adj;
    spillWorklist = NULL;
    simplifyWorklist = NULL;
    freezeWorklist = NULL;
    worklistMoves = g.moves;
    activeMoves = NULL;
    frozenMoves = NULL;
    constrainedMoves = NULL;
    coalescedMoves = NULL;
    selectStack = NULL;
    coalescedNodes = NULL;
}

static G_node GetAlias(G_node n)
{
    G_node * a = G_look(alias, n);
    if (*a != n) {
        *a = GetAlias(*a);
    }
    return *a;
}

static Live_moveList nodeMoves(G_node n)
{
    Live_moveList p = Live_UnionMoveList(activeMoves, worklistMoves);
    Live_moveList res = NULL;
    G_node m = GetAlias(n);
    for (Live_moveList cur = p; cur; cur = cur->tail) {
        if (GetAlias(cur->src) == m || GetAlias(cur->dst) == m) {
            res = Live_MoveList(cur->src, cur->dst, res);
        }
    }
    return res;
}

static bool moveRelated(G_node n)
{
    return nodeMoves(n) != NULL;
}

static void makeWorklist()
{
    G_nodeList p = G_nodes(graph);
    for (; p; p = p->tail) {
        int * deg = G_look(degree, p->head);
        int * c = G_look(color, p->head);
        if (*c == 0) {
            if (*deg >= K) {
                spillWorklist = G_NodeList(p->head, spillWorklist);
            } else if (moveRelated(p->head)) {
                freezeWorklist = G_NodeList(p->head, freezeWorklist);
            } else {
                simplifyWorklist = G_NodeList(p->head, simplifyWorklist);
            }
        }
    }
}

static G_nodeList adjacent(G_node n)
{
    return G_SubNodeList(G_SubNodeList(G_succ(n), selectStack), coalescedNodes);
}

static void enableMoves(G_nodeList nodes)
{
    for (G_nodeList p = nodes; p; p = p->tail) {
        for (Live_moveList m = nodeMoves(p->head); m; m = m->tail) {
            if (Live_inMoveList(m->src, m->dst, activeMoves)) {
                activeMoves = Live_SubMoveList(activeMoves, Live_MoveList(m->src, m->dst, NULL));
                worklistMoves = Live_UnionMoveList(worklistMoves, Live_MoveList(m->src, m->dst, NULL));
            }
        }
    }
}

static void decrementDegree(G_node n)
{
    int *d = G_look(degree, n);
    int *c = G_look(color, n);
    *d--;
    if (*d == K && *c == 0) {
        enableMoves(G_NodeList(n, adjacent(n)));
        spillWorklist = G_SubNodeList(spillWorklist, G_NodeList(n, NULL));
        if (moveRelated(n)) {
            freezeWorklist = G_NodeList(n, freezeWorklist);
        } else {
            simplifyWorklist = G_NodeList(n, simplifyWorklist);
        }
    }
}

static void simplify()
{
    G_node cur = simplifyWorklist->head;
    simplifyWorklist = simplifyWorklist->tail;
    selectStack = G_NodeList(cur, selectStack);
    for (G_nodeList p = adjacent(cur); p; p = p->tail) {
        decrementDegree(p->head);
    }
}

static void freezeMoves(G_node u)
{
    G_node v;
    for (Live_moveList m = nodeMoves(u); m; m = m->tail) {
        if (GetAlias(m->dst) == GetAlias(u)) {
            v = GetAlias(m->src);
        } else {
            v = GetAlias(m->dst);
        }
        activeMoves = Live_SubMoveList(activeMoves, Live_MoveList(m->src, m->dst, NULL));
        frozenMoves = Live_UnionMoveList(frozenMoves, Live_MoveList(m->src, m->dst, NULL));
        int *deg = G_look(degree, v);
        if (!moveRelated(v) && *deg < K) {
            freezeWorklist = G_SubNodeList(freezeWorklist, G_NodeList(v, NULL));
            simplifyWorklist = G_NodeList(v, simplifyWorklist);
        }
    }
}

static void freeze()
{
    G_node u = freezeWorklist->head;
    freezeWorklist = freezeWorklist->tail;
    simplifyWorklist = G_NodeList(u, simplifyWorklist);
    freezeMoves(u);
}

static void selectSpill()
{
    G_node m = spillWorklist->head;
    spillWorklist = spillWorklist->tail;
    simplifyWorklist = G_NodeList(m, simplifyWorklist);
    freezeMoves(m);
}

static bool precolored(G_node n)
{
    int *c = G_look(color, n);
    return *c;
}

static bool ok(G_node v, G_node u)
{
    for (G_nodeList p = adjacent(v); p; p = p->tail) {
        int * deg = G_look(degree, p->head);
        bool * cell = G_adjSet(adjSet, G_NodeCount(graph), G_NodeKey(p->head), G_NodeKey(u));
        if (!precolored(p->head) && *deg >= K && !(*cell)) {
            return FALSE;
        }
    }
    return TRUE;
}

static bool conservative(G_nodeList nodes)
{
    int k = 0;
    for (G_nodeList n = nodes; n; n = n->tail) {
        int *deg = G_look(degree, n->head);
        if (precolored(n->head) || *deg >= K) {
            ++k;
        }
    }
    return (k < K);
}

static void addWorklist(G_node u)
{
    int * deg = G_look(degree, u);
    if (!precolored(u) && !moveRelated(u) && *deg < K) {
        freezeWorklist = G_SubNodeList(freezeWorklist, G_NodeList(u, NULL));
        simplifyWorklist = G_NodeList(u, simplifyWorklist);
    }
}

static void addEdge(G_node u, G_node v)
{
    bool * cell = G_adjSet(adjSet, G_NodeCount(graph), G_NodeKey(u), G_NodeKey(v));
    if (u != v && !*cell) {
        *cell = TRUE;
        if (!precolored(u)) {
            int * deg = G_look(degree, u);
            *deg++;
            G_addEdge(u, v);
        }
        if (!precolored(v)) {
            int * deg = G_look(degree, v);
            *deg++;
            G_addEdge(v, u);
        }
    }
}

static void combine(G_node u, G_node v)
{
    fprintf(out, "sim: %x\n", simplifyWorklist);
    fflush(out);
    if (G_inNodeList(v, freezeWorklist)) {
        freezeWorklist = G_SubNodeList(freezeWorklist, G_NodeList(v, NULL));
    } else {
        spillWorklist = G_SubNodeList(spillWorklist, G_NodeList(v, NULL));
    }
    coalescedNodes = G_NodeList(v, coalescedNodes);
    G_node * a = G_look(alias, v);
    *a = u;
    for (G_nodeList p = adjacent(v); p; p = p->tail) {
        addEdge(p->head, u);
        decrementDegree(p->head);
    }
    int * deg = G_look(degree, u);
    if (*deg >= K && G_inNodeList(u, freezeWorklist)) {
        fprintf(out, "u: %d\n", precolored(u));
        fprintf(out, "v: %d\n", precolored(v));
        fprintf(out, "sim: %x\n", simplifyWorklist);
        fprintf(out, "spill by combine %d %d\n", ((Temp_temp)G_nodeInfo(u))->num, ((Temp_temp)G_nodeInfo(v))->num);
        fflush(out);
        freezeWorklist = G_SubNodeList(freezeWorklist, G_NodeList(u, NULL));
        spillWorklist = G_NodeList(u, spillWorklist);
    }
}

static void coalesce()
{
    G_node u, v;
    G_node src = worklistMoves->src;
    G_node dst = worklistMoves->dst;
    if (precolored(GetAlias(dst))) {
        u = GetAlias(dst);
        v = GetAlias(src);
    } else {
        u = GetAlias(src);
        v = GetAlias(dst);
    }
    worklistMoves = worklistMoves->tail;

    bool * cell = G_adjSet(adjSet, G_NodeCount(graph), G_NodeKey(u), G_NodeKey(v));
    if (u == v) {
        coalescedMoves = Live_MoveList(src, dst, coalescedMoves);
        addWorklist(u);
    } else if (precolored(v) || *cell) {
        constrainedMoves = Live_MoveList(src, dst, constrainedMoves);
        addWorklist(u);
        addWorklist(v);
    } else if ((precolored(u) && ok(v, u)) || (!precolored(u) && conservative(G_UnionNodeList(adjacent(u), adjacent(v))))) {
        coalescedMoves = Live_MoveList(src, dst, coalescedMoves);
        combine(u, v);
        addWorklist(u);
    } else {
        activeMoves = Live_MoveList(src, dst, activeMoves);
    }
}

static void assignColors()
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
    for (G_nodeList p = G_nodes(graph); p != NULL; p = p->tail) {
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
                fprintf(out, "replace: %d -> %d\n", c->num, t->num);
                fflush(out);
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
                fprintf(out, "replace: %d -> %d\n", c->num, t->num);
                fflush(out);
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

static Temp_map generate_map()
{
    Temp_map res = Temp_empty();
    G_nodeList p = G_nodes(graph);
    for (; p != NULL; p = p->tail) {
        int * t = G_look(color, p->head);
        /*
        char * a = checked_malloc(sizeof(char) * MAXLINE);
        sprintf(a, "%s%d", reg_names[*t], Live_gtemp(p->head)->num);
        */
        Temp_enter(res, Live_gtemp(p->head), reg_names[*t]);
    }

    /* ebp */
    Temp_enter(res, F_FP(), "%ebp");

    return res;
}

struct RA_result RA_regAlloc(F_frame f, AS_instrList il) {
    out = fopen("log", "a");
    struct Live_graph live_graph;
    bool done = FALSE;
    while (!done) {
        fprintf(out, "loop\n");
        fflush(out);
        G_graph flow_graph = FG_AssemFlowGraph(il, f);
        live_graph = Live_liveness(flow_graph);
        build(live_graph);
        makeWorklist();
        while (simplifyWorklist || spillWorklist || worklistMoves || freezeWorklist) {
            if (simplifyWorklist) {
                simplify();
            } else if (worklistMoves) {
                coalesce();
            } else if (freezeWorklist) {
                freeze();
            } else if (spillWorklist) {
                selectSpill();
            }
        }
        assignColors();
        if (spillNodes) {
            rewriteProgram(f, &il);
        } else {
            done = TRUE;
        }
    }

    struct RA_result ret;
    ret.il = il;
    ret.coloring = generate_map();

    return ret;
}
