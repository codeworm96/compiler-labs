#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "flowgraph.h"
#include "liveness.h"
#include "table.h"

static int sqr(int x)
{
    return x * x;
}

/* machine registers */
static Temp_tempList machine_regs = NULL;
Temp_tempList MachineRegs()
{
    if (!machine_regs) {
        machine_regs = Temp_TempList(F_eax(),
                       Temp_TempList(F_ebx(),
                       Temp_TempList(F_ecx(),
                       Temp_TempList(F_edx(),
                       Temp_TempList(F_esi(),
                       Temp_TempList(F_edi(), NULL))))));
    }
    return machine_regs;
}

bool Live_inMoveList(G_node src, G_node dst, Live_moveList l)
{
    for (Live_moveList p = l; p; p = p->tail) {
        if (p->src == src && p->dst == dst) {
            return TRUE;
        }
    }
    return FALSE;
}

Live_moveList Live_UnionMoveList(Live_moveList l, Live_moveList r)
{
    Live_moveList res = r;
    for (Live_moveList p = l; p; p = p->tail) {
        if (!Live_inMoveList(p->src, p->dst, r)) {
            res = Live_MoveList(p->src, p->dst, res);
        }
    }
    return res;
}

Live_moveList Live_SubMoveList(Live_moveList l, Live_moveList r)
{
    Live_moveList res = NULL;
    for (Live_moveList p = l; p; p = p->tail) {
        if (!Live_inMoveList(p->src, p->dst, r)) {
            res = Live_MoveList(p->src, p->dst, res);
        }
    }
    return res;
}

Live_moveList Live_MoveList(G_node src, G_node dst, Live_moveList tail) {
    if (!Live_inMoveList(src, dst, tail)) {
	Live_moveList lm = (Live_moveList) checked_malloc(sizeof(*lm));
	lm->src = src;
	lm->dst = dst;
	lm->tail = tail;
	return lm;
    } else {
        return tail;
    }
}


Temp_temp Live_gtemp(G_node n) {
    return G_nodeInfo(n);
}

static G_node get_node(G_graph g, Temp_temp temp, TAB_table temp2node)
{
    G_node res = TAB_look(temp2node, temp);
    if (!res) {
        res = G_Node(g, temp);
        TAB_enter(temp2node, temp, res);
    }
    return res;
}

static void link(struct Live_graph *g, Temp_temp temp_a, Temp_temp temp_b, TAB_table temp2node)
{
    if (temp_a == temp_b || temp_a == F_FP() || temp_b == F_FP()) return; /* exclude ebp */

    G_node a = get_node(g->graph, temp_a, temp2node);
    G_node b = get_node(g->graph, temp_b, temp2node);
    bool * cell = G_adjSet(g->adj, G_NodeCount(g->graph), G_NodeKey(a), G_NodeKey(b));
    if (!*cell) {
        printf("link %d-%d\n", temp_a->num, temp_b->num);

        *cell = TRUE;
        if (!Temp_inTempList(temp_a, MachineRegs()))
            G_addEdge(a, b);
        if (!Temp_inTempList(temp_b, MachineRegs()))
            G_addEdge(b, a);
    }
}

struct Live_graph Live_liveness(G_graph flow) {
    struct Live_graph res;
    G_table in = G_empty();
    G_table out = G_empty();
    TAB_table temp2node = TAB_empty();
    G_nodeList p = G_nodes(flow);
    bool changed = TRUE;
    for (; p != NULL; p = p->tail) {
        G_enter(in, p->head, checked_malloc(sizeof(Temp_tempList*)));
        G_enter(out, p->head, checked_malloc(sizeof(Temp_tempList*)));
    }
    while (changed) {
        changed = FALSE;
        p = G_nodes(flow);
        for (; p != NULL; p = p->tail) {
            Temp_tempList inp0 = *(Temp_tempList*)G_look(in, p->head);
            Temp_tempList outp0 = *(Temp_tempList*)G_look(out, p->head);
            Temp_tempList inp, outp;
            G_nodeList cur = G_succ(p->head);
            outp = NULL;
            for (; cur != NULL; cur = cur->tail) {
                Temp_tempList ins = *(Temp_tempList*)G_look(in, cur->head);
                outp = Temp_UnionTempList(outp, ins); 
            }
            inp = Temp_UnionTempList(FG_use(p->head), Temp_SubTempList(outp, FG_def(p->head)));
            if (!Temp_TempListEqual(inp, inp0)) {
                changed = TRUE;
                *(Temp_tempList*)G_look(in, p->head) = inp;
            }
            if (!Temp_TempListEqual(outp, outp0)) {
                changed = TRUE;
                *(Temp_tempList*)G_look(out, p->head) = outp;
            }
        }
    }
    res.moves = NULL; // TODO
    res.graph = G_Graph();


    /* create nodes */
    for (Temp_tempList m = MachineRegs(); m; m = m->tail) {
        get_node(res.graph, m->head, temp2node);
    }
    for (p = G_nodes(flow); p != NULL; p = p->tail) {
        for (Temp_tempList def = FG_def(p->head); def; def = def->tail) {
            if (def->head != F_FP()) {
                get_node(res.graph, def->head, temp2node);
            }
        }
    }
    res.adj = checked_malloc(sqr(G_NodeCount(res.graph)) * sizeof(bool));

    /* link nodes */
    for (Temp_tempList m1 = MachineRegs(); m1; m1 = m1->tail) {
        for (Temp_tempList m2 = MachineRegs(); m2; m2 = m2->tail) {
            if (m1->head != m2->head) {
                link(&res, m1->head, m2->head, temp2node);
            }
        }
    }

    for (p = G_nodes(flow); p != NULL; p = p->tail) {
        Temp_tempList outp = *(Temp_tempList*)G_look(out, p->head), op;
        AS_instr inst = G_nodeInfo(p->head);
        if (inst->kind == I_MOVE) {
            printf("move\n");
            outp = Temp_SubTempList(outp, FG_use(p->head));
            for (Temp_tempList def = FG_def(p->head); def; def = def->tail) {
                for (Temp_tempList use = FG_use(p->head); use; use = use->tail) {
                    res.moves = Live_MoveList(get_node(res.graph, use->head, temp2node),
                            get_node(res.graph, def->head, temp2node),
                            res.moves);
                }
            }
        }
        /*
        AS_instr inst = G_nodeInfo(p->head);
        printf("%s:", inst->u.MOVE.assem);
        Temp_DumpTempList(outp);
        printf("\n");
        */

        for (Temp_tempList def = FG_def(p->head); def; def = def->tail) {
            for (op = outp; op; op = op->tail) {
                link(&res, def->head, op->head, temp2node);
            }
        }
    }

    return res;
}

