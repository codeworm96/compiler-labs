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

Live_moveList Live_MoveList(G_node src, G_node dst, Live_moveList tail) {
	Live_moveList lm = (Live_moveList) checked_malloc(sizeof(*lm));
	lm->src = src;
	lm->dst = dst;
	lm->tail = tail;
	return lm;
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

static void link(G_graph g, Temp_temp temp_a, Temp_temp temp_b, TAB_table temp2node)
{
    if (temp_a == temp_b || temp_a == F_FP() || temp_b == F_FP()) return; /* exclude ebp */

    G_node a = get_node(g, temp_a, temp2node);
    G_node b = get_node(g, temp_b, temp2node);
    if (!G_inNodeList(a, G_adj(b))) {
        printf("link %d-%d\n", temp_a->num, temp_b->num);
        G_addEdge(a, b);
        G_addEdge(b, a);
    }
}

struct Live_graph Live_liveness(G_graph flow) {
    Temp_tempList machine_regs;
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

    /* machine registers */
    machine_regs = Temp_TempList(F_eax(),
                   Temp_TempList(F_ebx(),
                   Temp_TempList(F_ecx(),
                   Temp_TempList(F_edx(),
                   Temp_TempList(F_esi(),
                   Temp_TempList(F_edi(), NULL))))));
    for (Temp_tempList m1 = machine_regs; m1; m1 = m1->tail) {
        for (Temp_tempList m2 = machine_regs; m2; m2 = m2->tail) {
            if (m1->head != m2->head) {
                link(res.graph, m1->head, m2->head, temp2node);
            }
        }
    }

    p = G_nodes(flow);
    for (; p != NULL; p = p->tail) {
        Temp_tempList outp = *(Temp_tempList*)G_look(out, p->head), op;
        Temp_tempList def = FG_def(p->head);
        AS_instr inst = G_nodeInfo(p->head);
        printf("%s:", inst->u.MOVE.assem);
        Temp_DumpTempList(outp);
        printf("\n");

        for (; def; def = def->tail) {
            if (def->head != F_FP()) {
                get_node(res.graph, def->head, temp2node); /* define a reg */
                for (op = outp; op; op = op->tail) {
                    link(res.graph, def->head, op->head, temp2node);
                }
            }
        }
    }

    return res;
}


