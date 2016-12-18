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
#include "errormsg.h"
#include "table.h"

Temp_tempList FG_def(G_node n) {
    AS_instr inst = G_nodeInfo(n);
    switch (inst->kind) {
        case I_OPER:
            return inst->u.OPER.dst;
        case I_LABEL:
            return NULL;
        case I_MOVE:
            return inst->u.MOVE.dst;
        default:
            assert(0);
    }
    return NULL;
}

Temp_tempList FG_use(G_node n) {
    AS_instr inst = G_nodeInfo(n);
    switch (inst->kind) {
        case I_OPER:
            return inst->u.OPER.src;
        case I_LABEL:
            return NULL;
        case I_MOVE:
            return inst->u.MOVE.src;
        default:
            assert(0);
    }
    return NULL;
}

bool FG_isMove(G_node n) {
    AS_instr inst = G_nodeInfo(n);
    return inst->kind == I_MOVE;
}

G_graph FG_AssemFlowGraph(AS_instrList il, F_frame f) {
    TAB_table label2node = TAB_empty();
    TAB_table instr2node = TAB_empty();
    G_graph res = G_Graph();
    G_node last = NULL;
    for (AS_instrList cur = il; cur != NULL; cur = cur->tail) {
        G_node node = G_Node(res, cur->head);
        TAB_enter(instr2node, cur->head, node);
        if (last) {
            G_addEdge(last, node);
        }
        last = node;
        if (cur->head->kind == I_LABEL) {
            TAB_enter(label2node, cur->head->u.LABEL.label, node);
        }
    }
    for (AS_instrList cur = il; cur != NULL; cur = cur->tail) {
        if (cur->head->kind == I_OPER) {
            G_node node = TAB_look(instr2node, cur->head);
            Temp_labelList ll = cur->head->u.OPER.jumps->labels;
            for (; ll != NULL; ll = ll->tail) {
                G_addEdge(node, TAB_look(label2node, ll->head));
            }
        }
    }
    return res;
}
