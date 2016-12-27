typedef struct Live_moveList_ *Live_moveList;
struct Live_moveList_ {
	G_node src, dst;
	Live_moveList tail;
};

bool Live_inMoveList(G_node src, G_node dst, Live_moveList l);
Live_moveList Live_UnionMoveList(Live_moveList l, Live_moveList r);
Live_moveList Live_SubMoveList(Live_moveList l, Live_moveList r);
Live_moveList Live_MoveList(G_node src, G_node dst, Live_moveList tail);

struct Live_graph {
        bool *adj;
	G_graph graph;
	Live_moveList moves;
};
Temp_temp Live_gtemp(G_node n);

struct Live_graph Live_liveness(G_graph flow);

Temp_tempList MachineRegs();
