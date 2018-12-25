#ifndef LIVENESS_H
#define LIVENESS_H

typedef struct Live_moveList_ *Live_moveList;
struct Live_moveList_ {
	G_node src, dst;
	Live_moveList tail;
};

Live_moveList Live_MoveList(G_node src, G_node dst, Live_moveList tail);

struct Live_graph {
	G_graph graph;
	Live_moveList moves;
};
Temp_temp Live_gtemp(G_node n);

struct Live_graph Live_liveness(G_graph flow);

bool inMoveList(G_node node, Live_moveList list);
Live_moveList RMrelatedMovs(G_node node, Live_moveList list);
Live_moveList CatMovList(Live_moveList A, Live_moveList B);

#endif
