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

Live_moveList Live_remove(G_node src, G_node dst, Live_moveList l){
    	Live_moveList last = NULL;
    	for (Live_moveList p = l; p; p = p->tail)
	{
            if(p->dst == dst && p->src == src)
	    {
            	if(last)
		{
                    last->tail = p->tail;
                    break;
            	}
            	else
		{
                    l = l->tail;
                    break;
            	}
            }
            last = p;
    	}
    	return l;
}

Live_moveList RMrelatedMovs(G_node node, Live_moveList list){
    	Live_moveList li = NULL;
    	Live_moveList last = NULL;
    	for(;list;list = list->tail)
	{
            if(node == list->dst || node == list->src)
	    {
            	li = Live_MoveList(list->src, list->dst, li);
            	if(last)
		{
                    last->tail = list->tail;
                    list = last;
        	}
            }
            last = list;
    	}
    	return li;
}

Temp_temp Live_gtemp(G_node n) {
	//your code here.
	return G_nodeInfo(n);
}

bool inMoveList(G_node src, G_node dst, Live_moveList moves)
{
	for(; moves; moves = moves->tail) 
	    if(moves->src == src && moves->dst == dst) 
		return TRUE;

	return FALSE;
}


G_node getNode(G_graph g, Temp_temp temp, TAB_table tempNode) {
	G_node node = TAB_look(tempNode, temp);
	if(!node) 
	{
	    node = G_Node(g, temp);
	    TAB_enter(tempNode, temp, node);
	}
	return node;
}

void addEdge(G_graph g, Temp_temp temp1, Temp_temp temp2, TAB_table tempNode) {
	if(temp1 == temp2) return;

	G_node a = getNode(g, temp1, tempNode);
	G_node b = getNode(g, temp2, tempNode);
	if(!G_inNodeList(a, G_adj(b)))
	{
	    G_addEdge(a, b);
	    G_addEdge(b, a);
	}
}

Live_moveList Live_Union(Live_moveList moves_a, Live_moveList moves_b) {
	Live_moveList res = moves_a;
	for(Live_moveList moves2 = moves_b; moves2; moves2 = moves2->tail) 
	    if(!inMoveList(moves2->src, moves2->dst, moves_a)) 
		res = Live_MoveList(moves2->src, moves2->dst, res);

	return res;
}

struct Live_graph Live_liveness(G_graph flow) {
	//your code here.
	struct Live_graph lg;
	lg.graph = G_Graph();
	lg.moves = NULL;

	G_table inSet = G_empty();
	G_table outSet = G_empty();
	bool done = FALSE;

	while(!done) 
	{
	    done = TRUE;
	    for(G_nodeList flownodes = G_nodes(flow); flownodes; flownodes = flownodes->tail) 
	    {
		Temp_tempList in_ = G_look(inSet, flownodes->head);
		Temp_tempList out_ = G_look(outSet, flownodes->head);
		Temp_tempList use = FG_use(flownodes->head);
		Temp_tempList def = FG_def(flownodes->head);

		Temp_tempList in = Temp_Union(use, Temp_Minus(out_, def));
		Temp_tempList out = NULL;

		for(G_nodeList nodes = G_succ(flownodes->head); nodes; nodes = nodes->tail) 
		    out = Temp_Union(G_look(inSet, nodes->head), out);
			
		if(!Temp_Equal(in_, in)) 
		{
		    done = FALSE;
		    G_enter(inSet, flownodes->head, in);
		}

		if(!Temp_Equal(out_, out)) 
		{
		    done = FALSE;
		    G_enter(outSet, flownodes->head, out);
		}
	    }
	}

	TAB_table tempNode = TAB_empty();

	for(G_nodeList flownodes = G_nodes(flow); flownodes; flownodes = flownodes->tail) 
	{
	    Temp_tempList liveouts = G_look(outSet, flownodes->head);
	    if(FG_isMove(flownodes->head)) 
	    {
		liveouts = Temp_Minus(liveouts, FG_use(flownodes->head));
		for(Temp_tempList defs = FG_def(flownodes->head); defs; defs = defs->tail) 
		    for(Temp_tempList uses = FG_use(flownodes->head); uses; uses = uses->tail) 
			lg.moves = Live_MoveList(getNode(lg.graph,uses->head,tempNode),getNode(lg.graph,defs->head,tempNode),lg.moves);

	    }

	    for(Temp_tempList defs = FG_def(flownodes->head); defs; defs = defs->tail)
		for(Temp_tempList outs = liveouts; outs; outs = outs->tail)
		    addEdge(lg.graph, defs->head, outs->head,tempNode);
	}

	return lg;
}

