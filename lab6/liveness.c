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
    for(;list;list = list->tail){
        if(node == list->dst || node == list->src){
            li = Live_MoveList(list->src, list->dst, li);
            if(last){
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

Temp_tempList F_registers(void) {
	return Temp_TempList(F_RAX(), Temp_catList(F_calleeSave(), F_callerSave()));
}

bool inMoveList(G_node src, G_node dst, Live_moveList moves)
{
	for(; moves; moves = moves->tail) 
	    if(moves->src == src && moves->dst == dst) 
		return TRUE;

	return FALSE;
}


static G_node getOrCreateNode(G_graph g, Temp_temp temp, TAB_table temp_node_table) {
	G_node node = TAB_look(temp_node_table, temp);
	if(!node) {
		node = G_Node(g, temp);
		TAB_enter(temp_node_table, temp, node);
	}
	return node;
}

static void addEdge(G_graph ig, Temp_temp temp1, Temp_temp temp2, TAB_table temp_node_table) {
	if(temp1 == temp2) return;

	G_node a = getOrCreateNode(ig, temp1, temp_node_table);
	G_node b = getOrCreateNode(ig, temp2, temp_node_table);
	if(!G_inNodeList(a, G_adj(b))){

		if(!Temp_inList(F_registers(), temp1)) {
			G_addEdge(a, b);
		}
		if(!Temp_inList(F_registers(), temp2)) {
			G_addEdge(b, a);
		}
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

	G_table in_set_table = G_empty();
	G_table out_set_table = G_empty();
	bool has_change = TRUE;

	while(has_change) {
		has_change = FALSE;
		for(G_nodeList flownodes = G_nodes(flow); flownodes; flownodes = flownodes->tail) {
			Temp_tempList old_in_set = G_look(in_set_table, flownodes->head);
			Temp_tempList old_out_set = G_look(out_set_table, flownodes->head);
			Temp_tempList use_set = FG_use(flownodes->head);
			Temp_tempList def_set = FG_def(flownodes->head);

			Temp_tempList new_in_set = Temp_Union(use_set, Temp_Minus(old_out_set, def_set));
			Temp_tempList new_out_set = NULL;

			for(G_nodeList nodes = G_succ(flownodes->head); nodes; nodes = nodes->tail) {
				new_out_set = Temp_Union(new_out_set, G_look(in_set_table, nodes->head));
			}

			if(!Temp_Equal(old_in_set, new_in_set)) {
				has_change = TRUE;
				G_enter(in_set_table, flownodes->head, new_in_set);
			}

			if(!Temp_Equal(old_out_set, new_out_set)) {
				has_change = TRUE;
				G_enter(out_set_table, flownodes->head, new_out_set);
			}
		}
	}

	TAB_table temp_node_table = TAB_empty();
	for(Temp_tempList temps1 = F_registers(); temps1; temps1 = temps1->tail) {
		for(Temp_tempList temps2 = F_registers(); temps2; temps2 = temps2->tail) {
			addEdge(lg.graph, temps1->head, temps2->head, temp_node_table);
		}

	}

	for(G_nodeList flownodes = G_nodes(flow); flownodes; flownodes = flownodes->tail) {
		for(Temp_tempList defs = FG_def(flownodes->head); defs; defs = defs->tail) {
			getOrCreateNode(lg.graph, defs->head, temp_node_table);
		}
	}

	for(G_nodeList flownodes = G_nodes(flow); flownodes; flownodes = flownodes->tail) {
		Temp_tempList liveouts = G_look(out_set_table, flownodes->head);
		if(FG_isMove(flownodes->head)) {
			liveouts = Temp_Minus(liveouts, FG_use(flownodes->head));
			for(Temp_tempList defs = FG_def(flownodes->head); defs; defs = defs->tail) {
				for(Temp_tempList uses = FG_use(flownodes->head); uses; uses = uses->tail) {
					if(uses->head != F_FP() && defs->head != F_FP()) {
						lg.moves = Live_Union(lg.moves, Live_MoveList(getOrCreateNode(lg.graph, uses->head, temp_node_table),getOrCreateNode(lg.graph, defs->head, temp_node_table),NULL));
					}
        }
      }
		}

		for(Temp_tempList defs = FG_def(flownodes->head); defs; defs = defs->tail) {
			for(Temp_tempList outs = liveouts; outs; outs = outs->tail) {
				addEdge(lg.graph, defs->head, outs->head, temp_node_table);
			}
		}
	}

	return lg;
}

