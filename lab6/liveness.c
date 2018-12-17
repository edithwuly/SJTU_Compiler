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

static void enterLiveMap(G_table t, G_node flowNode, Temp_tempList temps) {
	G_enter(t, flowNode, temps);
}

static Temp_tempList lookupLiveMap(G_table t, G_node flownode) {
	return (Temp_tempList) G_look(t, flownode);
}

Temp_temp Live_gtemp(G_node n) {
	//your code here.
	
	return G_nodeInfo(n);
}

bool findInTempList(Temp_tempList tempList, Temp_temp temp) {
    	for (; tempList; tempList = tempList->tail)
            if (tempList->head == temp)
            	return TRUE;

    	return FALSE;
}

bool findInMoveList(Live_moveList moveList, G_node src, G_node dst) {
    	for (; moveList; moveList = moveList->tail)
	    if (moveList->src == src && moveList->dst == dst)
		return TRUE;

	return FALSE;
}

Temp_tempList unionTempList(Temp_tempList tempList1, Temp_tempList tempList2) {
	Temp_tempList res = NULL;
	for(; tempList1; tempList1 = tempList1->tail) 
	    res = Temp_TempList(tempList1->head, res);

	for(; tempList2; tempList2 = tempList2->tail) 
	    if (!findInTempList(res, tempList2->head))
		res = Temp_TempList(tempList2->head, res);

	return res;
}

Temp_tempList diffTempList(Temp_tempList tempList1, Temp_tempList tempList2) {
	Temp_tempList res = NULL;
	for(; tempList1; tempList1 = tempList1->tail) 
	    if (!findInTempList(tempList2, tempList1->head))
		res = Temp_TempList(tempList1->head, res);

	return res;
}

bool equalTempList(Temp_tempList tempList1, Temp_tempList tempList2) {
	for(Temp_tempList temp = tempList1; temp; temp = temp->tail) 
	    if (!findInTempList(tempList2, temp->head))
		return FALSE;

	for(Temp_tempList temp = tempList2; temp; temp = temp->tail) 
	    if (!findInTempList(tempList1, temp->head))
		return FALSE;

	return TRUE;
}

struct Live_graph Live_liveness(G_graph flow) {
	//your code here.
	struct Live_graph lg;
	
	bool done = FALSE;
    	G_table livein = G_empty(), liveout = G_empty();

	while(!done) 
	{
	    done = TRUE;
	    for(G_nodeList flownodes = G_nodes(flow); flownodes; flownodes = flownodes->tail) 
	    {
		Temp_tempList in_ = lookupLiveMap(livein, flownodes->head), out_ = lookupLiveMap(liveout, flownodes->head);
		Temp_tempList use = FG_use(flownodes->head), def = FG_def(flownodes->head);

		Temp_tempList in = unionTempList(use, diffTempList(out_, def));
		Temp_tempList out = NULL;

		for(G_nodeList nodes = G_succ(flownodes->head); nodes; nodes = nodes->tail)
		    out = unionTempList(out, lookupLiveMap(livein, nodes->head));

		if(!equalTempList(in_, in)) 
		{
		    done = FALSE;
		    enterLiveMap(livein, flownodes->head, in);
		}

		if(!equalTempList(out_, out)) 
		{
		    done = FALSE;
		    enterLiveMap(liveout, flownodes->head, out);
		}
	    }
	}

	lg.moves = NULL;
	lg.graph = G_Graph();

	TAB_table tempTab= TAB_empty();
	Temp_tempList hardRegs = Temp_TempList(F_RAX(),Temp_TempList(F_RBX(),Temp_TempList(F_RCX(),Temp_TempList(F_RDX(),Temp_TempList(F_RSI(),Temp_TempList(F_RDI(), Temp_TempList(F_R8(),Temp_TempList(F_R9(),Temp_TempList(F_R10(),Temp_TempList(F_R11(),Temp_TempList(F_R12(),Temp_TempList(F_R13(),Temp_TempList(F_R14(),Temp_TempList(F_R15(),NULL))))))))))))));

	for (Temp_tempList temps = hardRegs; temps; temps = temps->tail) 
	{
	    G_node tempNode = G_Node(lg.graph, temps->head);
	    TAB_enter(tempTab, temps->head, tempNode);
	}

	for (Temp_tempList temps = hardRegs; temps; temps = temps->tail) 
	{
	    for (Temp_tempList next = temps->tail; next; next = next->tail) 
	    {
		G_node a = TAB_look(tempTab, temps->head);
		G_node b = TAB_look(tempTab, next->head);
		G_addEdge(a, b);
		G_addEdge(b, a);
	    }
	}

	for(G_nodeList flownodes = G_nodes(flow); flownodes; flownodes = flownodes->tail)
	{
	    for(Temp_tempList def = FG_def(flownodes->head); def; def = def->tail)
		if (!TAB_look(tempTab, def->head)) 
		    TAB_enter(tempTab, def->head, G_Node(lg.graph, def->head));

	    for(Temp_tempList out = lookupLiveMap(liveout, flownodes->head); out; out = out->tail)
		if (!TAB_look(tempTab, out->head)) 
		    TAB_enter(tempTab, out->head, G_Node(lg.graph, out->head));
	}

	for (G_nodeList flownodes = G_nodes(flow); flownodes; flownodes = flownodes->tail) 
	{
	    if (!FG_isMove(flownodes->head)) 
		for (Temp_tempList def = FG_def(flownodes->head); def; def = def->tail) 
		    if (def->head != F_FP()) 
		    {
			G_node a = TAB_look(tempTab, def->head);
			for (Temp_tempList out = lookupLiveMap(liveout, flownodes->head); out; out = out->tail) 
			    if (out->head != F_FP() && out->head != def->head) 
			    {
				G_node b = TAB_look(tempTab, out->head);
				if (!G_inNodeList(a, G_adj(b))) 
				{
				    G_addEdge(a, b);
				    G_addEdge(b, a);
				}
			    }
		    } 
	    else 
		for (Temp_tempList def = FG_def(flownodes->head); def; def = def->tail) 
		    if (def->head != F_FP()) 
		    {
			G_node a = TAB_look(tempTab, def->head);
			for (Temp_tempList out = lookupLiveMap(liveout, flownodes->head); out; out = out->tail) 
			    if (out->head != F_FP() && out->head != def->head) 
			    {
				G_node b = TAB_look(tempTab, out->head);			
				if (!G_inNodeList(a, G_adj(b)) && !findInTempList(FG_use(flownodes->head), out->head)) 
				{
				    G_addEdge(a, b);
				    G_addEdge(b, a);
				}
			    }
			for (Temp_tempList use = FG_use(flownodes->head); use; use = use->tail) 
			    if (use->head != F_FP() && use->head != def->head)
			    {
				G_node b = TAB_look(tempTab, use->head);

			    	if (!findInMoveList(lg.moves, b, a))
				    lg.moves = Live_MoveList(b, a, lg.moves);
			    }
		    }
	}

	return lg;
}


