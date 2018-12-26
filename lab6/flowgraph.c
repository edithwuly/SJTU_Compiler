#include <stdio.h>
#include <string.h>
#include <stdlib.h>

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
	//your code here.
	AS_instr ins = G_nodeInfo(n);
	switch(ins->kind)
	{
	    case I_OPER:
		return ins->u.OPER.dst;
	    case I_LABEL:
		return NULL;
	    case I_MOVE:
		return ins->u.MOVE.dst;
	}
}

Temp_tempList FG_use(G_node n) {
	//your code here
	AS_instr ins = G_nodeInfo(n);
	switch(ins->kind)
	{
	    case I_OPER:
		return ins->u.OPER.src;
	    case I_LABEL:
		return NULL;
	    case I_MOVE:
		return ins->u.MOVE.src;
	}
}

bool FG_isMove(G_node n) {
	//your code here.
	AS_instr ins = G_nodeInfo(n);
	if (strstr(ins->u.MOVE.assem,"movq `s0, `d0"))
	    return TRUE;

	return FALSE;
}

G_graph FG_AssemFlowGraph(AS_instrList il) {
	//your code here.
	G_graph g = G_Graph();
	G_node prev = NULL;
	AS_instrList head = il;
	
	struct TAB_table_ *labelMap = TAB_empty();
	
	for (; il; il = il->tail) 
	{
	    AS_instr instr = il->head;
	    G_node n = G_Node(g, instr);
	    if (prev) 
		G_addEdge(prev, n);
		
            if (instr->kind == I_OPER && strstr(instr->u.OPER.assem, "jmp"))
            	prev = NULL;
       	    else 
            	prev = n;
        
	    if (instr->kind == I_LABEL) 
		TAB_enter(labelMap, instr->u.LABEL.label, n);
		
	}

	for (G_nodeList nodes = G_nodes(g); nodes; nodes = nodes->tail) 
	{
            G_node n = nodes->head;
            AS_instr instr = (AS_instr) G_nodeInfo(n);
	    if (instr->kind == I_OPER && instr->u.OPER.jumps) 
		for (Temp_labelList labels = instr->u.OPER.jumps->labels; labels; labels = labels->tail) 
		{
		    Temp_label label = labels->head;
		    G_node dest = (G_node) TAB_look(labelMap, label);
		    G_addEdge(n, dest);
		}
	}
	return g;
}
