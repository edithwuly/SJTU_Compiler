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
	AS_instr instr = G_nodeInfo(n);
	switch(instr->kind) 
	{
	    case I_OPER:
		return instr->u.OPER.dst;
	    case I_LABEL:
		return NULL;
	    case I_MOVE:
		return instr->u.MOVE.dst;
	    default:
		assert(0);
	}
}

Temp_tempList FG_use(G_node n) {
	//your code here.
	AS_instr instr = G_nodeInfo(n);
	switch(instr->kind) 
	{
	    case I_OPER:
		return instr->u.OPER.src;
	    case I_LABEL:
		return NULL;
	    case I_MOVE:
		return instr->u.MOVE.src;
	    default:
		assert(0);
	}
}

bool FG_isMove(G_node n) {
	//your code here.
	AS_instr instr = G_nodeInfo(n);
	return instr->kind == I_MOVE;
}

G_graph FG_AssemFlowGraph(AS_instrList il, F_frame f) {
	//your code here.
	G_graph g = G_Graph();
	G_node node1 = NULL, node2 = NULL;
	TAB_table label_node_table = TAB_empty();

	AS_instr last_inst = NULL;
	for(AS_instrList instrList = il; instrList; instrList = instrList->tail) 
	{
	    node2 = G_Node(g, instrList->head);

	    if(node1 && !(last_inst->kind == I_OPER && strncmp("jmp", last_inst->u.OPER.assem, 3) == 0))
		G_addEdge(node1, node2);

	    if(instrList->head->kind == I_LABEL)
		TAB_enter(label_node_table, instrList->head->u.LABEL.label, node2);

	    node1 = node2;
	    last_inst = instrList->head;
	}

	for(G_nodeList nodes = G_nodes(g); nodes; nodes = nodes->tail) 
	{
	    AS_instr inst = G_nodeInfo(nodes->head);
	    if(inst->kind == I_OPER && inst->u.OPER.jumps) 
		for(Temp_labelList labelList = inst->u.OPER.jumps->labels; labelList; labelList = labelList->tail) 
		    G_addEdge(nodes->head, TAB_look(label_node_table, labelList->head));
	}

	return g;
}
