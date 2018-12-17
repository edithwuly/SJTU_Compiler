#include <stdio.h>
#include <string.h>

#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "liveness.h"
#include "color.h"
#include "table.h"

#define K 14

static char *hard_regs[15] = {"none", "%rax", "%rbx", "%rcx", "%rdx", "%rsi", "%rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"};

G_nodeList simplifyWorklist;
G_nodeList freezeWorklist;
G_nodeList spillWorklist;
G_nodeList spilledNodes;
G_nodeList coalescedNodes;
G_nodeList coloredNodes;
G_nodeList selectStack;

Live_moveList worklistMoves;
Live_moveList coalescedMoves;
Live_moveList constrainedMoves;
Live_moveList frozenMoves;
Live_moveList activeMoves;

G_table degree;
G_table moveList;
G_table alias;
G_table color;

bool isPrecolored(G_node node) {
	return *(int *)G_look(color, node);
}

void build(struct Live_graph lg, Temp_tempList regs)
{
	simplifyWorklist = NULL;
	freezeWorklist = NULL;
	spillWorklist = NULL;
	spilledNodes = NULL;
	coalescedNodes = NULL;
	selectStack = NULL;

	coalescedMoves = NULL;
	constrainedMoves = NULL;
	frozenMoves = NULL;
	worklistMoves = lg.moves;
	activeMoves = NULL;

    	degree = G_empty();
    	moveList = G_empty();
    	alias = G_empty();
    	color = G_empty();
	for(G_nodeList nodes = G_nodes(lg.graph); nodes; nodes = nodes->tail) 
	{
	    int *nodeDegree = checked_malloc(sizeof(int));
	    *nodeDegree = 0;
	    for (G_nodeList cur = G_succ(nodes->head); cur; cur = cur->tail)
		(*nodeDegree)++;

	    G_enter(degree, nodes->head, nodeDegree);

	    int *nodeColor = checked_malloc(sizeof(int));
	    Temp_temp temp = Live_gtemp(nodes->head);
	    if (temp == F_RAX())
		*nodeColor = 1;
	    else if (temp == F_RBX()) 
		*nodeColor = 2;
	    else if (temp == F_RCX())
		*nodeColor = 3;
	    else if (temp == F_RDX())
		*nodeColor = 4;
	    else if (temp == F_RSI())
		*nodeColor = 5;
	    else if (temp == F_RDI())
		*nodeColor = 6;
	    else if (temp == F_R8())
		*nodeColor = 7;
	    else if (temp == F_R9())
		*nodeColor = 8;
	    else if (temp == F_R10())
		*nodeColor = 9;
	    else if (temp == F_R11())
		*nodeColor = 10;
	    else if (temp == F_R12())
		*nodeColor = 11;
	    else if (temp == F_R13())
		*nodeColor = 12;
	    else if (temp == F_R14())
		*nodeColor = 13;
	    else if (temp == F_R15())
		*nodeColor = 14;
	    else 
		*nodeColor = 0;

	    G_enter(color, nodes->head, nodeColor);

	    G_node *nodeAlias = checked_malloc(sizeof(G_node));
	    *nodeAlias = nodes->head;
	    G_enter(alias, nodes->head, nodeAlias);
	}
}

void AddEdge(G_node u, G_node v) {
	if (!G_inNodeList(u, G_adj(v)) && u != v) 
	{
	    if (!isPrecolored(u)) 
	    {
		(*(int *)G_look(degree, u))++;
		G_addEdge(u, v);
	    }
	    if (!isPrecolored(v)) 
	    {
		(*(int *)G_look(degree, v))++;
		G_addEdge(v, u);
	    }
	}
}

Live_moveList NodeMoves(G_node n) {
	Live_moveList moveList = NULL;
	return moveList;
}

bool MoveRelated(G_node n) {
	return NodeMoves(n) != NULL;
}

void MakeWorklist(struct Live_graph lg) {
	for (G_nodeList nodes = G_nodes(lg.graph); nodes; nodes = nodes->tail) 
	{
	    if (*((int *)G_look(color, nodes->head)) == 0) 
	    {
		if (*((int *)G_look(degree, nodes->head)) >= K)
			spillWorklist = G_NodeList(nodes->head, spillWorklist);
		else if (MoveRelated(nodes->head))
			freezeWorklist = G_NodeList(nodes->head, freezeWorklist);
		else
			simplifyWorklist = G_NodeList(nodes->head, simplifyWorklist);
	    }
	}
}

struct COL_result COL_color(G_graph ig, Temp_map initial, Temp_tempList regs) {
	//your code here.
	struct Live_graph live_graph = Live_liveness(ig);
	build(live_graph, regs);

	struct COL_result ret;
	return ret;
}
