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
#include "regalloc.h"
#include "table.h"
#include "flowgraph.h"

const int REG_NUM = 16;

static G_nodeList precolored;
static G_nodeList coloredNode;
static G_nodeList spilledNode;
static G_nodeList coalescedNode;
static G_nodeList selectStack;
static G_nodeList spillWorkList;
static G_nodeList freezeWorkList;
static G_nodeList simplifyWorkList;

static Live_moveList worklistMoves;
static Live_moveList coalescedMoves;
static Live_moveList frozenMoves;
static Live_moveList constrainedMoves;
static Live_moveList activeMoves;

static G_table degree;
static G_table alias;
static Live_moveList moveList;
static Temp_map color;

static Live_moveList NodeMoves(G_node n){
	Live_moveList l = NULL;
	for (Live_moveList rel = RMrelatedMovs(n, moveList); rel; rel=rel->tail)
	    if((rel->src != n && inMoveList(rel->src, rel->dst, activeMoves)) || (rel->dst != n && inMoveList(rel->src, rel->dst, worklistMoves)))	
		l = Live_MoveList(rel->src, rel->dst, l);
	return l;
}

static bool MoveRelated(G_node n){
	return NodeMoves(n) != NULL;
}

static G_nodeList Adjacent(G_node node){
	return G_minusNodeList(G_adj(node), G_unionNodeList(selectStack, coalescedNode));
}

static void EnableMoves(G_nodeList nodes){
	for(;nodes;nodes=nodes->tail)
	{
	    G_node n = nodes->head;
	    for (Live_moveList rel = NodeMoves(n); rel; rel=rel->tail)
	    {
	    	if((rel->src != n && inMoveList(rel->src, rel->dst, activeMoves)) || (rel->dst != n && inMoveList(rel->src, rel->dst, worklistMoves)))
	    	{
		    activeMoves = Live_remove(rel->src, rel->dst, activeMoves);	
		    worklistMoves = Live_MoveList(rel->src, rel->dst, worklistMoves);
	    	}
	    }
	}	
}

static void DecrementDegree(G_node m){
	int *d = G_look(degree, m);
	(*d)--;
	if(*d + 1 == REG_NUM)
	{
	    EnableMoves(G_NodeList(m, Adjacent(m)));
	    spillWorkList = G_removeNode(m, spillWorkList);
	    if(MoveRelated(m))
		freezeWorkList=G_NodeList(m, freezeWorkList);
		
	    else
		simplifyWorkList=G_NodeList(m, simplifyWorkList);
		
	}
}
static G_node GetAlias(G_node node){
	if(G_inNodeList(node, coalescedNode))
	    return GetAlias(G_look(alias, node));
	
	else
	    return node;
	
}
static void AddWorkList(G_node node){
	if(!G_inNodeList(node, precolored) && !MoveRelated(node) && *(int *)G_look(degree, node) < REG_NUM)
	{
	    freezeWorkList = G_removeNode(node, freezeWorkList);
	    simplifyWorkList=G_NodeList(node, simplifyWorkList);
	}
}
static bool OK(G_node t, G_node r){
	for(G_nodeList nl=Adjacent(t);nl;nl=nl->tail)
	{
	    G_node node = nl->head;
	    if (!((*(int *)G_look(degree, node) < REG_NUM || G_inNodeList(node,precolored) || G_inNodeList(node, G_adj(r)))))
		return FALSE;
	}

	return TRUE;
}

static bool Conservative(G_nodeList nodes){
	int k = 0;
	for(;nodes;nodes=nodes->tail)
	    if(*(int *)G_look(degree, nodes->head) >= REG_NUM) 
		k++;
	
	return k < REG_NUM;
}

static void Combine(G_node u, G_node v){
	if(G_inNodeList(v, freezeWorkList))
	    freezeWorkList = G_removeNode(v, freezeWorkList);
	else
	    spillWorkList = G_removeNode(v, spillWorkList);

	coalescedNode = G_NodeList(v, coalescedNode);
	G_enter(alias, v, u);
	EnableMoves(G_NodeList(v, NULL));

	for(G_nodeList nl=Adjacent(v);nl;nl=nl->tail)
	{
	    G_node t = nl->head;
	    G_addEdge(t, u);		
	    DecrementDegree(t);
	}
	if(*(int *)G_look(degree, u) >= REG_NUM && G_inNodeList(u, freezeWorkList))
	{
	    freezeWorkList = G_removeNode(u, freezeWorkList);
	    spillWorkList = G_NodeList(u, spillWorkList);
	}	
}

static void Coalesce(){
	G_node x = GetAlias(worklistMoves->src);
	G_node y = GetAlias(worklistMoves->dst);
	worklistMoves = worklistMoves->tail;

	G_node u,v;
	if (G_inNodeList(x, precolored))
	{
	    u = x;
	    v = y;
	}
	else
	{
	    u = y;
	    v = x;
	}
	
	if(u == v)
	{
	    coalescedMoves = Live_MoveList(x, y, coalescedMoves);
	    AddWorkList(u);
	}
	else if(G_inNodeList(v, precolored) || G_inNodeList(u, G_adj(v)))
	{
	    constrainedMoves = Live_MoveList(x, y, constrainedMoves);
	    AddWorkList(u);
	    AddWorkList(v);
	}
	else if(G_inNodeList(u, precolored) && OK(u,v) || !G_inNodeList(u, precolored) && Conservative(G_unionNodeList(Adjacent(u),Adjacent(v))))
	{
	    coalescedMoves = Live_MoveList(x, y, coalescedMoves);
	    Combine(u, v);
	    AddWorkList(u);
	}
	else
	    activeMoves = Live_MoveList(x, y, activeMoves);
}

static void MakeWorkList(G_graph cfgraph){
	G_nodeList nl = G_nodes(cfgraph);
	for(;nl;nl=nl->tail)
	{
	    G_node node = nl->head;
	    int *d = checked_malloc(sizeof(int));
	    *d = G_degree(node);

	    if(Temp_look(F_tempMap, Live_gtemp(node)))
	    {
		*d = 9999;
		precolored=G_NodeList(node, precolored);
		G_enter(degree, node, d);
		continue;
	    }		
	    if(*d >= REG_NUM)
		spillWorkList=G_NodeList(node, spillWorkList);
		
	    else if(MoveRelated(node))
		freezeWorkList=G_NodeList(node, freezeWorkList);
		
	    else
		simplifyWorkList=G_NodeList(node, simplifyWorkList);
		
	    G_enter(degree, node, d);
	}
}
static void Simplify(){
	G_node node = simplifyWorkList->head;
	simplifyWorkList = simplifyWorkList->tail;	
	selectStack = G_NodeList(node, selectStack);

	for(G_nodeList nl=Adjacent(node);nl;nl=nl->tail)
	    DecrementDegree(nl->head);
	
}

static void FreezeMoves(G_node u){
	for(Live_moveList m = NodeMoves(u); m; m=m->tail)
	{
	    G_node v;
	    if(GetAlias(m->dst) == GetAlias(u))
		v = GetAlias(m->src);
	    else
		v = GetAlias(m->dst);

	    frozenMoves = Live_MoveList(m->src, m->dst, frozenMoves);
	    activeMoves = Live_remove(m->src, m->dst, activeMoves);
		
	    if(!NodeMoves(v) && *(int *)G_look(degree, v)<REG_NUM)
	    {
		freezeWorkList = G_removeNode(v, freezeWorkList);
		simplifyWorkList = G_NodeList(v, simplifyWorkList);
	    }
	}
}

static void Freeze(){
	G_node node = freezeWorkList->head;
	freezeWorkList = freezeWorkList->tail;
	simplifyWorkList = G_NodeList(node, simplifyWorkList);
	FreezeMoves(node);
}
static void SelectSpill(){
	G_node node = spillWorkList->head;
	spillWorkList = spillWorkList->tail;
	simplifyWorkList = G_NodeList(node, simplifyWorkList);
}

Temp_tempList removeColor(G_node t, Temp_tempList l){
	Temp_tempList last = NULL;
	for(Temp_tempList p=l;p;p=p->tail)
	{
	    if(!strcmp(Temp_look(color, Live_gtemp(t)), Temp_look(color, p->head)))
	    {
		if(last)
		    last->tail = p->tail;
		else
		    l = l->tail;
			
		break;
	    }
	    last = p;
	}
	return l;
}

static void AssignColor(){
	for(;selectStack ;selectStack = selectStack->tail)
	{
	    G_node node = selectStack->head;
	    Temp_tempList okColors = NULL;

	    for(Temp_tempList p =F_register();p;p=p->tail)
		okColors = Temp_TempList(p->head,okColors);
	
		
	    for(G_nodeList adj=G_adj(node);adj;adj=adj->tail)
	    {
		G_node w = adj->head;
		if(G_inNodeList(GetAlias(w), G_unionNodeList(precolored, coloredNode)))
		    okColors = removeColor(GetAlias(w), okColors);
			
	    }

	    if(!okColors)
		spilledNode = G_NodeList(node, spilledNode);
		
	    else
	    {
		Temp_enter(color, Live_gtemp(node), Temp_look(F_tempMap, okColors->head));
		coloredNode = G_NodeList(node, coloredNode);
	    }
	}

	for(G_nodeList nl=coalescedNode;nl;nl=nl->tail)
	{
	    G_node node = nl->head;
	    Temp_enter(color, Live_gtemp(node), Temp_look(color, Live_gtemp(GetAlias(node))));
	}
}

void AS_rewrite(AS_instrList iList){
  	AS_instrList p = iList;
  	AS_instrList last = NULL;
  	for(;p;p=p->tail)
  	{
    	    AS_instr ins = p->head;
    	    if(ins->kind == I_MOVE)			
		if(strstr(ins->u.MOVE.assem,"movq `s0, `d0") && Temp_look(color, ins->u.MOVE.src->head) == Temp_look(color, ins->u.MOVE.dst->head))
		{
            	    last->tail = p->tail;  
            	    continue;          
        	}
    	    last = p;
  	}
}

struct RA_result RA_regAlloc(F_frame f, AS_instrList il) {
	G_graph fg = FG_AssemFlowGraph(il);
	struct Live_graph lg = Live_liveness(fg);

	precolored = NULL;
	coloredNode = NULL;
	spilledNode = NULL;
	coalescedNode = NULL;
	selectStack = NULL;
	spillWorkList = NULL;
	freezeWorkList = NULL;
	simplifyWorkList = NULL;

	worklistMoves = NULL;
	coalescedMoves = NULL;
	frozenMoves = NULL;
	constrainedMoves = NULL;
	activeMoves = NULL;

	degree = G_empty();
	alias = G_empty();
	moveList = NULL;
	color = Temp_empty();
	color = Temp_layerMap(color, F_tempMap);

	worklistMoves = moveList = lg.moves;
	MakeWorkList(lg.graph);
		
	do 
	{
	    if(simplifyWorkList) 
		Simplify();
	    else if(worklistMoves) 
		Coalesce();
	    else if(freezeWorkList) 
		Freeze();
	    else if(spillWorkList) 
		SelectSpill();
	} while(simplifyWorkList || worklistMoves || freezeWorkList || spillWorkList);
		
	AssignColor();
	
	if(spilledNode){
		AS_instrList nil = AS_rewriteSpill(f, il, spilledNode);
		return RA_regAlloc(f, nil);
	}

	AS_rewrite(il);
					

	struct RA_result ret;
	ret.coloring = color;
	ret.il=il;

	return ret;
}
