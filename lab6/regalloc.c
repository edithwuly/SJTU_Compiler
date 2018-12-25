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

static Temp_map color;

static bool MoveRelated(G_node node){
	return inMoveList(node, worklistMoves) || inMoveList(node, activeMoves);
}

static G_nodeList Adjacent(G_node node){
	return G_minusNodeList(G_adj(node), G_unionNodeList(selectStack, coalescedNode));
}
static void EnableMoves(G_nodeList nodes){
	for(;nodes;nodes=nodes->tail){
		G_node node = nodes->head;
		Live_moveList rel = RMrelatedMovs(node, activeMoves);
		if(inMoveList(node, activeMoves))
			activeMoves = activeMoves->tail;
		
		worklistMoves = CatMovList(worklistMoves, rel);
	}	
}
static void DecrementDegree(G_node node){
	int *d = G_look(degree, node);
	(*d)--;
	if(*d + 1 == REG_NUM)
	{
		EnableMoves(G_NodeList(node, Adjacent(node)));
		spillWorkList = G_removeNode(node, spillWorkList);
		if(MoveRelated(node))
		    freezeWorkList=G_NodeList(node, freezeWorkList);
		
		else
		    simplifyWorkList=G_NodeList(node, simplifyWorkList);
		
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
	return (*(int *)G_look(degree, t) < REG_NUM || G_inNodeList(t,precolored) || G_inNodeList(t, G_adj(r)));
}
static bool Check(G_node u, G_node v){
	if(G_inNodeList(u, precolored)){
		bool pass = TRUE;
		for(G_nodeList nl=Adjacent(v);nl;nl=nl->tail){
			G_node t = nl->head;
			if(!OK(t,u)){
				pass = FALSE;
				break;
			}
		}
		if(pass) return TRUE;
	}
	else{
		G_nodeList nodes = G_unionNodeList(Adjacent(u),Adjacent(v));
		int cnt = 0;
		for(;nodes;nodes=nodes->tail){
			G_node n = nodes->head;
			if(*(int *)G_look(degree, n) >= REG_NUM) cnt += 1;
		}
		if(cnt < REG_NUM) return TRUE;
	}
	return FALSE;
}
static void Combine(G_node u, G_node v){
	if(G_inNodeList(v, freezeWorkList))
	    freezeWorkList = G_removeNode(v, freezeWorkList);
	else
	    spillWorkList = G_removeNode(v, spillWorkList);

	coalescedNode = G_NodeList(v, coalescedNode);

	G_enter(alias, v, u);

	EnableMoves(G_NodeList(v, NULL));
	for(G_nodeList nl=Adjacent(v);nl;nl=nl->tail){
		G_node t = nl->head;
		if(G_goesTo(u, t) || u == t)continue;
		G_addEdge(t, u);		
		DecrementDegree(t);
	}
	if(*(int *)G_look(degree, u) >= REG_NUM && G_inNodeList(u, freezeWorkList)){
		freezeWorkList = G_removeNode(u, freezeWorkList);
		spillWorkList = G_NodeList(u, spillWorkList);
	}	
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
static void Coalesce(){
	Live_moveList p = Live_MoveList(worklistMoves->src,worklistMoves->dst,NULL);
	worklistMoves = worklistMoves->tail;
	G_node src = GetAlias(p->src);
	G_node dst = GetAlias(p->dst);

	G_node u,v;
	if (G_inNodeList(src, precolored)){
		u = src; 
		v = dst;
	}
	else{
		u = dst; 
		v = src;
	}
	
	if(u == v){
		coalescedMoves = Live_MoveList(p->src, p->dst, coalescedMoves);
		AddWorkList(u);
	}
	else if(G_inNodeList(v, precolored) || G_inNodeList(u, G_adj(v))){
		constrainedMoves = Live_MoveList(p->src, p->dst, constrainedMoves);
		AddWorkList(u);
		AddWorkList(v);
	}
	else if(Check(u, v)){
		coalescedMoves = Live_MoveList(p->src, p->dst, coalescedMoves);
		Combine(u, v);
		AddWorkList(u);
	}
	else
		activeMoves = Live_MoveList(p->src, p->dst, activeMoves);
	
}

static void FreezeMoves(G_node node){
	Live_moveList ml = RMrelatedMovs(node, activeMoves);
	if(inMoveList(node, activeMoves))
		activeMoves = activeMoves->tail;
	for(;ml;ml=ml->tail){
		G_node src = GetAlias(ml->src);
		G_node dst = GetAlias(ml->dst);
		G_node v;
		if(GetAlias(node) == src)
			v = dst;
		else
			v = src;
		frozenMoves = Live_MoveList(ml->src, ml->dst, frozenMoves);
		
		if(!G_inNodeList(v,precolored) && !inMoveList(v, activeMoves) && *(int *)G_look(degree, v)<REG_NUM){
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

Temp_tempList COL_rmColor(G_node t, Temp_tempList l){
	Temp_temp c = Live_gtemp(t);
	Temp_map map = Temp_layerMap(color, F_tempMap);

	Temp_tempList last = NULL;
	for(Temp_tempList p=l;p;p=p->tail){
		if(!strcmp(Temp_look(map, c), Temp_look(map, p->head))){
			if(last){
				last->tail = p->tail;
			}
			else{
				l = l->tail;
			}
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
	
		
		for(G_nodeList adj=G_adj(node);adj;adj=adj->tail){
			G_node w = adj->head;
			if(G_inNodeList(GetAlias(w), G_unionNodeList(precolored, coloredNode))){
				okColors = COL_rmColor(GetAlias(w), okColors);
			}
		}

		if(!okColors)
			spilledNode = G_NodeList(node, spilledNode);
		
		else{
			Temp_enter(color, Live_gtemp(node), Temp_look(F_tempMap, okColors->head));
			coloredNode = G_NodeList(node, coloredNode);
		}
	}

	for(G_nodeList nl=coalescedNode;nl;nl=nl->tail){
		G_node node = nl->head;
		Temp_enter(color, Live_gtemp(node), Temp_look(Temp_layerMap(color, F_tempMap), Live_gtemp(GetAlias(node))));
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

	color = Temp_empty();

	worklistMoves = lg.moves;
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

	Temp_map map = Temp_layerMap(color,Temp_layerMap(F_tempMap, Temp_name()));
	
	if(spilledNode){
		AS_instrList nil = AS_rewriteSpill(f, il, spilledNode);
		return RA_regAlloc(f, nil);
	}

	AS_rewrite(il, map);
					

	struct RA_result ret;
	ret.coloring = color;
	ret.il=il;

	return ret;
}
