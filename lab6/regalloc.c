#include <stdio.h>
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
static G_table color;
static G_table alias;

static void clear(){
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
	color = G_empty();
	alias = G_empty();
}

static void Push(G_node node, enum State st){
	switch(st){
		case PRECOLORED: precolored=G_NodeList(node, precolored);break;
		case SIMPLIFY: simplifyWorkList=G_NodeList(node, simplifyWorkList);break;
		case SPILL: spillWorkList=G_NodeList(node, spillWorkList);break;
		case FREEZE: freezeWorkList=G_NodeList(node, freezeWorkList);break;
		case STACK: selectStack = G_NodeList(node, selectStack);break;
		default:assert(0);
	}
	
}

static bool MoveRelated(G_node node){
	return inMoveList(node, worklistMoves) || inMoveList(node, activeMoves);
}

static G_nodeList Adjacent(G_node node){
	G_nodeList adj = G_adj(node);
	G_nodeList locked = G_unionNodeList(selectStack, coalescedNode);
	return G_minusNodeList(adj, locked);
}
static void EnableMoves(G_nodeList nodes){
	for(;nodes;nodes=nodes->tail){
		G_node node = nodes->head;
		Live_moveList rel = RMrelatedMovs(node, activeMoves);
		if(inMoveList(node, activeMoves)){
			activeMoves = activeMoves->tail;
		}
		worklistMoves = CatMovList(worklistMoves, rel);
	}	
}
static void DecrementDegree(G_node node){
	nodeInfo info = G_nodeInfo(node);
	int d = info->degree;
	info->degree = d-1;
	if(d == REG_NUM){
		EnableMoves(G_NodeList(node, Adjacent(node)));
		spillWorkList = G_removeNode(node, spillWorkList);
		if(MoveRelated(node)){
			info->stat = FREEZE;
			Push(node, FREEZE);
		}
		else{
			info->stat = SIMPLIFY;
			Push(node, SIMPLIFY);
		}
	}
}
static G_node GetAlias(G_node node){
	if(G_inNodeList(node, coalescedNode)){
		nodeInfo info = G_nodeInfo(node);
		assert(info->alias);
		return GetAlias(info->alias);
	}
	else{
		return node;
	}
}
static void AddWorkList(G_node node){
	nodeInfo info = G_nodeInfo(node);
	if(!G_inNodeList(node, precolored)
			&& !MoveRelated(node)
				&& info->degree < REG_NUM){
		freezeWorkList = G_removeNode(node, freezeWorkList);
		Push(node, SIMPLIFY);
	}
}
static bool OK(G_node t, G_node r){
	nodeInfo tinfo = G_nodeInfo(t);
	return (tinfo->degree<REG_NUM 
		|| G_inNodeList(t,precolored)
		|| G_inNodeList(t, G_adj(r)));
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
			nodeInfo info = G_nodeInfo(n);
			if(info->degree >= REG_NUM) cnt += 1;
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
	nodeInfo vinfo = G_nodeInfo(v);
	vinfo->alias = u;
	EnableMoves(G_NodeList(v, NULL));
	for(G_nodeList nl=Adjacent(v);nl;nl=nl->tail){
		G_node t = nl->head;
		if(G_goesTo(u, t) || u == t)continue;
		G_addEdge(t, u);		
		DecrementDegree(t);
	}
	nodeInfo uinfo = G_nodeInfo(u);
	if(uinfo->degree>=REG_NUM && G_inNodeList(u, freezeWorkList)){
		freezeWorkList = G_removeNode(u, freezeWorkList);
		spillWorkList = G_NodeList(u, spillWorkList);
	}	
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
		
		nodeInfo vinfo = G_nodeInfo(v);
		if(!G_inNodeList(v,precolored) && !inMoveList(v, activeMoves) && vinfo->degree<REG_NUM){
			freezeWorkList = G_removeNode(v, freezeWorkList);
			simplifyWorkList = G_NodeList(v, simplifyWorkList);
		}

	}
}



//core procedure
static void MakeWorkList(G_graph cfgraph){
	G_nodeList nl = G_nodes(cfgraph);
	for(;nl;nl=nl->tail){
		G_node node = nl->head;
		nodeInfo info = G_nodeInfo(node);
		int degree = G_degree(node);
		info->degree = degree;
		if(Temp_look(F_tempMap, info->reg)){
			info->stat = PRECOLORED;
			info->degree = 9999;
			Push(node, PRECOLORED);
			continue;
		}		
		enum State st;
		if(degree >= REG_NUM){
			st = SPILL;
		}
		else if(MoveRelated(node)){
			st = FREEZE;
		}
		else{
			st = SIMPLIFY;
		}
		info->stat = st;
		Push(node, st);
	}
}
static void Simplify(){
	G_node node = simplifyWorkList->head;
	simplifyWorkList = simplifyWorkList->tail;	
	nodeInfo info = G_nodeInfo(node);
	info->stat = STACK;
	Push(node, STACK);
	for(G_nodeList nl=Adjacent(node);nl;nl=nl->tail){
		DecrementDegree(nl->head);
	}
}
static void Coalesce(){
	Live_moveList p = Live_MoveList(worklistMoves->src,worklistMoves->dst,NULL);
	worklistMoves = worklistMoves->tail;
	G_node src = GetAlias(p->src);
	G_node dst = GetAlias(p->dst);

	//Live_prMovs(Live_MoveList(p->src,p->dst,NULL));
	G_node u,v;
	if(G_inNodeList(src, precolored)){
		u = src; v = dst;
	}
	else{
		u = dst; v = src;
	}
	
	if(u == v){
		//printf("3");
		coalescedMoves = Live_MoveList(p->src, p->dst, coalescedMoves);
		AddWorkList(u);
	}
	else if(G_inNodeList(v, precolored) || G_inNodeList(u, G_adj(v))){
		//printf("4");
		constrainedMoves = Live_MoveList(p->src, p->dst, constrainedMoves);
		AddWorkList(u);
		AddWorkList(v);
	}
	else if(Check(u, v)){
		//printf("5");
		coalescedMoves = Live_MoveList(p->src, p->dst, coalescedMoves);
		Combine(u, v);
		AddWorkList(u);
	}
	else{
		//printf("6");
		activeMoves = Live_MoveList(p->src, p->dst, activeMoves);
	}
	//printf("\n");
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
static void AssignColor(){
	COL_map();
	for(G_nodeList nl=selectStack;nl;nl=nl->tail){
		G_node node = nl->head;
		Temp_tempList colors = COL_allColor();
		
		for(G_nodeList adj=G_adj(node);adj;adj=adj->tail){
			G_node t = adj->head;
			G_nodeList used = G_unionNodeList(precolored, coloredNode);
			if(G_inNodeList(GetAlias(t), used)){
				colors = COL_rmColor(GetAlias(t), colors);
			}
		}

		if(!colors){
			spilledNode = G_NodeList(node, spilledNode);
		}
		else{
			COL_assignColor(node, colors);
			coloredNode = G_NodeList(node, coloredNode);
		}
	}
	selectStack = NULL;
	for(G_nodeList nl=coalescedNode;nl;nl=nl->tail){
		G_node node = nl->head;
		COL_sameColor(GetAlias(node), node);
	}
}

struct RA_result RA_regAlloc(F_frame f, AS_instrList il) {
	clear();
	G_graph fg = FG_AssemFlowGraph(il);
	struct Live_graph lg = Live_liveness(fg);

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

	Temp_map map = Temp_layerMap(COL_map(),Temp_layerMap(F_tempMap, Temp_name()));
	
	if(spilledNode){
		COL_clearMap();
		AS_instrList nil = AS_rewriteSpill(f, il, spilledNode);
		return RA_regAlloc(f, nil);
	}

	AS_rewrite(il, map);
					

	struct RA_result ret;
	ret.coloring = COL_map();
	ret.il=il;

	return ret;
}
