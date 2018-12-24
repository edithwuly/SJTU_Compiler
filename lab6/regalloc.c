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
#include "listop.h"

const int REG_NUM = 16;

//node set
static G_nodeList precolored = NULL;
static G_nodeList coloredNode = NULL;
static G_nodeList spilledNode = NULL;
static G_nodeList coalescedNode = NULL;

//nodeWorklist
static G_nodeList spillWorkList = NULL;
static G_nodeList freezeWorkList = NULL;
static G_nodeList simplifyWorkList = NULL;

//moveList
static Live_moveList worklistMoves = NULL;
static Live_moveList coalescedMoves = NULL;
static Live_moveList frozenMoves = NULL;
static Live_moveList constrainedMoves = NULL;
static Live_moveList activeMoves = NULL;


//stack
static G_nodeList nodeStack;

//helper
void RA_showInfo(void *p){
	nodeInfo t = p;
	Temp_map map = Temp_layerMap(COL_map(),Temp_layerMap(F_tempMap, Temp_name()));
	if(t->alias){
		printf("%s\t stat:%d\tdegree:%d\talias:%s\t",Temp_look(map, t->reg), t->stat, t->degree,Temp_look(map, Live_gtemp(t->alias)));
	}
	else
		printf("%s\t stat:%d\tdegree:%d\t",Temp_look(map, t->reg), t->stat, t->degree);
}
static void clear(){
	//node set
	precolored = NULL;
	coloredNode = NULL;
	spilledNode = NULL;
	coalescedNode = NULL;

	//nodeWorklist
	spillWorkList = NULL;
	freezeWorkList = NULL;
	simplifyWorkList = NULL;

	//moveList
	worklistMoves = NULL;
	coalescedMoves = NULL;
	frozenMoves = NULL;
	constrainedMoves = NULL;
	activeMoves = NULL;

	nodeStack = NULL;
}
static void Push(G_node node, enum State st){
	switch(st){
		case PRECOLORED: precolored=G_NodeList(node, precolored);break;
		case SIMPLIFY: simplifyWorkList=G_NodeList(node, simplifyWorkList);break;
		case SPILL: spillWorkList=G_NodeList(node, spillWorkList);break;
		case FREEZE: freezeWorkList=G_NodeList(node, freezeWorkList);break;
		case STACK: nodeStack = G_NodeList(node, nodeStack);break;
		default:assert(0);
	}
	
}
static bool MoveRelated(G_node node){
	return inMoveList(node, worklistMoves) || inMoveList(node, activeMoves);
}

static G_nodeList Adjacent(G_node node){
	G_nodeList adj = G_adj(node);
	G_nodeList locked = NL_Union(nodeStack, coalescedNode);
	return NL_Minus(adj, locked);
}
static void EnableMoves(G_nodeList nodes){
	for(;nodes;nodes=nodes->tail){
		G_node node = nodes->head;
		Live_moveList rel = RMrelatedMovs(node, activeMoves);
		//deal with first-mov-related err
		if(inMoveList(node, activeMoves)){
			activeMoves = activeMoves->tail;
		}
		worklistMoves = CatMovList(worklistMoves, rel);
	}	
}
static void DecDegree(G_node node){
	nodeInfo info = G_nodeInfo(node);
	int d = info->degree;
	info->degree = d-1;
	if(d == REG_NUM){
		EnableMoves(G_NodeList(node, Adjacent(node)));
		spillWorkList = NL_rmNode(spillWorkList, node);
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
		freezeWorkList = NL_rmNode(freezeWorkList, node);
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
		G_nodeList nodes = NL_Union(Adjacent(u),Adjacent(v));
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
		freezeWorkList = NL_rmNode(freezeWorkList, v);
	else
		spillWorkList = NL_rmNode(spillWorkList, v);

	coalescedNode = G_NodeList(v, coalescedNode);
	nodeInfo vinfo = G_nodeInfo(v);
	vinfo->alias = u;
	EnableMoves(G_NodeList(v, NULL));
	for(G_nodeList nl=Adjacent(v);nl;nl=nl->tail){
		G_node t = nl->head;
		if(G_goesTo(u, t) || u == t)continue;
		G_addEdge(t, u);		
		DecDegree(t);
	}
	nodeInfo uinfo = G_nodeInfo(u);
	if(uinfo->degree>=REG_NUM && G_inNodeList(u, freezeWorkList)){
		freezeWorkList = NL_rmNode(freezeWorkList, u);
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
			freezeWorkList = NL_rmNode(freezeWorkList, v);
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
		DecDegree(nl->head);
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
	//blind select
	G_node node = spillWorkList->head;
	spillWorkList = spillWorkList->tail;
	simplifyWorkList = G_NodeList(node, simplifyWorkList);
}
static void AssignColor(){
	COL_map();
	for(G_nodeList nl=nodeStack;nl;nl=nl->tail){
		G_node node = nl->head;
		//Temp_map map = Temp_layerMap(F_tempMap, Temp_name());
		//printf("t%s\n", Temp_look(map, Live_gtemp(node)));
		Temp_tempList colors = COL_allColor();
		
		for(G_nodeList adj=G_adj(node);adj;adj=adj->tail){
			G_node t = adj->head;
			//printf("\tadj t%s\n", Temp_look(map, Live_gtemp(t)));
			G_nodeList used = NL_Union(precolored, coloredNode);
			if(G_inNodeList(GetAlias(t), used)){
				colors = COL_rmColor(GetAlias(t), colors);
				//printf("\t\trm one color\n");
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
	nodeStack = NULL;
	for(G_nodeList nl=coalescedNode;nl;nl=nl->tail){
		G_node node = nl->head;
		COL_sameColor(GetAlias(node), node);
	}
}

void printMovs(){
	printf("\n-------==== spillworklist =====-----\n");
	G_show(stdout, spillWorkList, RA_showInfo);	
	printf("\n-------==== stack =====-----\n");
	G_show(stdout, nodeStack, RA_showInfo);	
	printf("\n-------==== coalescedMoves =====-----\n");
	Live_prMovs(coalescedMoves);
	printf("\n-------==== frozenMoves =====-----\n");
	Live_prMovs(frozenMoves);
	printf("\n-------==== constrainedMoves =====-----\n");
	Live_prMovs(constrainedMoves);
	printf("\n-------==== activeMoves =====-----\n");
	Live_prMovs(activeMoves);
}

struct RA_result RA_regAlloc(F_frame f, AS_instrList il) {
	clear();
	//Flowgraph
	G_graph fg = FG_AssemFlowGraph(il);  /* 10.1 */
		//G_show(stdout, G_nodes(fg), FG_showInfo);
		//printf("\n-------====flow graph=====-----\n");

	//liveness analysis
	struct Live_graph lg = Live_liveness(fg);  /* 10.2 */
		//G_show(stdout, G_nodes(lg.graph), Live_showInfo);
		//printf("\n-------==== CF graph=====-----\n");
		//Live_prMovs(lg.moves);

	worklistMoves = lg.moves;
	MakeWorkList(lg.graph);
		//G_show(stdout, simplifyWorkList, RA_showInfo);
		//Live_prMovs(worklistMoves);
		//printf("\n-------==== init =====-----\n");
		

	bool empty = FALSE;
	int cnt = 0;
	while(!empty){
		empty = TRUE;
		if(simplifyWorkList){
			empty = FALSE;
			Simplify();
		}
		else if(worklistMoves){
			empty = FALSE;
			Coalesce();
		}
		else if(freezeWorkList){
			empty = FALSE;
			Freeze();
		}
		else if(spillWorkList){
			empty = FALSE;
			SelectSpill();
		}
	}
	//printf("\n-------==== loop over =====-----\n");
	//printMovs();
		
	AssignColor();

	Temp_map map = Temp_layerMap(COL_map(),Temp_layerMap(F_tempMap, Temp_name()));
	
	if(spilledNode){
		printf("\n-------==== spillnode =====-----\n");
		G_show(stdout, spilledNode, RA_showInfo);
		COL_clearMap();
		AS_instrList nil = AS_rewriteSpill(f, il, spilledNode);
		printf("\n");
		//AS_printInstrList (stdout, nil, map);
		return RA_regAlloc(f, nil);
		assert(0);
	}

	AS_rewrite(il, map);
		//printf("BEGIN function\n");
		AS_printInstrList (stdout, il, map);
 		printf("\n-------==== after RA =====-----\n");
					

	struct RA_result ret;
	ret.coloring = COL_map();
	ret.il=il;

	return ret;
}
