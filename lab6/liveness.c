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


static G_graph cfGraph; //cfnode -> temp
static G_nodeList revFlow; 
static TAB_table liveTab; // flownode -> in/out
static TAB_table TNtab; //temp -> cfnode
static Live_moveList movs;

//data structure
typedef struct liveInfo_ *liveInfo;
struct liveInfo_{
	Temp_tempList in;
	Temp_tempList out;
};
liveInfo LiveInfo(Temp_tempList in, Temp_tempList out){
	liveInfo i = checked_malloc(sizeof(*i));
	i->in = in;
	i->out = out;
	return i;
}

Live_moveList Live_MoveList(G_node src, G_node dst, Live_moveList tail) {
	Live_moveList lm = (Live_moveList) checked_malloc(sizeof(*lm));
	lm->src = src;
	lm->dst = dst;
	lm->tail = tail;
	return lm;
}

bool inMoveList(G_node node, Live_moveList list){
    for(;list;list = list->tail){
        if(node == list->dst || node == list->src){
            return TRUE;
        }
    }
    return FALSE;
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

Live_moveList CatMovList(Live_moveList A, Live_moveList B){
    if(!A) return B;
    Live_moveList p = A;
    assert(p);
    for(;p->tail;p=p->tail){}
    p->tail = B;
    return A;
}

//helper
static int pool[100];
static int cnt;
static bool inPool(Temp_temp t){	
	int mark = Temp_int(t);
	for(int i=0;i<cnt;i++){
		if(pool[i] == mark){
			return TRUE;
		}
	}
	pool[cnt] = mark;
	cnt += 1;
	return FALSE;
}

Temp_temp Live_gtemp(G_node n) {
	//your code here.
	return G_nodeInfo(n);
}

static void genGraph(G_graph flow){
	cnt = 0;
	for(G_nodeList nodes=G_nodes(flow);nodes;nodes=nodes->tail){
		G_node fnode = nodes->head;
		for(Temp_tempList tp = FG_def(fnode);tp;tp=tp->tail){
			Temp_temp t = tp->head;
			if(!inPool(t)){
				G_node cfnode = G_Node(cfGraph,t);
				TAB_enter(TNtab, t, cfnode);
			}
		}
		for(Temp_tempList tp = FG_use(fnode);tp;tp=tp->tail){
			Temp_temp t = tp->head;
			if(!inPool(t)){
				G_node cfnode = G_Node(cfGraph,t);
				TAB_enter(TNtab, t, cfnode);
			}
		}
		TAB_enter(liveTab, fnode, LiveInfo(NULL, NULL));
		revFlow = G_NodeList(fnode, revFlow);
	}
}
static void loopAnalyse(){
	bool stable = FALSE;
	while(!stable){
		stable = TRUE;
		for(G_nodeList np=revFlow;np;np=np->tail){
			G_node fnode = np->head;

			liveInfo old = TAB_look(liveTab, fnode);
			assert(old);

			Temp_tempList out = old->out;
			for(G_nodeList sp=G_succ(fnode);sp;sp=sp->tail){
				G_node succ = sp->head;
				liveInfo tmp = TAB_look(liveTab, succ);
				assert(tmp);
				out = Temp_UnionCombine(out, tmp->in);
			}

			Temp_tempList in = Temp_Union(FG_use(fnode), Temp_Minus(out, FG_def(fnode)));

			if(!Temp_Equal(in, old->in) || !Temp_Equal(out, old->out)){
				stable = FALSE;
			}

			TAB_enter(liveTab, fnode, LiveInfo(in, out));
		}
	}
}
static void addConf(){
	for(G_nodeList np=revFlow;np;np=np->tail){
		G_node fnode = np->head;

		liveInfo info = TAB_look(liveTab, fnode);
		Temp_tempList live = info->out;

		//move
		if(FG_isMove(fnode)){
			live = Temp_Minus(live, FG_use(fnode));

			Temp_temp dst = FG_def(fnode)->head;
			G_node d = TAB_look(TNtab, dst);
			Temp_temp src = FG_use(fnode)->head;
			G_node s = TAB_look(TNtab, src);

			movs = Live_MoveList(s, d, movs);
		}

		//add conflicts 
		Temp_tempList def = FG_def(fnode);
		live = Temp_Union(live, def);
		for(Temp_tempList p1=def;p1;p1=p1->tail){
			G_node cf1 = TAB_look(TNtab, p1->head);
			for(Temp_tempList p2=live;p2;p2=p2->tail){
				G_node cf2 = TAB_look(TNtab, p2->head);
				if(G_goesTo(cf2, cf1) || cf1 == cf2)continue;
				G_addEdge(cf1, cf2);
			}
		}

	}
}

/* Conflict graph -- [node -> temp]*/
struct Live_graph Live_liveness(G_graph flow) {
	//your code here.
	struct Live_graph lg;

	cfGraph = G_Graph();
	revFlow = NULL;
	liveTab = TAB_empty();
	TNtab = TAB_empty();
	movs = NULL;	

	//generate a empty conflict graph with no edge in it 
	genGraph(flow);
	
	//loop find in/out
	loopAnalyse();
	
	//add conflict edges according to [in]
	addConf();
	
	lg.graph = cfGraph;
	lg.moves = movs;

	return lg;
}


