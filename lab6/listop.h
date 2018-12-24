#ifndef LISTOP_H
#define LISTOP_H

#include <stdio.h>
#include "util.h"
#include "temp.h"
#include "graph.h"
#include "liveness.h"

bool inMoveList(G_node node, Live_moveList list){
    for(;list;list = list->tail){
        if(node == list->dst || node == list->src){
            return TRUE;
        }
    }
    return FALSE;
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
            else{
                //rm first mov need to be specially dealed with
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


G_nodeList NL_Union(G_nodeList A, G_nodeList B){
    G_nodeList list = NULL;
    for(;A;A=A->tail){
        G_node n = A->head;
        list = G_NodeList(n, list);
    }
    for(;B;B=B->tail){
        G_node n = B->head;
        if(!G_inNodeList(n, A)){
            list = G_NodeList(n, list);
        }
    }
    return list;
}
G_nodeList NL_Inter(G_nodeList A, G_nodeList B){
    G_nodeList list = NULL;
    for(;B;B=B->tail){
        G_node n = B->head;
        if(G_inNodeList(n, A)){
            list = G_NodeList(n, list);
        }
    }
    return list;
}
G_nodeList NL_Minus(G_nodeList A, G_nodeList B){
    G_nodeList list = NULL;
    for(;A;A=A->tail){
        G_node n = A->head;
        if(!G_inNodeList(n, B)){
            list = G_NodeList(n, list);
        }
    }
    return list;
}
G_nodeList NL_rmNode(G_nodeList li, G_node node){
    G_nodeList p = li;
    G_nodeList last = NULL;
    while(p){
        if(p->head == node){
            if(last){
                last->tail = p->tail;
                break;
            }
            else{
                li = li->tail;
                break;
            }
        }
        last = p;
        p = p->tail;
    }
    return li;
}

#endif