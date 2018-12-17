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

struct RA_result RA_regAlloc(F_frame f, AS_instrList il) {
	//your code here

	G_graph flow_graph = FG_AssemFlowGraph(il, f);
	Temp_map initial = Temp_layerMap(Temp_empty(), Temp_name());
	Temp_tempList regs = F_registers();

	struct COL_result col_res = COL_color(flow_graph, initial, regs);

	struct RA_result ret;
	return ret;
}
