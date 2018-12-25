/*
 * color.h - Data structures and function prototypes for coloring algorithm
 *             to determine register allocation.
 */

#ifndef COLOR_H
#define COLOR_H

struct COL_result {Temp_map coloring; Temp_tempList spills;};
struct COL_result COL_color(G_graph ig, Temp_map initial, Temp_tempList regs, Live_moveList moves);

Temp_map COL_map();
void COL_clearMap();
Temp_tempList COL_allColor();
Temp_tempList COL_rmColor(G_node t, Temp_tempList l);
void COL_assignColor(G_node t, Temp_tempList colors);
void COL_sameColor(G_node from, G_node to);
#endif
