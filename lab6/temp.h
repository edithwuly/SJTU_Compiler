/*
 * temp.h 
 *
 */

#ifndef TEMP_H
#define TEMP_H

typedef struct Temp_temp_ *Temp_temp;
Temp_temp Temp_newtemp(void);
int Temp_int(Temp_temp);

typedef struct Temp_tempList_ *Temp_tempList;
struct Temp_tempList_ { Temp_temp head; Temp_tempList tail;};
Temp_tempList Temp_TempList(Temp_temp h, Temp_tempList t);

typedef S_symbol Temp_label;
Temp_label Temp_newlabel(void);
Temp_label Temp_namedlabel(string name);
string Temp_labelstring(Temp_label s);

typedef struct Temp_labelList_ *Temp_labelList;
struct Temp_labelList_ { Temp_label head; Temp_labelList tail;};
Temp_labelList Temp_LabelList(Temp_label h, Temp_labelList t);

typedef struct Temp_map_ *Temp_map;
Temp_map Temp_empty(void);
Temp_map Temp_layerMap(Temp_map over, Temp_map under);
void Temp_enter(Temp_map m, Temp_temp t, string s);
string Temp_look(Temp_map m, Temp_temp t);
void Temp_dumpMap(FILE *out, Temp_map m);

Temp_map Temp_name(void);

Temp_tempList Temp_catList(Temp_tempList a, Temp_tempList b);
bool Temp_inList(Temp_tempList list, Temp_temp t);
Temp_tempList Temp_Union(Temp_tempList A, Temp_tempList B);
Temp_tempList Temp_Minus(Temp_tempList A, Temp_tempList B);
bool Temp_Equal(Temp_tempList A, Temp_tempList B);
void Temp_replace(Temp_temp old, Temp_temp fresh, Temp_tempList li);


#endif
