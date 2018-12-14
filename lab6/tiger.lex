%{
/* Lab2 Attention: You are only allowed to add code in this file and start at Line 26.*/
#include <string.h>
#include "util.h"
#include "symbol.h"
#include "errormsg.h"
#include "absyn.h"
#include "y.tab.h"

int charPos=1;

int yywrap(void)
{
 charPos=1;
 return 1;
}

void adjust(void)
{
 EM_tokPos=charPos;
 charPos+=yyleng;
}

/*":" { adjust(); return COLON; }
* Please don't modify the lines above.
* You can add C declarations of your own below.
*/

/* @function: getstr
 * @input: a string literal
 * @output: the string value for the input which has all the escape sequences 
 * translated into their meaning.
 */
static int comment_depth;
static int cur;
static char temp[4096];
char *getstr(const char *str)
{
	//optional: implement this function if you need it
	return NULL;
}

%}
  /* You can add lex definitions here. */
%Start COMMENT STR

%%
  /* 
  * Below is an example, which you can wipe out
  * and write reguler expressions and actions of your own.
  */ 

"\n" {adjust(); EM_newline(); continue;}
"/*" {adjust(), comment_depth++; BEGIN COMMENT;}

<COMMENT>"*/" {adjust(); comment_depth--;
    if (comment_depth == 0) 
	BEGIN INITIAL;
}
<COMMENT>. {adjust();}

<INITIAL>"," {adjust(); return COMMA;}
<INITIAL>":" {adjust(); return COLON;}
<INITIAL>";" {adjust(); return SEMICOLON;}
<INITIAL>"(" {adjust(); return LPAREN;}
<INITIAL>")" {adjust(); return RPAREN;}
<INITIAL>"[" {adjust(); return LBRACK;}
<INITIAL>"]" {adjust(); return RBRACK;}
<INITIAL>"{" {adjust(); return LBRACE;}
<INITIAL>"}" {adjust(); return RBRACE;}
<INITIAL>"." {adjust(); return DOT;}
<INITIAL>"+" {adjust(); return PLUS;}
<INITIAL>"-" {adjust(); return MINUS;}
<INITIAL>"*" {adjust(); return TIMES;}
<INITIAL>"/" {adjust(); return DIVIDE;}
<INITIAL>"=" {adjust(); return EQ;}
<INITIAL>"<>" {adjust(); return NEQ;}
<INITIAL>"<" {adjust(); return LT;}
<INITIAL>"<=" {adjust(); return LE;}
<INITIAL>">" {adjust(); return GT;}
<INITIAL>">=" {adjust(); return GE;}
<INITIAL>"&" {adjust(); return AND;}
<INITIAL>"|" {adjust(); return OR;}
<INITIAL>":=" {adjust(); return ASSIGN;}
<INITIAL>array {adjust(); return ARRAY;}
<INITIAL>if {adjust(); return IF;}
<INITIAL>then {adjust(); return THEN;}
<INITIAL>else {adjust(); return ELSE;}
<INITIAL>while {adjust(); return WHILE;}
<INITIAL>for {adjust(); return FOR;}
<INITIAL>to {adjust(); return TO;}
<INITIAL>do {adjust(); return DO;}
<INITIAL>let {adjust(); return LET;}
<INITIAL>in {adjust(); return IN;}
<INITIAL>end {adjust(); return END;}
<INITIAL>of {adjust(); return OF;}
<INITIAL>break {adjust(); return BREAK;}
<INITIAL>nil {adjust(); return NIL;}
<INITIAL>function {adjust(); return FUNCTION;}
<INITIAL>var {adjust(); return VAR;}
<INITIAL>type {adjust(); return TYPE;}

<INITIAL>[0-9]* {adjust(); yylval.ival = atoi(yytext); return INT;}
<INITIAL>[_a-zA-Z][_0-9a-zA-Z]* {adjust(); yylval.sval = String(yytext); return ID;}
<INITIAL>"\"" {adjust(); cur = 0; BEGIN STR;}
<INITIAL>[\ \t]* {adjust();}

<INITIAL><<EOF>> {adjust(); yyterminate();}
<INITIAL>. {adjust();}

<STR>\\n {charPos += yyleng; temp[cur] = '\n'; cur++;}
<STR>\\t {charPos += yyleng; temp[cur] = '\t'; cur++;}
<STR>"\\\\" {charPos += yyleng; temp[cur] = '\\'; cur++;}
<STR>\\[ \t\n\f]+\\ {charPos += yyleng;}
<STR>\\\^[A-Z] {charPos += yyleng; temp[cur] = yytext[2] - 'A' + 1; cur++;}
<STR>\\\" {charPos += yyleng; temp[cur] = '"'; cur++;}
<STR>\\[0-9]* {charPos += yyleng; temp[cur] = atoi(&yytext[1]); cur++;}
<STR>\" {charPos += yyleng; BEGIN INITIAL; 
	temp[cur] = '\0';
	yylval.sval = String(temp); 
	return STRING;
}
<STR>. {charPos += yyleng; strcpy(temp + cur, yytext); cur += yyleng;}
