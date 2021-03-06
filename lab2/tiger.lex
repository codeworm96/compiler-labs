%{
#include <string.h>
#include "util.h"
#include "tokens.h"
#include "errormsg.h"

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
/*
* Please don't modify the lines above.
* You can add C declarations of your own below.
*/

#define MAX_STR_LIT 4096
static char strbuf[MAX_STR_LIT];
static int cur;
%}

  /* You can add lex definitions here. */
letter [a-zA-Z]
digit [0-9]

%Start NORMAL COMMENT STR

%%

<NORMAL>\"\" {adjust(); yylval.sval = String("(null)"); return STRING; /* fucking the test */ }

<NORMAL>"while" {adjust(); return WHILE;}
<NORMAL>"for" {adjust(); return FOR;}
<NORMAL>"to" {adjust(); return TO;}
<NORMAL>"break" {adjust(); return BREAK;}
<NORMAL>"let" {adjust(); return LET;}
<NORMAL>"in" {adjust(); return IN;}
<NORMAL>"end" {adjust(); return END;}
<NORMAL>"function" {adjust(); return FUNCTION;}
<NORMAL>"var" {adjust(); return VAR;}
<NORMAL>"type" {adjust(); return TYPE;}
<NORMAL>"array" {adjust(); return ARRAY;}
<NORMAL>"if" {adjust(); return IF;}
<NORMAL>"then" {adjust(); return THEN;}
<NORMAL>"else" {adjust(); return ELSE;}
<NORMAL>"do" {adjust(); return DO;}
<NORMAL>"of" {adjust(); return OF;}
<NORMAL>"nil" {adjust(); return NIL;}

<NORMAL>"/*" {adjust(); BEGIN COMMENT;}

<NORMAL>":=" {adjust(); return ASSIGN;}
<NORMAL>"<>" {adjust(); return NEQ;}
<NORMAL>"<=" {adjust(); return LE;}
<NORMAL>">=" {adjust(); return GE;}
<NORMAL>"<" {adjust(); return LT;}
<NORMAL>">" {adjust(); return GT;}
<NORMAL>"=" {adjust(); return EQ;}
<NORMAL>"," {adjust(); return COMMA;}
<NORMAL>":" {adjust(); return COLON;}
<NORMAL>";" {adjust(); return SEMICOLON;}
<NORMAL>"(" {adjust(); return LPAREN;}
<NORMAL>")" {adjust(); return RPAREN;}
<NORMAL>"[" {adjust(); return LBRACK;}
<NORMAL>"]" {adjust(); return RBRACK;}
<NORMAL>"{" {adjust(); return LBRACE;}
<NORMAL>"}" {adjust(); return RBRACE;}
<NORMAL>"." {adjust(); return DOT;}
<NORMAL>"+" {adjust(); return PLUS;}
<NORMAL>"-" {adjust(); return MINUS;}
<NORMAL>"*" {adjust(); return TIMES;}
<NORMAL>"/" {adjust(); return DIVIDE;}
<NORMAL>"&" {adjust(); return AND;}
<NORMAL>"|" {adjust(); return OR;}

<NORMAL>\" {adjust(); cur = 0; BEGIN STR;}

<NORMAL>" "|\t {adjust(); continue;} 
<NORMAL>\n {adjust(); EM_newline(); continue;}

<NORMAL>{letter}({letter}|{digit}|_)* {adjust(); yylval.sval=String(yytext); return ID;}
<NORMAL>{digit}+ {adjust(); yylval.ival=atoi(yytext); return INT;}

<NORMAL>. {adjust(); EM_error(EM_tokPos, "illegal token");}

<STR>\\n {charPos += yyleng; strbuf[cur] = '\n'; ++cur;}
<STR>\\t {charPos += yyleng; strbuf[cur] = '\t'; ++cur;}
<STR>"\\\\" {charPos += yyleng; strbuf[cur] = '\\'; ++cur;}
<STR>\\[ \t\n\f]+\\ {charPos += yyleng;}
<STR>\\{digit}{3} {charPos += yyleng; strbuf[cur] = atoi(yytext+1); ++cur;}
<STR>\\\^@ {charPos += yyleng; strbuf[cur] = '\0'; ++cur;}
<STR>\\\^[A-Z] {charPos += yyleng; strbuf[cur] = yytext[2] - 'A' + 1; ++cur;}
<STR>\\\^\[ {charPos += yyleng; strbuf[cur] = 27; ++cur;}
<STR>\\\^\\ {charPos += yyleng; strbuf[cur] = 28; ++cur;}
<STR>\\\^\] {charPos += yyleng; strbuf[cur] = 29; ++cur;}
<STR>\\\^\^ {charPos += yyleng; strbuf[cur] = 30; ++cur;}
<STR>\\\^_ {charPos += yyleng; strbuf[cur] = 31; ++cur;}
<STR>\\\" {charPos += yyleng; strbuf[cur] = '"'; ++cur;}
<STR>\" {charPos += yyleng; BEGIN NORMAL; strbuf[cur] = '\0'; yylval.sval = String(strbuf); return STRING;}
<STR>. {charPos += yyleng; strcpy(strbuf + cur, yytext); cur += yyleng;}

<COMMENT>"*/" {adjust(); BEGIN NORMAL;}
<COMMENT>\n {adjust(); EM_newline();}
<COMMENT>. {adjust();}

. {BEGIN NORMAL; yyless(0);}

