// Lean compiler output
// Module: Init.Guard
// Imports: Init.Tactics Init.Conv Init.NotationExtra
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static lean_object* l_Lean_Parser_Tactic_guardHypConv___closed__1;
static lean_object* l_Lean_Parser_equalR___closed__5;
static lean_object* l_Lean_Parser_colonD___closed__2;
static lean_object* l_Lean_Parser_colonR___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_colonEqA;
static lean_object* l_Lean_Parser_Tactic_guardExpr___closed__9;
static lean_object* l_Lean_Parser_Tactic_guardHyp___closed__9;
static lean_object* l_Lean_Parser_equalD___closed__5;
static lean_object* l_Lean_Parser_Tactic_guardExprConv___closed__1;
static lean_object* l_Lean_Parser_colon___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_guardTargetConv;
static lean_object* l_Lean_Parser_colonS___closed__4;
static lean_object* l_Lean_Parser_Command_guardCmd___closed__1;
static lean_object* l_Lean_Parser_equal___closed__3;
static lean_object* l_Lean_Parser_Tactic_guardHypConv___closed__2;
static lean_object* l_Lean_Parser_Tactic_guardExpr___closed__13;
static lean_object* l_Lean_Parser_equalS___closed__2;
static lean_object* l_Lean_Parser_colonD___closed__5;
static lean_object* l_Lean_Parser_equalA___closed__2;
static lean_object* l_Lean_Parser_equalD___closed__3;
static lean_object* l_Lean_Parser_colonR___closed__2;
static lean_object* l_Lean_Parser_Tactic_guardHyp___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_guardExpr;
static lean_object* l_Lean_Parser_Command_guardCmd___closed__3;
static lean_object* l_Lean_Parser_colonS___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_colonA;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_guardExprCmd;
static lean_object* l_Lean_Parser_colon___closed__6;
static lean_object* l_Lean_Parser_Tactic_guardHypConv___closed__3;
static lean_object* l_Lean_Parser_colonEq___closed__4;
static lean_object* l_Lean_Parser_colonR___closed__4;
static lean_object* l_Lean_Parser_colonS___closed__1;
static lean_object* l_Lean_Parser_colonEqR___closed__3;
static lean_object* l_Lean_Parser_colon___closed__8;
static lean_object* l_Lean_Parser_equalR___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_colonEq;
static lean_object* l_Lean_Parser_Tactic_guardExpr___closed__10;
static lean_object* l_Lean_Parser_equalD___closed__4;
static lean_object* l_Lean_Parser_Tactic_guardExpr___closed__3;
static lean_object* l_Lean_Parser_Command_guardExprCmd___closed__7;
static lean_object* l_Lean_Parser_Tactic_guardTarget___closed__2;
static lean_object* l_Lean_Parser_Command_guardExprCmd___closed__6;
static lean_object* l_Lean_Parser_equalA___closed__4;
static lean_object* l_Lean_Parser_Tactic_guardHyp___closed__15;
static lean_object* l_Lean_Parser_Tactic_guardTarget___closed__5;
static lean_object* l_Lean_Parser_colonEqS___closed__4;
static lean_object* l_Lean_Parser_colonR___closed__1;
static lean_object* l_Lean_Parser_colonEq___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_colonD;
static lean_object* l_Lean_Parser_Command_guardExprCmd___closed__5;
static lean_object* l_Lean_Parser_colonEqD___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_colonEqR;
static lean_object* l_Lean_Parser_Tactic_guardHyp___closed__2;
static lean_object* l_Lean_Parser_colonR___closed__7;
static lean_object* l_Lean_Parser_colonEqA___closed__3;
static lean_object* l_Lean_Parser_Tactic_guardExpr___closed__8;
static lean_object* l_Lean_Parser_Tactic_guardTarget___closed__6;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_equal___closed__1;
static lean_object* l_Lean_Parser_Tactic_guardHyp___closed__7;
static lean_object* l_Lean_Parser_colonEqA___closed__5;
static lean_object* l_Lean_Parser_Tactic_guardExpr___closed__5;
static lean_object* l_Lean_Parser_Tactic_guardExpr___closed__4;
static lean_object* l_Lean_Parser_Command_guardExprCmd___closed__9;
static lean_object* l_Lean_Parser_Tactic_guardExpr___closed__12;
static lean_object* l_Lean_Parser_colonEqD___closed__1;
static lean_object* l_Lean_Parser_equalS___closed__4;
static lean_object* l_Lean_Parser_colon___closed__7;
static lean_object* l_Lean_Parser_colonA___closed__2;
static lean_object* l_Lean_Parser_colonEq___closed__1;
static lean_object* l_Lean_Parser_equalD___closed__1;
static lean_object* l_Lean_Parser_equalD___closed__2;
static lean_object* l_Lean_Parser_colonEq___closed__5;
static lean_object* l_Lean_Parser_Command_guardExprCmd___closed__3;
static lean_object* l_Lean_Parser_Command_guardCmd___closed__5;
static lean_object* l_Lean_Parser_Tactic_guardExprConv___closed__2;
static lean_object* l_Lean_Parser_Tactic_guardExpr___closed__6;
static lean_object* l_Lean_Parser_colonEqR___closed__5;
static lean_object* l_Lean_Parser_equalA___closed__5;
static lean_object* l_Lean_Parser_colonA___closed__1;
static lean_object* l_Lean_Parser_Tactic_guardHyp___closed__14;
static lean_object* l_Lean_Parser_colonD___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_guardCmd;
static lean_object* l_Lean_Parser_Tactic_guardExpr___closed__14;
LEAN_EXPORT lean_object* l_Lean_Parser_equalA;
static lean_object* l_Lean_Parser_colon___closed__4;
static lean_object* l_Lean_Parser_Command_guardExprCmd___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_equalD;
static lean_object* l_Lean_Parser_Tactic_guardTarget___closed__4;
static lean_object* l_Lean_Parser_colonEqR___closed__4;
static lean_object* l_Lean_Parser_equal___closed__2;
static lean_object* l_Lean_Parser_colonS___closed__3;
static lean_object* l_Lean_Parser_Tactic_guardHyp___closed__6;
static lean_object* l_Lean_Parser_Tactic_guardExpr___closed__11;
LEAN_EXPORT lean_object* l_Lean_Parser_colonEqD;
static lean_object* l_Lean_Parser_Tactic_guardTargetConv___closed__2;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_guardTarget;
static lean_object* l_Lean_Parser_equalS___closed__3;
static lean_object* l_Lean_Parser_Tactic_guardExpr___closed__15;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_guardHypConv;
static lean_object* l_Lean_Parser_Tactic_guardTarget___closed__7;
static lean_object* l_Lean_Parser_Tactic_guardHyp___closed__8;
static lean_object* l_Lean_Parser_Tactic_guardExpr___closed__1;
static lean_object* l_Lean_Parser_equalR___closed__4;
static lean_object* l_Lean_Parser_colonEqR___closed__1;
static lean_object* l_Lean_Parser_Tactic_guardHyp___closed__13;
static lean_object* l_Lean_Parser_colonEqS___closed__2;
static lean_object* l_Lean_Parser_Tactic_guardHyp___closed__3;
static lean_object* l_Lean_Parser_equal___closed__6;
static lean_object* l_Lean_Parser_colonEq___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_colonR;
static lean_object* l_Lean_Parser_colonEqA___closed__1;
static lean_object* l_Lean_Parser_Tactic_guardTarget___closed__3;
static lean_object* l_Lean_Parser_equalR___closed__2;
static lean_object* l_Lean_Parser_Tactic_guardHyp___closed__1;
static lean_object* l_Lean_Parser_colonEq___closed__6;
static lean_object* l_Lean_Parser_Command_guardExprCmd___closed__8;
static lean_object* l_Lean_Parser_colonR___closed__3;
static lean_object* l_Lean_Parser_Tactic_guardHyp___closed__11;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_guardHyp;
static lean_object* l_Lean_Parser_colonEqA___closed__2;
static lean_object* l_Lean_Parser_equalA___closed__3;
static lean_object* l_Lean_Parser_colonA___closed__4;
static lean_object* l_Lean_Parser_Command_guardExprCmd___closed__1;
static lean_object* l_Lean_Parser_Tactic_guardHyp___closed__12;
static lean_object* l_Lean_Parser_equal___closed__5;
static lean_object* l_Lean_Parser_Command_guardExprCmd___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_equalS;
static lean_object* l_Lean_Parser_colonEqD___closed__3;
static lean_object* l_Lean_Parser_colonEqR___closed__2;
static lean_object* l_Lean_Parser_Tactic_guardTargetConv___closed__1;
static lean_object* l_Lean_Parser_colonEqD___closed__5;
static lean_object* l_Lean_Parser_colonEqD___closed__2;
static lean_object* l_Lean_Parser_equalA___closed__1;
static lean_object* l_Lean_Parser_colonR___closed__6;
static lean_object* l_Lean_Parser_colonA___closed__3;
static lean_object* l_Lean_Parser_equalS___closed__1;
static lean_object* l_Lean_Parser_colonD___closed__4;
static lean_object* l_Lean_Parser_Tactic_guardTargetConv___closed__3;
static lean_object* l_Lean_Parser_colonD___closed__3;
static lean_object* l_Lean_Parser_colonA___closed__5;
static lean_object* l_Lean_Parser_equalR___closed__3;
static lean_object* l_Lean_Parser_Tactic_guardHyp___closed__5;
static lean_object* l_Lean_Parser_Tactic_guardTarget___closed__1;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Command_guardCmd___closed__4;
static lean_object* l_Lean_Parser_colonEqS___closed__1;
static lean_object* l_Lean_Parser_Tactic_guardExpr___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_colonS;
static lean_object* l_Lean_Parser_Command_guardCmd___closed__6;
static lean_object* l_Lean_Parser_colonEqA___closed__4;
static lean_object* l_Lean_Parser_equal___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_colon;
static lean_object* l_Lean_Parser_Tactic_guardExpr___closed__7;
static lean_object* l_Lean_Parser_colonS___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_equalR;
static lean_object* l_Lean_Parser_Tactic_guardHyp___closed__10;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_guardExprConv;
static lean_object* l_Lean_Parser_Tactic_guardExprConv___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_equal;
static lean_object* l_Lean_Parser_equalS___closed__5;
static lean_object* l_Lean_Parser_colonEqS___closed__3;
static lean_object* l_Lean_Parser_colon___closed__1;
static lean_object* l_Lean_Parser_Command_guardCmd___closed__2;
static lean_object* l_Lean_Parser_colon___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_colonEqS;
static lean_object* l_Lean_Parser_colonEqS___closed__5;
static lean_object* l_Lean_Parser_colon___closed__3;
static lean_object* _init_l_Lean_Parser_colonR___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colonR___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colonR___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("colonR", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colonR___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colonR___closed__1;
x_2 = l_Lean_Parser_colonR___closed__2;
x_3 = l_Lean_Parser_colonR___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_colonR___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" : ", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colonR___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_colonR___closed__5;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_colonR___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colonR___closed__3;
x_2 = l_Lean_Parser_colonR___closed__4;
x_3 = l_Lean_Parser_colonR___closed__6;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_colonR() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_colonR___closed__7;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colonD___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("colonD", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colonD___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colonR___closed__1;
x_2 = l_Lean_Parser_colonR___closed__2;
x_3 = l_Lean_Parser_colonD___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_colonD___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" :~ ", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colonD___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_colonD___closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_colonD___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colonD___closed__1;
x_2 = l_Lean_Parser_colonD___closed__2;
x_3 = l_Lean_Parser_colonD___closed__4;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_colonD() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_colonD___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colonS___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("colonS", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colonS___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colonR___closed__1;
x_2 = l_Lean_Parser_colonR___closed__2;
x_3 = l_Lean_Parser_colonS___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_colonS___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" :ₛ ", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colonS___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_colonS___closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_colonS___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colonS___closed__1;
x_2 = l_Lean_Parser_colonS___closed__2;
x_3 = l_Lean_Parser_colonS___closed__4;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_colonS() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_colonS___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colonA___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("colonA", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colonA___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colonR___closed__1;
x_2 = l_Lean_Parser_colonR___closed__2;
x_3 = l_Lean_Parser_colonA___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_colonA___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" :ₐ ", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colonA___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_colonA___closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_colonA___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colonA___closed__1;
x_2 = l_Lean_Parser_colonA___closed__2;
x_3 = l_Lean_Parser_colonA___closed__4;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_colonA() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_colonA___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colon___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("colon", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colon___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colonR___closed__1;
x_2 = l_Lean_Parser_colonR___closed__2;
x_3 = l_Lean_Parser_colon___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_colon___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("orelse", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colon___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_colon___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_colon___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colon___closed__4;
x_2 = l_Lean_Parser_colonS;
x_3 = l_Lean_Parser_colonA;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_colon___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colon___closed__4;
x_2 = l_Lean_Parser_colonD;
x_3 = l_Lean_Parser_colon___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_colon___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colon___closed__4;
x_2 = l_Lean_Parser_colonR;
x_3 = l_Lean_Parser_colon___closed__6;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_colon___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colon___closed__1;
x_2 = l_Lean_Parser_colon___closed__2;
x_3 = l_Lean_Parser_colon___closed__7;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_colon() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_colon___closed__8;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colonEqR___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("colonEqR", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colonEqR___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colonR___closed__1;
x_2 = l_Lean_Parser_colonR___closed__2;
x_3 = l_Lean_Parser_colonEqR___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_colonEqR___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" := ", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colonEqR___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_colonEqR___closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_colonEqR___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colonEqR___closed__1;
x_2 = l_Lean_Parser_colonEqR___closed__2;
x_3 = l_Lean_Parser_colonEqR___closed__4;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_colonEqR() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_colonEqR___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colonEqD___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("colonEqD", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colonEqD___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colonR___closed__1;
x_2 = l_Lean_Parser_colonR___closed__2;
x_3 = l_Lean_Parser_colonEqD___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_colonEqD___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" :=~ ", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colonEqD___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_colonEqD___closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_colonEqD___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colonEqD___closed__1;
x_2 = l_Lean_Parser_colonEqD___closed__2;
x_3 = l_Lean_Parser_colonEqD___closed__4;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_colonEqD() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_colonEqD___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colonEqS___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("colonEqS", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colonEqS___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colonR___closed__1;
x_2 = l_Lean_Parser_colonR___closed__2;
x_3 = l_Lean_Parser_colonEqS___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_colonEqS___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" :=ₛ ", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colonEqS___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_colonEqS___closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_colonEqS___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colonEqS___closed__1;
x_2 = l_Lean_Parser_colonEqS___closed__2;
x_3 = l_Lean_Parser_colonEqS___closed__4;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_colonEqS() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_colonEqS___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colonEqA___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("colonEqA", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colonEqA___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colonR___closed__1;
x_2 = l_Lean_Parser_colonR___closed__2;
x_3 = l_Lean_Parser_colonEqA___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_colonEqA___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" :=ₐ ", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colonEqA___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_colonEqA___closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_colonEqA___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colonEqA___closed__1;
x_2 = l_Lean_Parser_colonEqA___closed__2;
x_3 = l_Lean_Parser_colonEqA___closed__4;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_colonEqA() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_colonEqA___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colonEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("colonEq", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_colonEq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colonR___closed__1;
x_2 = l_Lean_Parser_colonR___closed__2;
x_3 = l_Lean_Parser_colonEq___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_colonEq___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colon___closed__4;
x_2 = l_Lean_Parser_colonEqS;
x_3 = l_Lean_Parser_colonEqA;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_colonEq___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colon___closed__4;
x_2 = l_Lean_Parser_colonEqD;
x_3 = l_Lean_Parser_colonEq___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_colonEq___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colon___closed__4;
x_2 = l_Lean_Parser_colonEqR;
x_3 = l_Lean_Parser_colonEq___closed__4;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_colonEq___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colonEq___closed__1;
x_2 = l_Lean_Parser_colonEq___closed__2;
x_3 = l_Lean_Parser_colonEq___closed__5;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_colonEq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_colonEq___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_equalR___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("equalR", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_equalR___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colonR___closed__1;
x_2 = l_Lean_Parser_colonR___closed__2;
x_3 = l_Lean_Parser_equalR___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_equalR___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" = ", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_equalR___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_equalR___closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_equalR___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_equalR___closed__1;
x_2 = l_Lean_Parser_equalR___closed__2;
x_3 = l_Lean_Parser_equalR___closed__4;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_equalR() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_equalR___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_equalD___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("equalD", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_equalD___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colonR___closed__1;
x_2 = l_Lean_Parser_colonR___closed__2;
x_3 = l_Lean_Parser_equalD___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_equalD___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" =~ ", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_equalD___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_equalD___closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_equalD___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_equalD___closed__1;
x_2 = l_Lean_Parser_equalD___closed__2;
x_3 = l_Lean_Parser_equalD___closed__4;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_equalD() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_equalD___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_equalS___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("equalS", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_equalS___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colonR___closed__1;
x_2 = l_Lean_Parser_colonR___closed__2;
x_3 = l_Lean_Parser_equalS___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_equalS___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" =ₛ ", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_equalS___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_equalS___closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_equalS___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_equalS___closed__1;
x_2 = l_Lean_Parser_equalS___closed__2;
x_3 = l_Lean_Parser_equalS___closed__4;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_equalS() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_equalS___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_equalA___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("equalA", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_equalA___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colonR___closed__1;
x_2 = l_Lean_Parser_colonR___closed__2;
x_3 = l_Lean_Parser_equalA___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_equalA___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" =ₐ ", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_equalA___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_equalA___closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_equalA___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_equalA___closed__1;
x_2 = l_Lean_Parser_equalA___closed__2;
x_3 = l_Lean_Parser_equalA___closed__4;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_equalA() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_equalA___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_equal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("equal", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_equal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colonR___closed__1;
x_2 = l_Lean_Parser_colonR___closed__2;
x_3 = l_Lean_Parser_equal___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_equal___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colon___closed__4;
x_2 = l_Lean_Parser_equalS;
x_3 = l_Lean_Parser_equalA;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_equal___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colon___closed__4;
x_2 = l_Lean_Parser_equalD;
x_3 = l_Lean_Parser_equal___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_equal___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_colon___closed__4;
x_2 = l_Lean_Parser_equalR;
x_3 = l_Lean_Parser_equal___closed__4;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_equal___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_equal___closed__1;
x_2 = l_Lean_Parser_equal___closed__2;
x_3 = l_Lean_Parser_equal___closed__5;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_equal() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_equal___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardExpr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("guardExpr", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardExpr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_colonR___closed__1;
x_2 = l_Lean_Parser_colonR___closed__2;
x_3 = l_Lean_Parser_Tactic_guardExpr___closed__1;
x_4 = l_Lean_Parser_Tactic_guardExpr___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardExpr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("andthen", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardExpr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_guardExpr___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardExpr___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("guard_expr ", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardExpr___closed__7() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_guardExpr___closed__6;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardExpr___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("term", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardExpr___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_guardExpr___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardExpr___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_guardExpr___closed__9;
x_2 = lean_unsigned_to_nat(51u);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardExpr___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_guardExpr___closed__5;
x_2 = l_Lean_Parser_Tactic_guardExpr___closed__7;
x_3 = l_Lean_Parser_Tactic_guardExpr___closed__10;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardExpr___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_guardExpr___closed__5;
x_2 = l_Lean_Parser_Tactic_guardExpr___closed__11;
x_3 = l_Lean_Parser_equal;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardExpr___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_guardExpr___closed__9;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardExpr___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_guardExpr___closed__5;
x_2 = l_Lean_Parser_Tactic_guardExpr___closed__12;
x_3 = l_Lean_Parser_Tactic_guardExpr___closed__13;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardExpr___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_guardExpr___closed__3;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Parser_Tactic_guardExpr___closed__14;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_guardExpr___closed__15;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardExprConv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("guardExprConv", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardExprConv___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_colonR___closed__1;
x_2 = l_Lean_Parser_colonR___closed__2;
x_3 = l_Lean_Parser_Tactic_guardExpr___closed__1;
x_4 = l_Lean_Parser_Tactic_guardExprConv___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardExprConv___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_guardExprConv___closed__2;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Parser_Tactic_guardExpr___closed__14;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardExprConv() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_guardExprConv___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardTarget___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("guardTarget", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardTarget___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_colonR___closed__1;
x_2 = l_Lean_Parser_colonR___closed__2;
x_3 = l_Lean_Parser_Tactic_guardExpr___closed__1;
x_4 = l_Lean_Parser_Tactic_guardTarget___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardTarget___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("guard_target ", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardTarget___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_guardTarget___closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardTarget___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_guardExpr___closed__5;
x_2 = l_Lean_Parser_Tactic_guardTarget___closed__4;
x_3 = l_Lean_Parser_equal;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardTarget___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_guardExpr___closed__5;
x_2 = l_Lean_Parser_Tactic_guardTarget___closed__5;
x_3 = l_Lean_Parser_Tactic_guardExpr___closed__13;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardTarget___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_guardTarget___closed__2;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Parser_Tactic_guardTarget___closed__6;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardTarget() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_guardTarget___closed__7;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardTargetConv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("guardTargetConv", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardTargetConv___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_colonR___closed__1;
x_2 = l_Lean_Parser_colonR___closed__2;
x_3 = l_Lean_Parser_Tactic_guardExpr___closed__1;
x_4 = l_Lean_Parser_Tactic_guardTargetConv___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardTargetConv___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_guardTargetConv___closed__2;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Parser_Tactic_guardTarget___closed__6;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardTargetConv() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_guardTargetConv___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardHyp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("guardHyp", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardHyp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_colonR___closed__1;
x_2 = l_Lean_Parser_colonR___closed__2;
x_3 = l_Lean_Parser_Tactic_guardExpr___closed__1;
x_4 = l_Lean_Parser_Tactic_guardHyp___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardHyp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("guard_hyp ", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardHyp___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_guardHyp___closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardHyp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_guardExpr___closed__9;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardHyp___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_guardExpr___closed__5;
x_2 = l_Lean_Parser_Tactic_guardHyp___closed__4;
x_3 = l_Lean_Parser_Tactic_guardHyp___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardHyp___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("optional", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardHyp___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_guardHyp___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardHyp___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_guardExpr___closed__5;
x_2 = l_Lean_Parser_colon;
x_3 = l_Lean_Parser_Tactic_guardExpr___closed__13;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardHyp___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_guardHyp___closed__8;
x_2 = l_Lean_Parser_Tactic_guardHyp___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardHyp___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_guardExpr___closed__5;
x_2 = l_Lean_Parser_Tactic_guardHyp___closed__6;
x_3 = l_Lean_Parser_Tactic_guardHyp___closed__10;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardHyp___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_guardExpr___closed__5;
x_2 = l_Lean_Parser_colonEq;
x_3 = l_Lean_Parser_Tactic_guardExpr___closed__13;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardHyp___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_guardHyp___closed__8;
x_2 = l_Lean_Parser_Tactic_guardHyp___closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardHyp___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_guardExpr___closed__5;
x_2 = l_Lean_Parser_Tactic_guardHyp___closed__11;
x_3 = l_Lean_Parser_Tactic_guardHyp___closed__13;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardHyp___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_guardHyp___closed__2;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Parser_Tactic_guardHyp___closed__14;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardHyp() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_guardHyp___closed__15;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardHypConv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("guardHypConv", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardHypConv___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_colonR___closed__1;
x_2 = l_Lean_Parser_colonR___closed__2;
x_3 = l_Lean_Parser_Tactic_guardExpr___closed__1;
x_4 = l_Lean_Parser_Tactic_guardHypConv___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardHypConv___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_guardHypConv___closed__2;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Parser_Tactic_guardHyp___closed__14;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardHypConv() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_guardHypConv___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Command_guardExprCmd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Command", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Command_guardExprCmd___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("guardExprCmd", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Command_guardExprCmd___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_colonR___closed__1;
x_2 = l_Lean_Parser_colonR___closed__2;
x_3 = l_Lean_Parser_Command_guardExprCmd___closed__1;
x_4 = l_Lean_Parser_Command_guardExprCmd___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Command_guardExprCmd___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("#guard_expr ", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Command_guardExprCmd___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Command_guardExprCmd___closed__4;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Command_guardExprCmd___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_guardExpr___closed__5;
x_2 = l_Lean_Parser_Command_guardExprCmd___closed__5;
x_3 = l_Lean_Parser_Tactic_guardExpr___closed__10;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Command_guardExprCmd___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_guardExpr___closed__5;
x_2 = l_Lean_Parser_Command_guardExprCmd___closed__6;
x_3 = l_Lean_Parser_equal;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Command_guardExprCmd___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_guardExpr___closed__5;
x_2 = l_Lean_Parser_Command_guardExprCmd___closed__7;
x_3 = l_Lean_Parser_Tactic_guardExpr___closed__13;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Command_guardExprCmd___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Command_guardExprCmd___closed__3;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Parser_Command_guardExprCmd___closed__8;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Command_guardExprCmd() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Command_guardExprCmd___closed__9;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Command_guardCmd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("guardCmd", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Command_guardCmd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_colonR___closed__1;
x_2 = l_Lean_Parser_colonR___closed__2;
x_3 = l_Lean_Parser_Command_guardExprCmd___closed__1;
x_4 = l_Lean_Parser_Command_guardCmd___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Command_guardCmd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("#guard ", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Command_guardCmd___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Command_guardCmd___closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Command_guardCmd___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_guardExpr___closed__5;
x_2 = l_Lean_Parser_Command_guardCmd___closed__4;
x_3 = l_Lean_Parser_Tactic_guardExpr___closed__13;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Command_guardCmd___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Command_guardCmd___closed__2;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Parser_Command_guardCmd___closed__5;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Command_guardCmd() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Command_guardCmd___closed__6;
return x_1;
}
}
lean_object* initialize_Init_Tactics(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Conv(uint8_t builtin, lean_object*);
lean_object* initialize_Init_NotationExtra(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Guard(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Tactics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Conv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_NotationExtra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_colonR___closed__1 = _init_l_Lean_Parser_colonR___closed__1();
lean_mark_persistent(l_Lean_Parser_colonR___closed__1);
l_Lean_Parser_colonR___closed__2 = _init_l_Lean_Parser_colonR___closed__2();
lean_mark_persistent(l_Lean_Parser_colonR___closed__2);
l_Lean_Parser_colonR___closed__3 = _init_l_Lean_Parser_colonR___closed__3();
lean_mark_persistent(l_Lean_Parser_colonR___closed__3);
l_Lean_Parser_colonR___closed__4 = _init_l_Lean_Parser_colonR___closed__4();
lean_mark_persistent(l_Lean_Parser_colonR___closed__4);
l_Lean_Parser_colonR___closed__5 = _init_l_Lean_Parser_colonR___closed__5();
lean_mark_persistent(l_Lean_Parser_colonR___closed__5);
l_Lean_Parser_colonR___closed__6 = _init_l_Lean_Parser_colonR___closed__6();
lean_mark_persistent(l_Lean_Parser_colonR___closed__6);
l_Lean_Parser_colonR___closed__7 = _init_l_Lean_Parser_colonR___closed__7();
lean_mark_persistent(l_Lean_Parser_colonR___closed__7);
l_Lean_Parser_colonR = _init_l_Lean_Parser_colonR();
lean_mark_persistent(l_Lean_Parser_colonR);
l_Lean_Parser_colonD___closed__1 = _init_l_Lean_Parser_colonD___closed__1();
lean_mark_persistent(l_Lean_Parser_colonD___closed__1);
l_Lean_Parser_colonD___closed__2 = _init_l_Lean_Parser_colonD___closed__2();
lean_mark_persistent(l_Lean_Parser_colonD___closed__2);
l_Lean_Parser_colonD___closed__3 = _init_l_Lean_Parser_colonD___closed__3();
lean_mark_persistent(l_Lean_Parser_colonD___closed__3);
l_Lean_Parser_colonD___closed__4 = _init_l_Lean_Parser_colonD___closed__4();
lean_mark_persistent(l_Lean_Parser_colonD___closed__4);
l_Lean_Parser_colonD___closed__5 = _init_l_Lean_Parser_colonD___closed__5();
lean_mark_persistent(l_Lean_Parser_colonD___closed__5);
l_Lean_Parser_colonD = _init_l_Lean_Parser_colonD();
lean_mark_persistent(l_Lean_Parser_colonD);
l_Lean_Parser_colonS___closed__1 = _init_l_Lean_Parser_colonS___closed__1();
lean_mark_persistent(l_Lean_Parser_colonS___closed__1);
l_Lean_Parser_colonS___closed__2 = _init_l_Lean_Parser_colonS___closed__2();
lean_mark_persistent(l_Lean_Parser_colonS___closed__2);
l_Lean_Parser_colonS___closed__3 = _init_l_Lean_Parser_colonS___closed__3();
lean_mark_persistent(l_Lean_Parser_colonS___closed__3);
l_Lean_Parser_colonS___closed__4 = _init_l_Lean_Parser_colonS___closed__4();
lean_mark_persistent(l_Lean_Parser_colonS___closed__4);
l_Lean_Parser_colonS___closed__5 = _init_l_Lean_Parser_colonS___closed__5();
lean_mark_persistent(l_Lean_Parser_colonS___closed__5);
l_Lean_Parser_colonS = _init_l_Lean_Parser_colonS();
lean_mark_persistent(l_Lean_Parser_colonS);
l_Lean_Parser_colonA___closed__1 = _init_l_Lean_Parser_colonA___closed__1();
lean_mark_persistent(l_Lean_Parser_colonA___closed__1);
l_Lean_Parser_colonA___closed__2 = _init_l_Lean_Parser_colonA___closed__2();
lean_mark_persistent(l_Lean_Parser_colonA___closed__2);
l_Lean_Parser_colonA___closed__3 = _init_l_Lean_Parser_colonA___closed__3();
lean_mark_persistent(l_Lean_Parser_colonA___closed__3);
l_Lean_Parser_colonA___closed__4 = _init_l_Lean_Parser_colonA___closed__4();
lean_mark_persistent(l_Lean_Parser_colonA___closed__4);
l_Lean_Parser_colonA___closed__5 = _init_l_Lean_Parser_colonA___closed__5();
lean_mark_persistent(l_Lean_Parser_colonA___closed__5);
l_Lean_Parser_colonA = _init_l_Lean_Parser_colonA();
lean_mark_persistent(l_Lean_Parser_colonA);
l_Lean_Parser_colon___closed__1 = _init_l_Lean_Parser_colon___closed__1();
lean_mark_persistent(l_Lean_Parser_colon___closed__1);
l_Lean_Parser_colon___closed__2 = _init_l_Lean_Parser_colon___closed__2();
lean_mark_persistent(l_Lean_Parser_colon___closed__2);
l_Lean_Parser_colon___closed__3 = _init_l_Lean_Parser_colon___closed__3();
lean_mark_persistent(l_Lean_Parser_colon___closed__3);
l_Lean_Parser_colon___closed__4 = _init_l_Lean_Parser_colon___closed__4();
lean_mark_persistent(l_Lean_Parser_colon___closed__4);
l_Lean_Parser_colon___closed__5 = _init_l_Lean_Parser_colon___closed__5();
lean_mark_persistent(l_Lean_Parser_colon___closed__5);
l_Lean_Parser_colon___closed__6 = _init_l_Lean_Parser_colon___closed__6();
lean_mark_persistent(l_Lean_Parser_colon___closed__6);
l_Lean_Parser_colon___closed__7 = _init_l_Lean_Parser_colon___closed__7();
lean_mark_persistent(l_Lean_Parser_colon___closed__7);
l_Lean_Parser_colon___closed__8 = _init_l_Lean_Parser_colon___closed__8();
lean_mark_persistent(l_Lean_Parser_colon___closed__8);
l_Lean_Parser_colon = _init_l_Lean_Parser_colon();
lean_mark_persistent(l_Lean_Parser_colon);
l_Lean_Parser_colonEqR___closed__1 = _init_l_Lean_Parser_colonEqR___closed__1();
lean_mark_persistent(l_Lean_Parser_colonEqR___closed__1);
l_Lean_Parser_colonEqR___closed__2 = _init_l_Lean_Parser_colonEqR___closed__2();
lean_mark_persistent(l_Lean_Parser_colonEqR___closed__2);
l_Lean_Parser_colonEqR___closed__3 = _init_l_Lean_Parser_colonEqR___closed__3();
lean_mark_persistent(l_Lean_Parser_colonEqR___closed__3);
l_Lean_Parser_colonEqR___closed__4 = _init_l_Lean_Parser_colonEqR___closed__4();
lean_mark_persistent(l_Lean_Parser_colonEqR___closed__4);
l_Lean_Parser_colonEqR___closed__5 = _init_l_Lean_Parser_colonEqR___closed__5();
lean_mark_persistent(l_Lean_Parser_colonEqR___closed__5);
l_Lean_Parser_colonEqR = _init_l_Lean_Parser_colonEqR();
lean_mark_persistent(l_Lean_Parser_colonEqR);
l_Lean_Parser_colonEqD___closed__1 = _init_l_Lean_Parser_colonEqD___closed__1();
lean_mark_persistent(l_Lean_Parser_colonEqD___closed__1);
l_Lean_Parser_colonEqD___closed__2 = _init_l_Lean_Parser_colonEqD___closed__2();
lean_mark_persistent(l_Lean_Parser_colonEqD___closed__2);
l_Lean_Parser_colonEqD___closed__3 = _init_l_Lean_Parser_colonEqD___closed__3();
lean_mark_persistent(l_Lean_Parser_colonEqD___closed__3);
l_Lean_Parser_colonEqD___closed__4 = _init_l_Lean_Parser_colonEqD___closed__4();
lean_mark_persistent(l_Lean_Parser_colonEqD___closed__4);
l_Lean_Parser_colonEqD___closed__5 = _init_l_Lean_Parser_colonEqD___closed__5();
lean_mark_persistent(l_Lean_Parser_colonEqD___closed__5);
l_Lean_Parser_colonEqD = _init_l_Lean_Parser_colonEqD();
lean_mark_persistent(l_Lean_Parser_colonEqD);
l_Lean_Parser_colonEqS___closed__1 = _init_l_Lean_Parser_colonEqS___closed__1();
lean_mark_persistent(l_Lean_Parser_colonEqS___closed__1);
l_Lean_Parser_colonEqS___closed__2 = _init_l_Lean_Parser_colonEqS___closed__2();
lean_mark_persistent(l_Lean_Parser_colonEqS___closed__2);
l_Lean_Parser_colonEqS___closed__3 = _init_l_Lean_Parser_colonEqS___closed__3();
lean_mark_persistent(l_Lean_Parser_colonEqS___closed__3);
l_Lean_Parser_colonEqS___closed__4 = _init_l_Lean_Parser_colonEqS___closed__4();
lean_mark_persistent(l_Lean_Parser_colonEqS___closed__4);
l_Lean_Parser_colonEqS___closed__5 = _init_l_Lean_Parser_colonEqS___closed__5();
lean_mark_persistent(l_Lean_Parser_colonEqS___closed__5);
l_Lean_Parser_colonEqS = _init_l_Lean_Parser_colonEqS();
lean_mark_persistent(l_Lean_Parser_colonEqS);
l_Lean_Parser_colonEqA___closed__1 = _init_l_Lean_Parser_colonEqA___closed__1();
lean_mark_persistent(l_Lean_Parser_colonEqA___closed__1);
l_Lean_Parser_colonEqA___closed__2 = _init_l_Lean_Parser_colonEqA___closed__2();
lean_mark_persistent(l_Lean_Parser_colonEqA___closed__2);
l_Lean_Parser_colonEqA___closed__3 = _init_l_Lean_Parser_colonEqA___closed__3();
lean_mark_persistent(l_Lean_Parser_colonEqA___closed__3);
l_Lean_Parser_colonEqA___closed__4 = _init_l_Lean_Parser_colonEqA___closed__4();
lean_mark_persistent(l_Lean_Parser_colonEqA___closed__4);
l_Lean_Parser_colonEqA___closed__5 = _init_l_Lean_Parser_colonEqA___closed__5();
lean_mark_persistent(l_Lean_Parser_colonEqA___closed__5);
l_Lean_Parser_colonEqA = _init_l_Lean_Parser_colonEqA();
lean_mark_persistent(l_Lean_Parser_colonEqA);
l_Lean_Parser_colonEq___closed__1 = _init_l_Lean_Parser_colonEq___closed__1();
lean_mark_persistent(l_Lean_Parser_colonEq___closed__1);
l_Lean_Parser_colonEq___closed__2 = _init_l_Lean_Parser_colonEq___closed__2();
lean_mark_persistent(l_Lean_Parser_colonEq___closed__2);
l_Lean_Parser_colonEq___closed__3 = _init_l_Lean_Parser_colonEq___closed__3();
lean_mark_persistent(l_Lean_Parser_colonEq___closed__3);
l_Lean_Parser_colonEq___closed__4 = _init_l_Lean_Parser_colonEq___closed__4();
lean_mark_persistent(l_Lean_Parser_colonEq___closed__4);
l_Lean_Parser_colonEq___closed__5 = _init_l_Lean_Parser_colonEq___closed__5();
lean_mark_persistent(l_Lean_Parser_colonEq___closed__5);
l_Lean_Parser_colonEq___closed__6 = _init_l_Lean_Parser_colonEq___closed__6();
lean_mark_persistent(l_Lean_Parser_colonEq___closed__6);
l_Lean_Parser_colonEq = _init_l_Lean_Parser_colonEq();
lean_mark_persistent(l_Lean_Parser_colonEq);
l_Lean_Parser_equalR___closed__1 = _init_l_Lean_Parser_equalR___closed__1();
lean_mark_persistent(l_Lean_Parser_equalR___closed__1);
l_Lean_Parser_equalR___closed__2 = _init_l_Lean_Parser_equalR___closed__2();
lean_mark_persistent(l_Lean_Parser_equalR___closed__2);
l_Lean_Parser_equalR___closed__3 = _init_l_Lean_Parser_equalR___closed__3();
lean_mark_persistent(l_Lean_Parser_equalR___closed__3);
l_Lean_Parser_equalR___closed__4 = _init_l_Lean_Parser_equalR___closed__4();
lean_mark_persistent(l_Lean_Parser_equalR___closed__4);
l_Lean_Parser_equalR___closed__5 = _init_l_Lean_Parser_equalR___closed__5();
lean_mark_persistent(l_Lean_Parser_equalR___closed__5);
l_Lean_Parser_equalR = _init_l_Lean_Parser_equalR();
lean_mark_persistent(l_Lean_Parser_equalR);
l_Lean_Parser_equalD___closed__1 = _init_l_Lean_Parser_equalD___closed__1();
lean_mark_persistent(l_Lean_Parser_equalD___closed__1);
l_Lean_Parser_equalD___closed__2 = _init_l_Lean_Parser_equalD___closed__2();
lean_mark_persistent(l_Lean_Parser_equalD___closed__2);
l_Lean_Parser_equalD___closed__3 = _init_l_Lean_Parser_equalD___closed__3();
lean_mark_persistent(l_Lean_Parser_equalD___closed__3);
l_Lean_Parser_equalD___closed__4 = _init_l_Lean_Parser_equalD___closed__4();
lean_mark_persistent(l_Lean_Parser_equalD___closed__4);
l_Lean_Parser_equalD___closed__5 = _init_l_Lean_Parser_equalD___closed__5();
lean_mark_persistent(l_Lean_Parser_equalD___closed__5);
l_Lean_Parser_equalD = _init_l_Lean_Parser_equalD();
lean_mark_persistent(l_Lean_Parser_equalD);
l_Lean_Parser_equalS___closed__1 = _init_l_Lean_Parser_equalS___closed__1();
lean_mark_persistent(l_Lean_Parser_equalS___closed__1);
l_Lean_Parser_equalS___closed__2 = _init_l_Lean_Parser_equalS___closed__2();
lean_mark_persistent(l_Lean_Parser_equalS___closed__2);
l_Lean_Parser_equalS___closed__3 = _init_l_Lean_Parser_equalS___closed__3();
lean_mark_persistent(l_Lean_Parser_equalS___closed__3);
l_Lean_Parser_equalS___closed__4 = _init_l_Lean_Parser_equalS___closed__4();
lean_mark_persistent(l_Lean_Parser_equalS___closed__4);
l_Lean_Parser_equalS___closed__5 = _init_l_Lean_Parser_equalS___closed__5();
lean_mark_persistent(l_Lean_Parser_equalS___closed__5);
l_Lean_Parser_equalS = _init_l_Lean_Parser_equalS();
lean_mark_persistent(l_Lean_Parser_equalS);
l_Lean_Parser_equalA___closed__1 = _init_l_Lean_Parser_equalA___closed__1();
lean_mark_persistent(l_Lean_Parser_equalA___closed__1);
l_Lean_Parser_equalA___closed__2 = _init_l_Lean_Parser_equalA___closed__2();
lean_mark_persistent(l_Lean_Parser_equalA___closed__2);
l_Lean_Parser_equalA___closed__3 = _init_l_Lean_Parser_equalA___closed__3();
lean_mark_persistent(l_Lean_Parser_equalA___closed__3);
l_Lean_Parser_equalA___closed__4 = _init_l_Lean_Parser_equalA___closed__4();
lean_mark_persistent(l_Lean_Parser_equalA___closed__4);
l_Lean_Parser_equalA___closed__5 = _init_l_Lean_Parser_equalA___closed__5();
lean_mark_persistent(l_Lean_Parser_equalA___closed__5);
l_Lean_Parser_equalA = _init_l_Lean_Parser_equalA();
lean_mark_persistent(l_Lean_Parser_equalA);
l_Lean_Parser_equal___closed__1 = _init_l_Lean_Parser_equal___closed__1();
lean_mark_persistent(l_Lean_Parser_equal___closed__1);
l_Lean_Parser_equal___closed__2 = _init_l_Lean_Parser_equal___closed__2();
lean_mark_persistent(l_Lean_Parser_equal___closed__2);
l_Lean_Parser_equal___closed__3 = _init_l_Lean_Parser_equal___closed__3();
lean_mark_persistent(l_Lean_Parser_equal___closed__3);
l_Lean_Parser_equal___closed__4 = _init_l_Lean_Parser_equal___closed__4();
lean_mark_persistent(l_Lean_Parser_equal___closed__4);
l_Lean_Parser_equal___closed__5 = _init_l_Lean_Parser_equal___closed__5();
lean_mark_persistent(l_Lean_Parser_equal___closed__5);
l_Lean_Parser_equal___closed__6 = _init_l_Lean_Parser_equal___closed__6();
lean_mark_persistent(l_Lean_Parser_equal___closed__6);
l_Lean_Parser_equal = _init_l_Lean_Parser_equal();
lean_mark_persistent(l_Lean_Parser_equal);
l_Lean_Parser_Tactic_guardExpr___closed__1 = _init_l_Lean_Parser_Tactic_guardExpr___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_guardExpr___closed__1);
l_Lean_Parser_Tactic_guardExpr___closed__2 = _init_l_Lean_Parser_Tactic_guardExpr___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_guardExpr___closed__2);
l_Lean_Parser_Tactic_guardExpr___closed__3 = _init_l_Lean_Parser_Tactic_guardExpr___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_guardExpr___closed__3);
l_Lean_Parser_Tactic_guardExpr___closed__4 = _init_l_Lean_Parser_Tactic_guardExpr___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_guardExpr___closed__4);
l_Lean_Parser_Tactic_guardExpr___closed__5 = _init_l_Lean_Parser_Tactic_guardExpr___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_guardExpr___closed__5);
l_Lean_Parser_Tactic_guardExpr___closed__6 = _init_l_Lean_Parser_Tactic_guardExpr___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_guardExpr___closed__6);
l_Lean_Parser_Tactic_guardExpr___closed__7 = _init_l_Lean_Parser_Tactic_guardExpr___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_guardExpr___closed__7);
l_Lean_Parser_Tactic_guardExpr___closed__8 = _init_l_Lean_Parser_Tactic_guardExpr___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_guardExpr___closed__8);
l_Lean_Parser_Tactic_guardExpr___closed__9 = _init_l_Lean_Parser_Tactic_guardExpr___closed__9();
lean_mark_persistent(l_Lean_Parser_Tactic_guardExpr___closed__9);
l_Lean_Parser_Tactic_guardExpr___closed__10 = _init_l_Lean_Parser_Tactic_guardExpr___closed__10();
lean_mark_persistent(l_Lean_Parser_Tactic_guardExpr___closed__10);
l_Lean_Parser_Tactic_guardExpr___closed__11 = _init_l_Lean_Parser_Tactic_guardExpr___closed__11();
lean_mark_persistent(l_Lean_Parser_Tactic_guardExpr___closed__11);
l_Lean_Parser_Tactic_guardExpr___closed__12 = _init_l_Lean_Parser_Tactic_guardExpr___closed__12();
lean_mark_persistent(l_Lean_Parser_Tactic_guardExpr___closed__12);
l_Lean_Parser_Tactic_guardExpr___closed__13 = _init_l_Lean_Parser_Tactic_guardExpr___closed__13();
lean_mark_persistent(l_Lean_Parser_Tactic_guardExpr___closed__13);
l_Lean_Parser_Tactic_guardExpr___closed__14 = _init_l_Lean_Parser_Tactic_guardExpr___closed__14();
lean_mark_persistent(l_Lean_Parser_Tactic_guardExpr___closed__14);
l_Lean_Parser_Tactic_guardExpr___closed__15 = _init_l_Lean_Parser_Tactic_guardExpr___closed__15();
lean_mark_persistent(l_Lean_Parser_Tactic_guardExpr___closed__15);
l_Lean_Parser_Tactic_guardExpr = _init_l_Lean_Parser_Tactic_guardExpr();
lean_mark_persistent(l_Lean_Parser_Tactic_guardExpr);
l_Lean_Parser_Tactic_guardExprConv___closed__1 = _init_l_Lean_Parser_Tactic_guardExprConv___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_guardExprConv___closed__1);
l_Lean_Parser_Tactic_guardExprConv___closed__2 = _init_l_Lean_Parser_Tactic_guardExprConv___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_guardExprConv___closed__2);
l_Lean_Parser_Tactic_guardExprConv___closed__3 = _init_l_Lean_Parser_Tactic_guardExprConv___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_guardExprConv___closed__3);
l_Lean_Parser_Tactic_guardExprConv = _init_l_Lean_Parser_Tactic_guardExprConv();
lean_mark_persistent(l_Lean_Parser_Tactic_guardExprConv);
l_Lean_Parser_Tactic_guardTarget___closed__1 = _init_l_Lean_Parser_Tactic_guardTarget___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_guardTarget___closed__1);
l_Lean_Parser_Tactic_guardTarget___closed__2 = _init_l_Lean_Parser_Tactic_guardTarget___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_guardTarget___closed__2);
l_Lean_Parser_Tactic_guardTarget___closed__3 = _init_l_Lean_Parser_Tactic_guardTarget___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_guardTarget___closed__3);
l_Lean_Parser_Tactic_guardTarget___closed__4 = _init_l_Lean_Parser_Tactic_guardTarget___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_guardTarget___closed__4);
l_Lean_Parser_Tactic_guardTarget___closed__5 = _init_l_Lean_Parser_Tactic_guardTarget___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_guardTarget___closed__5);
l_Lean_Parser_Tactic_guardTarget___closed__6 = _init_l_Lean_Parser_Tactic_guardTarget___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_guardTarget___closed__6);
l_Lean_Parser_Tactic_guardTarget___closed__7 = _init_l_Lean_Parser_Tactic_guardTarget___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_guardTarget___closed__7);
l_Lean_Parser_Tactic_guardTarget = _init_l_Lean_Parser_Tactic_guardTarget();
lean_mark_persistent(l_Lean_Parser_Tactic_guardTarget);
l_Lean_Parser_Tactic_guardTargetConv___closed__1 = _init_l_Lean_Parser_Tactic_guardTargetConv___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_guardTargetConv___closed__1);
l_Lean_Parser_Tactic_guardTargetConv___closed__2 = _init_l_Lean_Parser_Tactic_guardTargetConv___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_guardTargetConv___closed__2);
l_Lean_Parser_Tactic_guardTargetConv___closed__3 = _init_l_Lean_Parser_Tactic_guardTargetConv___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_guardTargetConv___closed__3);
l_Lean_Parser_Tactic_guardTargetConv = _init_l_Lean_Parser_Tactic_guardTargetConv();
lean_mark_persistent(l_Lean_Parser_Tactic_guardTargetConv);
l_Lean_Parser_Tactic_guardHyp___closed__1 = _init_l_Lean_Parser_Tactic_guardHyp___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_guardHyp___closed__1);
l_Lean_Parser_Tactic_guardHyp___closed__2 = _init_l_Lean_Parser_Tactic_guardHyp___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_guardHyp___closed__2);
l_Lean_Parser_Tactic_guardHyp___closed__3 = _init_l_Lean_Parser_Tactic_guardHyp___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_guardHyp___closed__3);
l_Lean_Parser_Tactic_guardHyp___closed__4 = _init_l_Lean_Parser_Tactic_guardHyp___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_guardHyp___closed__4);
l_Lean_Parser_Tactic_guardHyp___closed__5 = _init_l_Lean_Parser_Tactic_guardHyp___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_guardHyp___closed__5);
l_Lean_Parser_Tactic_guardHyp___closed__6 = _init_l_Lean_Parser_Tactic_guardHyp___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_guardHyp___closed__6);
l_Lean_Parser_Tactic_guardHyp___closed__7 = _init_l_Lean_Parser_Tactic_guardHyp___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_guardHyp___closed__7);
l_Lean_Parser_Tactic_guardHyp___closed__8 = _init_l_Lean_Parser_Tactic_guardHyp___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_guardHyp___closed__8);
l_Lean_Parser_Tactic_guardHyp___closed__9 = _init_l_Lean_Parser_Tactic_guardHyp___closed__9();
lean_mark_persistent(l_Lean_Parser_Tactic_guardHyp___closed__9);
l_Lean_Parser_Tactic_guardHyp___closed__10 = _init_l_Lean_Parser_Tactic_guardHyp___closed__10();
lean_mark_persistent(l_Lean_Parser_Tactic_guardHyp___closed__10);
l_Lean_Parser_Tactic_guardHyp___closed__11 = _init_l_Lean_Parser_Tactic_guardHyp___closed__11();
lean_mark_persistent(l_Lean_Parser_Tactic_guardHyp___closed__11);
l_Lean_Parser_Tactic_guardHyp___closed__12 = _init_l_Lean_Parser_Tactic_guardHyp___closed__12();
lean_mark_persistent(l_Lean_Parser_Tactic_guardHyp___closed__12);
l_Lean_Parser_Tactic_guardHyp___closed__13 = _init_l_Lean_Parser_Tactic_guardHyp___closed__13();
lean_mark_persistent(l_Lean_Parser_Tactic_guardHyp___closed__13);
l_Lean_Parser_Tactic_guardHyp___closed__14 = _init_l_Lean_Parser_Tactic_guardHyp___closed__14();
lean_mark_persistent(l_Lean_Parser_Tactic_guardHyp___closed__14);
l_Lean_Parser_Tactic_guardHyp___closed__15 = _init_l_Lean_Parser_Tactic_guardHyp___closed__15();
lean_mark_persistent(l_Lean_Parser_Tactic_guardHyp___closed__15);
l_Lean_Parser_Tactic_guardHyp = _init_l_Lean_Parser_Tactic_guardHyp();
lean_mark_persistent(l_Lean_Parser_Tactic_guardHyp);
l_Lean_Parser_Tactic_guardHypConv___closed__1 = _init_l_Lean_Parser_Tactic_guardHypConv___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_guardHypConv___closed__1);
l_Lean_Parser_Tactic_guardHypConv___closed__2 = _init_l_Lean_Parser_Tactic_guardHypConv___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_guardHypConv___closed__2);
l_Lean_Parser_Tactic_guardHypConv___closed__3 = _init_l_Lean_Parser_Tactic_guardHypConv___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_guardHypConv___closed__3);
l_Lean_Parser_Tactic_guardHypConv = _init_l_Lean_Parser_Tactic_guardHypConv();
lean_mark_persistent(l_Lean_Parser_Tactic_guardHypConv);
l_Lean_Parser_Command_guardExprCmd___closed__1 = _init_l_Lean_Parser_Command_guardExprCmd___closed__1();
lean_mark_persistent(l_Lean_Parser_Command_guardExprCmd___closed__1);
l_Lean_Parser_Command_guardExprCmd___closed__2 = _init_l_Lean_Parser_Command_guardExprCmd___closed__2();
lean_mark_persistent(l_Lean_Parser_Command_guardExprCmd___closed__2);
l_Lean_Parser_Command_guardExprCmd___closed__3 = _init_l_Lean_Parser_Command_guardExprCmd___closed__3();
lean_mark_persistent(l_Lean_Parser_Command_guardExprCmd___closed__3);
l_Lean_Parser_Command_guardExprCmd___closed__4 = _init_l_Lean_Parser_Command_guardExprCmd___closed__4();
lean_mark_persistent(l_Lean_Parser_Command_guardExprCmd___closed__4);
l_Lean_Parser_Command_guardExprCmd___closed__5 = _init_l_Lean_Parser_Command_guardExprCmd___closed__5();
lean_mark_persistent(l_Lean_Parser_Command_guardExprCmd___closed__5);
l_Lean_Parser_Command_guardExprCmd___closed__6 = _init_l_Lean_Parser_Command_guardExprCmd___closed__6();
lean_mark_persistent(l_Lean_Parser_Command_guardExprCmd___closed__6);
l_Lean_Parser_Command_guardExprCmd___closed__7 = _init_l_Lean_Parser_Command_guardExprCmd___closed__7();
lean_mark_persistent(l_Lean_Parser_Command_guardExprCmd___closed__7);
l_Lean_Parser_Command_guardExprCmd___closed__8 = _init_l_Lean_Parser_Command_guardExprCmd___closed__8();
lean_mark_persistent(l_Lean_Parser_Command_guardExprCmd___closed__8);
l_Lean_Parser_Command_guardExprCmd___closed__9 = _init_l_Lean_Parser_Command_guardExprCmd___closed__9();
lean_mark_persistent(l_Lean_Parser_Command_guardExprCmd___closed__9);
l_Lean_Parser_Command_guardExprCmd = _init_l_Lean_Parser_Command_guardExprCmd();
lean_mark_persistent(l_Lean_Parser_Command_guardExprCmd);
l_Lean_Parser_Command_guardCmd___closed__1 = _init_l_Lean_Parser_Command_guardCmd___closed__1();
lean_mark_persistent(l_Lean_Parser_Command_guardCmd___closed__1);
l_Lean_Parser_Command_guardCmd___closed__2 = _init_l_Lean_Parser_Command_guardCmd___closed__2();
lean_mark_persistent(l_Lean_Parser_Command_guardCmd___closed__2);
l_Lean_Parser_Command_guardCmd___closed__3 = _init_l_Lean_Parser_Command_guardCmd___closed__3();
lean_mark_persistent(l_Lean_Parser_Command_guardCmd___closed__3);
l_Lean_Parser_Command_guardCmd___closed__4 = _init_l_Lean_Parser_Command_guardCmd___closed__4();
lean_mark_persistent(l_Lean_Parser_Command_guardCmd___closed__4);
l_Lean_Parser_Command_guardCmd___closed__5 = _init_l_Lean_Parser_Command_guardCmd___closed__5();
lean_mark_persistent(l_Lean_Parser_Command_guardCmd___closed__5);
l_Lean_Parser_Command_guardCmd___closed__6 = _init_l_Lean_Parser_Command_guardCmd___closed__6();
lean_mark_persistent(l_Lean_Parser_Command_guardCmd___closed__6);
l_Lean_Parser_Command_guardCmd = _init_l_Lean_Parser_Command_guardCmd();
lean_mark_persistent(l_Lean_Parser_Command_guardCmd);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
