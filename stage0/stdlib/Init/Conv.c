// Lean compiler output
// Module: Init.Conv
// Imports: Init.Notation
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
static lean_object* l_Lean_Parser_Tactic_convCongr___closed__3;
static lean_object* l_Lean_Parser_Tactic_convSeq1Indented___closed__12;
static lean_object* l_Lean_Parser_Tactic_convCongr___closed__5;
static lean_object* l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__12;
static lean_object* l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__10;
static lean_object* l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__20;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Tactic_conv_quot___closed__14;
static lean_object* l_Lean_Parser_Tactic_convCongr___closed__1;
static lean_object* l_Lean_Parser_Tactic_conv_quot___closed__20;
static lean_object* l_Lean_Parser_Tactic_conv_quot___closed__18;
static lean_object* l_Lean_Parser_Tactic_conv_quot___closed__5;
static lean_object* l_Lean_Parser_Tactic_conv_quot___closed__15;
static lean_object* l_Lean_Parser_Tactic_convSkip___closed__1;
lean_object* l_Lean_Parser_Tactic_convSeqBracketed;
static lean_object* l_Lean_Parser_Tactic_convSeqBracketed___closed__1;
static lean_object* l_Lean_Parser_Tactic_convSeq1Indented___closed__10;
static lean_object* l_Lean_Parser_Tactic_conv_quot___closed__23;
static lean_object* l_Lean_Parser_Tactic_convSeq1Indented___closed__21;
static lean_object* l_Lean_Parser_Tactic_conv_quot___closed__22;
static lean_object* l_Lean_Parser_Tactic_convWhnf___closed__2;
static lean_object* l_Lean_Parser_Tactic_convSkip___closed__2;
static lean_object* l_Lean_Parser_Tactic_convSeq1Indented___closed__13;
static lean_object* l_Lean_Parser_Tactic_convRhs___closed__5;
static lean_object* l_Lean_Parser_Tactic_convRhs___closed__1;
static lean_object* l_Lean_Parser_Tactic_convSeqBracketed___closed__9;
static lean_object* l_Lean_Parser_Tactic_convSkip___closed__4;
static lean_object* l_Lean_Parser_Tactic_convSeqBracketed___closed__8;
lean_object* l_Lean_Parser_Tactic_convRhs;
static lean_object* l_Lean_Parser_Tactic_convSeqBracketed___closed__4;
static lean_object* l_Lean_Parser_Tactic_conv_quot___closed__6;
static lean_object* l_Lean_Parser_Tactic_convSeqBracketed___closed__2;
static lean_object* l_Lean_Parser_Tactic_convLhs___closed__1;
lean_object* l_Lean_Parser_Tactic_convSkip;
static lean_object* l_Lean_Parser_Tactic_convSeq1Indented___closed__5;
static lean_object* l_Lean_Parser_Tactic_convRhs___closed__4;
static lean_object* l_Lean_Parser_Tactic_convSeq___closed__4;
static lean_object* l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__22;
static lean_object* l_Lean_Parser_Tactic_convSeq1Indented___closed__17;
static lean_object* l_Lean_Parser_Tactic_convSeq1Indented___closed__8;
static lean_object* l_Lean_Parser_Tactic_convLhs___closed__4;
static lean_object* l_Lean_Parser_Tactic_convSeq1Indented___closed__4;
static lean_object* l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__7;
static lean_object* l_Lean_Parser_Tactic_convSeqBracketed___closed__5;
static lean_object* l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__24;
static lean_object* l_Lean_Parser_Tactic_convLhs___closed__3;
static lean_object* l_Lean_Parser_Tactic_convSeq1Indented___closed__2;
static lean_object* l_Lean_Parser_Tactic_convSeq1Indented___closed__1;
static lean_object* l_Lean_Parser_Tactic_convLhs___closed__2;
static lean_object* l_Lean_Parser_Tactic_convSkip___closed__3;
static lean_object* l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__16;
static lean_object* l_Lean_Parser_Tactic_convSeqBracketed___closed__7;
static lean_object* l_Lean_Parser_Tactic_convRhs___closed__2;
static lean_object* l_Lean_Parser_Tactic_convWhnf___closed__5;
static lean_object* l_Lean_Parser_Tactic_convWhnf___closed__3;
static lean_object* l_Lean_Parser_Tactic_convSeq1Indented___closed__18;
static lean_object* l_Lean_Parser_Tactic_conv_quot___closed__3;
static lean_object* l_Lean_Parser_Tactic_conv_quot___closed__10;
static lean_object* l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__18;
static lean_object* l_Lean_Parser_Tactic_convSeq1Indented___closed__14;
lean_object* l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e__;
static lean_object* l_Lean_Parser_Tactic_convSeq___closed__5;
static lean_object* l_Lean_Parser_Tactic_convSeq1Indented___closed__15;
static lean_object* l_Lean_Parser_Tactic_convSeq___closed__3;
static lean_object* l_Lean_Parser_Tactic_convSeq___closed__1;
static lean_object* l_Lean_Parser_Tactic_convSeq1Indented___closed__3;
static lean_object* l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__14;
static lean_object* l_Lean_Parser_Tactic_conv_quot___closed__7;
static lean_object* l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__5;
static lean_object* l_Lean_Parser_Tactic_conv_quot___closed__16;
static lean_object* l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__15;
static lean_object* l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__3;
static lean_object* l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__2;
lean_object* l_Lean_Parser_Tactic_convSeq1Indented;
static lean_object* l_Lean_Parser_Tactic_conv_quot___closed__19;
static lean_object* l_Lean_Parser_Tactic_convSeq___closed__6;
lean_object* l_Lean_Parser_Tactic_convSeq;
lean_object* l_Lean_Parser_Tactic_conv_quot;
static lean_object* l_Lean_Parser_Tactic_conv_quot___closed__11;
static lean_object* l_Lean_Parser_Tactic_conv_quot___closed__2;
static lean_object* l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__6;
static lean_object* l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__25;
static lean_object* l_Lean_Parser_Tactic_convSeq1Indented___closed__6;
static lean_object* l_Lean_Parser_Tactic_convSeqBracketed___closed__6;
static lean_object* l_Lean_Parser_Tactic_convSeq1Indented___closed__9;
static lean_object* l_Lean_Parser_Tactic_convSeq___closed__2;
static lean_object* l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__21;
static lean_object* l_Lean_Parser_Tactic_convSeqBracketed___closed__3;
static lean_object* l_Lean_Parser_Tactic_conv_quot___closed__12;
static lean_object* l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__13;
static lean_object* l_Lean_Parser_Tactic_convSeqBracketed___closed__10;
static lean_object* l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__1;
static lean_object* l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__23;
static lean_object* l_Lean_Parser_Tactic_conv_quot___closed__13;
lean_object* l_Lean_Parser_Tactic_convLhs;
lean_object* l_Lean_Parser_Tactic_convWhnf;
static lean_object* l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__9;
static lean_object* l_Lean_Parser_Tactic_convWhnf___closed__4;
lean_object* l_Lean_Parser_Tactic_convCongr;
static lean_object* l_Lean_Parser_Tactic_convSeq1Indented___closed__7;
static lean_object* l_Lean_Parser_Tactic_convLhs___closed__5;
static lean_object* l_Lean_Parser_Tactic_convCongr___closed__2;
static lean_object* l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__17;
static lean_object* l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__8;
static lean_object* l_Lean_Parser_Tactic_convSeqBracketed___closed__11;
static lean_object* l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__4;
static lean_object* l_Lean_Parser_Tactic_conv_quot___closed__21;
static lean_object* l_Lean_Parser_Tactic_convSeq1Indented___closed__16;
static lean_object* l_Lean_Parser_Tactic_convRhs___closed__3;
static lean_object* l_Lean_Parser_Tactic_convSeq1Indented___closed__20;
static lean_object* l_Lean_Parser_Tactic_conv_quot___closed__17;
static lean_object* l_Lean_Parser_Tactic_conv_quot___closed__1;
static lean_object* l_Lean_Parser_Tactic_convSeq1Indented___closed__11;
static lean_object* l_Lean_Parser_Tactic_convCongr___closed__4;
static lean_object* l_Lean_Parser_Tactic_convSeq1Indented___closed__19;
static lean_object* l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__19;
static lean_object* l_Lean_Parser_Tactic_convWhnf___closed__1;
static lean_object* l_Lean_Parser_Tactic_convSkip___closed__5;
static lean_object* l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__11;
static lean_object* l_Lean_Parser_Tactic_conv_quot___closed__9;
static lean_object* l_Lean_Parser_Tactic_conv_quot___closed__8;
static lean_object* l_Lean_Parser_Tactic_conv_quot___closed__4;
static lean_object* _init_l_Lean_Parser_Tactic_conv_quot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_conv_quot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_conv_quot___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_conv_quot___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_conv_quot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_conv_quot___closed__2;
x_2 = l_Lean_Parser_Tactic_conv_quot___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_conv_quot___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Term");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_conv_quot___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_conv_quot___closed__4;
x_2 = l_Lean_Parser_Tactic_conv_quot___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_conv_quot___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("quot");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_conv_quot___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_conv_quot___closed__6;
x_2 = l_Lean_Parser_Tactic_conv_quot___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_conv_quot___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("andthen");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_conv_quot___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_conv_quot___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_conv_quot___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("`(conv|");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_conv_quot___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_conv_quot___closed__11;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_conv_quot___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("incQuotDepth");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_conv_quot___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_conv_quot___closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_conv_quot___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("conv");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_conv_quot___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_conv_quot___closed__15;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_conv_quot___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_conv_quot___closed__16;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_conv_quot___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_conv_quot___closed__14;
x_2 = l_Lean_Parser_Tactic_conv_quot___closed__17;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_conv_quot___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(")");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_conv_quot___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_conv_quot___closed__19;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_conv_quot___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_conv_quot___closed__10;
x_2 = l_Lean_Parser_Tactic_conv_quot___closed__18;
x_3 = l_Lean_Parser_Tactic_conv_quot___closed__20;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_conv_quot___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_conv_quot___closed__10;
x_2 = l_Lean_Parser_Tactic_conv_quot___closed__12;
x_3 = l_Lean_Parser_Tactic_conv_quot___closed__21;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_conv_quot___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_conv_quot___closed__8;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Tactic_conv_quot___closed__22;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_conv_quot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_conv_quot___closed__23;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Tactic");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_conv_quot___closed__4;
x_2 = l_Lean_Parser_Tactic_convSeq1Indented___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("convSeq1Indented");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_convSeq1Indented___closed__2;
x_2 = l_Lean_Parser_Tactic_convSeq1Indented___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("withPosition");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_convSeq1Indented___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("many1");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_convSeq1Indented___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("colGe");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_convSeq1Indented___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_convSeq1Indented___closed__10;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_conv_quot___closed__10;
x_2 = l_Lean_Parser_Tactic_convSeq1Indented___closed__11;
x_3 = l_Lean_Parser_Tactic_conv_quot___closed__17;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("optional");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_convSeq1Indented___closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(";");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_convSeq1Indented___closed__15;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_convSeq1Indented___closed__14;
x_2 = l_Lean_Parser_Tactic_convSeq1Indented___closed__16;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_conv_quot___closed__10;
x_2 = l_Lean_Parser_Tactic_convSeq1Indented___closed__12;
x_3 = l_Lean_Parser_Tactic_convSeq1Indented___closed__17;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_convSeq1Indented___closed__8;
x_2 = l_Lean_Parser_Tactic_convSeq1Indented___closed__18;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_convSeq1Indented___closed__6;
x_2 = l_Lean_Parser_Tactic_convSeq1Indented___closed__19;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_convSeq1Indented___closed__3;
x_2 = l_Lean_Parser_Tactic_convSeq1Indented___closed__4;
x_3 = l_Lean_Parser_Tactic_convSeq1Indented___closed__20;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq1Indented() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_convSeq1Indented___closed__21;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeqBracketed___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("convSeqBracketed");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeqBracketed___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_convSeq1Indented___closed__2;
x_2 = l_Lean_Parser_Tactic_convSeqBracketed___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeqBracketed___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("{");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeqBracketed___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_convSeqBracketed___closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeqBracketed___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_conv_quot___closed__10;
x_2 = l_Lean_Parser_Tactic_conv_quot___closed__17;
x_3 = l_Lean_Parser_Tactic_convSeq1Indented___closed__17;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeqBracketed___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_convSeq1Indented___closed__8;
x_2 = l_Lean_Parser_Tactic_convSeqBracketed___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeqBracketed___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_conv_quot___closed__10;
x_2 = l_Lean_Parser_Tactic_convSeqBracketed___closed__4;
x_3 = l_Lean_Parser_Tactic_convSeqBracketed___closed__6;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeqBracketed___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("}");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeqBracketed___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_convSeqBracketed___closed__8;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeqBracketed___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_conv_quot___closed__10;
x_2 = l_Lean_Parser_Tactic_convSeqBracketed___closed__7;
x_3 = l_Lean_Parser_Tactic_convSeqBracketed___closed__9;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeqBracketed___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_convSeqBracketed___closed__1;
x_2 = l_Lean_Parser_Tactic_convSeqBracketed___closed__2;
x_3 = l_Lean_Parser_Tactic_convSeqBracketed___closed__10;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeqBracketed() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_convSeqBracketed___closed__11;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("convSeq");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_convSeq1Indented___closed__2;
x_2 = l_Lean_Parser_Tactic_convSeq___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("orelse");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_convSeq___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_convSeq___closed__4;
x_2 = l_Lean_Parser_Tactic_convSeq1Indented;
x_3 = l_Lean_Parser_Tactic_convSeqBracketed;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_convSeq___closed__1;
x_2 = l_Lean_Parser_Tactic_convSeq___closed__2;
x_3 = l_Lean_Parser_Tactic_convSeq___closed__5;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_convSeq___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSkip___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("convSkip");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSkip___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_convSeq1Indented___closed__2;
x_2 = l_Lean_Parser_Tactic_convSkip___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSkip___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("skip ");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSkip___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_convSkip___closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSkip___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_convSkip___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Tactic_convSkip___closed__4;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convSkip() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_convSkip___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convLhs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("convLhs");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convLhs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_convSeq1Indented___closed__2;
x_2 = l_Lean_Parser_Tactic_convLhs___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convLhs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lhs");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convLhs___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_convLhs___closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convLhs___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_convLhs___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Tactic_convLhs___closed__4;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convLhs() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_convLhs___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convRhs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("convRhs");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convRhs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_convSeq1Indented___closed__2;
x_2 = l_Lean_Parser_Tactic_convRhs___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convRhs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("rhs");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convRhs___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_convRhs___closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convRhs___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_convRhs___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Tactic_convRhs___closed__4;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convRhs() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_convRhs___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convWhnf___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("convWhnf");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convWhnf___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_convSeq1Indented___closed__2;
x_2 = l_Lean_Parser_Tactic_convWhnf___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convWhnf___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("whnf");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convWhnf___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_convWhnf___closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convWhnf___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_convWhnf___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Tactic_convWhnf___closed__4;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convWhnf() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_convWhnf___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convCongr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("convCongr");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convCongr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_convSeq1Indented___closed__2;
x_2 = l_Lean_Parser_Tactic_convCongr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convCongr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("congr");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convCongr___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_convCongr___closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convCongr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_convCongr___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Tactic_convCongr___closed__4;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_convCongr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_convCongr___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tacticConvAt__In_=>_");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_convSeq1Indented___closed__2;
x_2 = l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("conv ");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" at ");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__5;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ident");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_conv_quot___closed__10;
x_2 = l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__6;
x_3 = l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__9;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_convSeq1Indented___closed__14;
x_2 = l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_conv_quot___closed__10;
x_2 = l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__4;
x_3 = l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__11;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" in ");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__13;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("term");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__15;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__16;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_conv_quot___closed__10;
x_2 = l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__14;
x_3 = l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__17;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_convSeq1Indented___closed__14;
x_2 = l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__18;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_conv_quot___closed__10;
x_2 = l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__12;
x_3 = l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__19;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" => ");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__21;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_conv_quot___closed__10;
x_2 = l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__20;
x_3 = l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__22;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_conv_quot___closed__10;
x_2 = l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__23;
x_3 = l_Lean_Parser_Tactic_convSeq;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__2;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__24;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e__() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__25;
return x_1;
}
}
lean_object* initialize_Init_Notation(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Conv(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Notation(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_conv_quot___closed__1 = _init_l_Lean_Parser_Tactic_conv_quot___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_conv_quot___closed__1);
l_Lean_Parser_Tactic_conv_quot___closed__2 = _init_l_Lean_Parser_Tactic_conv_quot___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_conv_quot___closed__2);
l_Lean_Parser_Tactic_conv_quot___closed__3 = _init_l_Lean_Parser_Tactic_conv_quot___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_conv_quot___closed__3);
l_Lean_Parser_Tactic_conv_quot___closed__4 = _init_l_Lean_Parser_Tactic_conv_quot___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_conv_quot___closed__4);
l_Lean_Parser_Tactic_conv_quot___closed__5 = _init_l_Lean_Parser_Tactic_conv_quot___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_conv_quot___closed__5);
l_Lean_Parser_Tactic_conv_quot___closed__6 = _init_l_Lean_Parser_Tactic_conv_quot___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_conv_quot___closed__6);
l_Lean_Parser_Tactic_conv_quot___closed__7 = _init_l_Lean_Parser_Tactic_conv_quot___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_conv_quot___closed__7);
l_Lean_Parser_Tactic_conv_quot___closed__8 = _init_l_Lean_Parser_Tactic_conv_quot___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_conv_quot___closed__8);
l_Lean_Parser_Tactic_conv_quot___closed__9 = _init_l_Lean_Parser_Tactic_conv_quot___closed__9();
lean_mark_persistent(l_Lean_Parser_Tactic_conv_quot___closed__9);
l_Lean_Parser_Tactic_conv_quot___closed__10 = _init_l_Lean_Parser_Tactic_conv_quot___closed__10();
lean_mark_persistent(l_Lean_Parser_Tactic_conv_quot___closed__10);
l_Lean_Parser_Tactic_conv_quot___closed__11 = _init_l_Lean_Parser_Tactic_conv_quot___closed__11();
lean_mark_persistent(l_Lean_Parser_Tactic_conv_quot___closed__11);
l_Lean_Parser_Tactic_conv_quot___closed__12 = _init_l_Lean_Parser_Tactic_conv_quot___closed__12();
lean_mark_persistent(l_Lean_Parser_Tactic_conv_quot___closed__12);
l_Lean_Parser_Tactic_conv_quot___closed__13 = _init_l_Lean_Parser_Tactic_conv_quot___closed__13();
lean_mark_persistent(l_Lean_Parser_Tactic_conv_quot___closed__13);
l_Lean_Parser_Tactic_conv_quot___closed__14 = _init_l_Lean_Parser_Tactic_conv_quot___closed__14();
lean_mark_persistent(l_Lean_Parser_Tactic_conv_quot___closed__14);
l_Lean_Parser_Tactic_conv_quot___closed__15 = _init_l_Lean_Parser_Tactic_conv_quot___closed__15();
lean_mark_persistent(l_Lean_Parser_Tactic_conv_quot___closed__15);
l_Lean_Parser_Tactic_conv_quot___closed__16 = _init_l_Lean_Parser_Tactic_conv_quot___closed__16();
lean_mark_persistent(l_Lean_Parser_Tactic_conv_quot___closed__16);
l_Lean_Parser_Tactic_conv_quot___closed__17 = _init_l_Lean_Parser_Tactic_conv_quot___closed__17();
lean_mark_persistent(l_Lean_Parser_Tactic_conv_quot___closed__17);
l_Lean_Parser_Tactic_conv_quot___closed__18 = _init_l_Lean_Parser_Tactic_conv_quot___closed__18();
lean_mark_persistent(l_Lean_Parser_Tactic_conv_quot___closed__18);
l_Lean_Parser_Tactic_conv_quot___closed__19 = _init_l_Lean_Parser_Tactic_conv_quot___closed__19();
lean_mark_persistent(l_Lean_Parser_Tactic_conv_quot___closed__19);
l_Lean_Parser_Tactic_conv_quot___closed__20 = _init_l_Lean_Parser_Tactic_conv_quot___closed__20();
lean_mark_persistent(l_Lean_Parser_Tactic_conv_quot___closed__20);
l_Lean_Parser_Tactic_conv_quot___closed__21 = _init_l_Lean_Parser_Tactic_conv_quot___closed__21();
lean_mark_persistent(l_Lean_Parser_Tactic_conv_quot___closed__21);
l_Lean_Parser_Tactic_conv_quot___closed__22 = _init_l_Lean_Parser_Tactic_conv_quot___closed__22();
lean_mark_persistent(l_Lean_Parser_Tactic_conv_quot___closed__22);
l_Lean_Parser_Tactic_conv_quot___closed__23 = _init_l_Lean_Parser_Tactic_conv_quot___closed__23();
lean_mark_persistent(l_Lean_Parser_Tactic_conv_quot___closed__23);
l_Lean_Parser_Tactic_conv_quot = _init_l_Lean_Parser_Tactic_conv_quot();
lean_mark_persistent(l_Lean_Parser_Tactic_conv_quot);
l_Lean_Parser_Tactic_convSeq1Indented___closed__1 = _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq1Indented___closed__1);
l_Lean_Parser_Tactic_convSeq1Indented___closed__2 = _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq1Indented___closed__2);
l_Lean_Parser_Tactic_convSeq1Indented___closed__3 = _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq1Indented___closed__3);
l_Lean_Parser_Tactic_convSeq1Indented___closed__4 = _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq1Indented___closed__4);
l_Lean_Parser_Tactic_convSeq1Indented___closed__5 = _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq1Indented___closed__5);
l_Lean_Parser_Tactic_convSeq1Indented___closed__6 = _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq1Indented___closed__6);
l_Lean_Parser_Tactic_convSeq1Indented___closed__7 = _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq1Indented___closed__7);
l_Lean_Parser_Tactic_convSeq1Indented___closed__8 = _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq1Indented___closed__8);
l_Lean_Parser_Tactic_convSeq1Indented___closed__9 = _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__9();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq1Indented___closed__9);
l_Lean_Parser_Tactic_convSeq1Indented___closed__10 = _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__10();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq1Indented___closed__10);
l_Lean_Parser_Tactic_convSeq1Indented___closed__11 = _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__11();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq1Indented___closed__11);
l_Lean_Parser_Tactic_convSeq1Indented___closed__12 = _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__12();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq1Indented___closed__12);
l_Lean_Parser_Tactic_convSeq1Indented___closed__13 = _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__13();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq1Indented___closed__13);
l_Lean_Parser_Tactic_convSeq1Indented___closed__14 = _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__14();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq1Indented___closed__14);
l_Lean_Parser_Tactic_convSeq1Indented___closed__15 = _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__15();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq1Indented___closed__15);
l_Lean_Parser_Tactic_convSeq1Indented___closed__16 = _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__16();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq1Indented___closed__16);
l_Lean_Parser_Tactic_convSeq1Indented___closed__17 = _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__17();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq1Indented___closed__17);
l_Lean_Parser_Tactic_convSeq1Indented___closed__18 = _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__18();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq1Indented___closed__18);
l_Lean_Parser_Tactic_convSeq1Indented___closed__19 = _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__19();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq1Indented___closed__19);
l_Lean_Parser_Tactic_convSeq1Indented___closed__20 = _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__20();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq1Indented___closed__20);
l_Lean_Parser_Tactic_convSeq1Indented___closed__21 = _init_l_Lean_Parser_Tactic_convSeq1Indented___closed__21();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq1Indented___closed__21);
l_Lean_Parser_Tactic_convSeq1Indented = _init_l_Lean_Parser_Tactic_convSeq1Indented();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq1Indented);
l_Lean_Parser_Tactic_convSeqBracketed___closed__1 = _init_l_Lean_Parser_Tactic_convSeqBracketed___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeqBracketed___closed__1);
l_Lean_Parser_Tactic_convSeqBracketed___closed__2 = _init_l_Lean_Parser_Tactic_convSeqBracketed___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeqBracketed___closed__2);
l_Lean_Parser_Tactic_convSeqBracketed___closed__3 = _init_l_Lean_Parser_Tactic_convSeqBracketed___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeqBracketed___closed__3);
l_Lean_Parser_Tactic_convSeqBracketed___closed__4 = _init_l_Lean_Parser_Tactic_convSeqBracketed___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeqBracketed___closed__4);
l_Lean_Parser_Tactic_convSeqBracketed___closed__5 = _init_l_Lean_Parser_Tactic_convSeqBracketed___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeqBracketed___closed__5);
l_Lean_Parser_Tactic_convSeqBracketed___closed__6 = _init_l_Lean_Parser_Tactic_convSeqBracketed___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeqBracketed___closed__6);
l_Lean_Parser_Tactic_convSeqBracketed___closed__7 = _init_l_Lean_Parser_Tactic_convSeqBracketed___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeqBracketed___closed__7);
l_Lean_Parser_Tactic_convSeqBracketed___closed__8 = _init_l_Lean_Parser_Tactic_convSeqBracketed___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeqBracketed___closed__8);
l_Lean_Parser_Tactic_convSeqBracketed___closed__9 = _init_l_Lean_Parser_Tactic_convSeqBracketed___closed__9();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeqBracketed___closed__9);
l_Lean_Parser_Tactic_convSeqBracketed___closed__10 = _init_l_Lean_Parser_Tactic_convSeqBracketed___closed__10();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeqBracketed___closed__10);
l_Lean_Parser_Tactic_convSeqBracketed___closed__11 = _init_l_Lean_Parser_Tactic_convSeqBracketed___closed__11();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeqBracketed___closed__11);
l_Lean_Parser_Tactic_convSeqBracketed = _init_l_Lean_Parser_Tactic_convSeqBracketed();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeqBracketed);
l_Lean_Parser_Tactic_convSeq___closed__1 = _init_l_Lean_Parser_Tactic_convSeq___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq___closed__1);
l_Lean_Parser_Tactic_convSeq___closed__2 = _init_l_Lean_Parser_Tactic_convSeq___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq___closed__2);
l_Lean_Parser_Tactic_convSeq___closed__3 = _init_l_Lean_Parser_Tactic_convSeq___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq___closed__3);
l_Lean_Parser_Tactic_convSeq___closed__4 = _init_l_Lean_Parser_Tactic_convSeq___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq___closed__4);
l_Lean_Parser_Tactic_convSeq___closed__5 = _init_l_Lean_Parser_Tactic_convSeq___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq___closed__5);
l_Lean_Parser_Tactic_convSeq___closed__6 = _init_l_Lean_Parser_Tactic_convSeq___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq___closed__6);
l_Lean_Parser_Tactic_convSeq = _init_l_Lean_Parser_Tactic_convSeq();
lean_mark_persistent(l_Lean_Parser_Tactic_convSeq);
l_Lean_Parser_Tactic_convSkip___closed__1 = _init_l_Lean_Parser_Tactic_convSkip___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_convSkip___closed__1);
l_Lean_Parser_Tactic_convSkip___closed__2 = _init_l_Lean_Parser_Tactic_convSkip___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_convSkip___closed__2);
l_Lean_Parser_Tactic_convSkip___closed__3 = _init_l_Lean_Parser_Tactic_convSkip___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_convSkip___closed__3);
l_Lean_Parser_Tactic_convSkip___closed__4 = _init_l_Lean_Parser_Tactic_convSkip___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_convSkip___closed__4);
l_Lean_Parser_Tactic_convSkip___closed__5 = _init_l_Lean_Parser_Tactic_convSkip___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_convSkip___closed__5);
l_Lean_Parser_Tactic_convSkip = _init_l_Lean_Parser_Tactic_convSkip();
lean_mark_persistent(l_Lean_Parser_Tactic_convSkip);
l_Lean_Parser_Tactic_convLhs___closed__1 = _init_l_Lean_Parser_Tactic_convLhs___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_convLhs___closed__1);
l_Lean_Parser_Tactic_convLhs___closed__2 = _init_l_Lean_Parser_Tactic_convLhs___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_convLhs___closed__2);
l_Lean_Parser_Tactic_convLhs___closed__3 = _init_l_Lean_Parser_Tactic_convLhs___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_convLhs___closed__3);
l_Lean_Parser_Tactic_convLhs___closed__4 = _init_l_Lean_Parser_Tactic_convLhs___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_convLhs___closed__4);
l_Lean_Parser_Tactic_convLhs___closed__5 = _init_l_Lean_Parser_Tactic_convLhs___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_convLhs___closed__5);
l_Lean_Parser_Tactic_convLhs = _init_l_Lean_Parser_Tactic_convLhs();
lean_mark_persistent(l_Lean_Parser_Tactic_convLhs);
l_Lean_Parser_Tactic_convRhs___closed__1 = _init_l_Lean_Parser_Tactic_convRhs___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_convRhs___closed__1);
l_Lean_Parser_Tactic_convRhs___closed__2 = _init_l_Lean_Parser_Tactic_convRhs___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_convRhs___closed__2);
l_Lean_Parser_Tactic_convRhs___closed__3 = _init_l_Lean_Parser_Tactic_convRhs___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_convRhs___closed__3);
l_Lean_Parser_Tactic_convRhs___closed__4 = _init_l_Lean_Parser_Tactic_convRhs___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_convRhs___closed__4);
l_Lean_Parser_Tactic_convRhs___closed__5 = _init_l_Lean_Parser_Tactic_convRhs___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_convRhs___closed__5);
l_Lean_Parser_Tactic_convRhs = _init_l_Lean_Parser_Tactic_convRhs();
lean_mark_persistent(l_Lean_Parser_Tactic_convRhs);
l_Lean_Parser_Tactic_convWhnf___closed__1 = _init_l_Lean_Parser_Tactic_convWhnf___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_convWhnf___closed__1);
l_Lean_Parser_Tactic_convWhnf___closed__2 = _init_l_Lean_Parser_Tactic_convWhnf___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_convWhnf___closed__2);
l_Lean_Parser_Tactic_convWhnf___closed__3 = _init_l_Lean_Parser_Tactic_convWhnf___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_convWhnf___closed__3);
l_Lean_Parser_Tactic_convWhnf___closed__4 = _init_l_Lean_Parser_Tactic_convWhnf___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_convWhnf___closed__4);
l_Lean_Parser_Tactic_convWhnf___closed__5 = _init_l_Lean_Parser_Tactic_convWhnf___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_convWhnf___closed__5);
l_Lean_Parser_Tactic_convWhnf = _init_l_Lean_Parser_Tactic_convWhnf();
lean_mark_persistent(l_Lean_Parser_Tactic_convWhnf);
l_Lean_Parser_Tactic_convCongr___closed__1 = _init_l_Lean_Parser_Tactic_convCongr___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_convCongr___closed__1);
l_Lean_Parser_Tactic_convCongr___closed__2 = _init_l_Lean_Parser_Tactic_convCongr___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_convCongr___closed__2);
l_Lean_Parser_Tactic_convCongr___closed__3 = _init_l_Lean_Parser_Tactic_convCongr___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_convCongr___closed__3);
l_Lean_Parser_Tactic_convCongr___closed__4 = _init_l_Lean_Parser_Tactic_convCongr___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_convCongr___closed__4);
l_Lean_Parser_Tactic_convCongr___closed__5 = _init_l_Lean_Parser_Tactic_convCongr___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_convCongr___closed__5);
l_Lean_Parser_Tactic_convCongr = _init_l_Lean_Parser_Tactic_convCongr();
lean_mark_persistent(l_Lean_Parser_Tactic_convCongr);
l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__1 = _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__1);
l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__2 = _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__2);
l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__3 = _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__3);
l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__4 = _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__4);
l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__5 = _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__5);
l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__6 = _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__6);
l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__7 = _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__7);
l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__8 = _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__8);
l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__9 = _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__9();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__9);
l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__10 = _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__10();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__10);
l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__11 = _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__11();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__11);
l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__12 = _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__12();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__12);
l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__13 = _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__13();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__13);
l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__14 = _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__14();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__14);
l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__15 = _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__15();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__15);
l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__16 = _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__16();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__16);
l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__17 = _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__17();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__17);
l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__18 = _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__18();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__18);
l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__19 = _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__19();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__19);
l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__20 = _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__20();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__20);
l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__21 = _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__21();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__21);
l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__22 = _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__22();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__22);
l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__23 = _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__23();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__23);
l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__24 = _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__24();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__24);
l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__25 = _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__25();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e_____closed__25);
l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e__ = _init_l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e__();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticConvAt____In___x3d_x3e__);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
