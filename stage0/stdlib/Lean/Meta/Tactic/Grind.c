// Lean compiler output
// Module: Lean.Meta.Tactic.Grind
// Imports: Lean.Meta.Tactic.Grind.Attr Lean.Meta.Tactic.Grind.RevertAll Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.Preprocessor Lean.Meta.Tactic.Grind.Util Lean.Meta.Tactic.Grind.Cases Lean.Meta.Tactic.Grind.Injection Lean.Meta.Tactic.Grind.Core Lean.Meta.Tactic.Grind.Canon Lean.Meta.Tactic.Grind.MarkNestedProofs Lean.Meta.Tactic.Grind.Inv Lean.Meta.Tactic.Grind.Proof Lean.Meta.Tactic.Grind.Propagate Lean.Meta.Tactic.Grind.PP Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Grind.Ctor Lean.Meta.Tactic.Grind.Parser
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
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_299____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_188____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_336____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_40____closed__2;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_151_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_40____closed__3;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_262_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_225____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__2;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_336_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__14;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_188_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__15;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_114_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__10;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_188____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_299____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_151____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_373____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_336____closed__3;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_40____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_225____closed__1;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__4;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_336____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_373____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__9;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_373_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_262____closed__1;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_262____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_77____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__8;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_225____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__5;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__17;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_40_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_114____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__13;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_188____closed__3;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_299_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_373____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__11;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_114____closed__3;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_225_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_77____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__7;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_114____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_151____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__12;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_299____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_262____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__6;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_77_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_151____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__18;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__16;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_77____closed__2;
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__4;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__6;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__8;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__9;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__11;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__13;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__15;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__16;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__17;
x_2 = lean_unsigned_to_nat(3u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__18;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_40____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_40____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_40____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_40____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__17;
x_2 = lean_unsigned_to_nat(40u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_40_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_40____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_40____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_77____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("issues", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_77____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_77____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_77____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__17;
x_2 = lean_unsigned_to_nat(77u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_77_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_77____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_77____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_114____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("add", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_114____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_114____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_114____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__17;
x_2 = lean_unsigned_to_nat(114u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_114_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_114____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_114____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_151____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pre", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_151____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_151____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_151____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__17;
x_2 = lean_unsigned_to_nat(151u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_151_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_151____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_151____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_188____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_188____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_188____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_188____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__17;
x_2 = lean_unsigned_to_nat(188u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_188_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_188____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_188____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_225____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proofs", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_225____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_188____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_225____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_225____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__17;
x_2 = lean_unsigned_to_nat(225u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_225_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_225____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_225____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_262____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_262____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_262____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_262____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__17;
x_2 = lean_unsigned_to_nat(262u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_262_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_262____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_262____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_299____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congr", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_299____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_299____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_299____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__17;
x_2 = lean_unsigned_to_nat(299u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_299_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_299____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_299____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_336____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proof", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_336____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_336____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_336____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__17;
x_2 = lean_unsigned_to_nat(336u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_336_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_336____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_336____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_373____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("detail", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_373____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_336____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_373____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_373____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__17;
x_2 = lean_unsigned_to_nat(373u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_373_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_373____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_373____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_RevertAll(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Preprocessor(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Injection(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Core(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Canon(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_MarkNestedProofs(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Inv(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Proof(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Propagate(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_PP(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Ctor(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Parser(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Attr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_RevertAll(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Preprocessor(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Cases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Injection(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Core(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Canon(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MarkNestedProofs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Inv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Proof(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Propagate(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PP(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Ctor(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Parser(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__3);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__4 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__4);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__5 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__5);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__6 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__6();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__6);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__7 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__7();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__7);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__8 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__8();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__8);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__9 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__9();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__9);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__10 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__10();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__10);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__11 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__11();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__11);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__12 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__12();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__12);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__13 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__13();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__13);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__14 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__14();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__14);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__15 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__15();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__15);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__16 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__16();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__16);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__17 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__17();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__17);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__18 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__18();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3____closed__18);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_40____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_40____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_40____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_40____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_40____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_40____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_40____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_40____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_40____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_40_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_77____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_77____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_77____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_77____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_77____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_77____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_77____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_77____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_77____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_77_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_114____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_114____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_114____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_114____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_114____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_114____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_114____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_114____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_114____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_114_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_151____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_151____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_151____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_151____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_151____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_151____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_151____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_151____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_151____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_151_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_188____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_188____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_188____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_188____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_188____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_188____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_188____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_188____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_188____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_188_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_225____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_225____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_225____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_225____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_225____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_225____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_225____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_225____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_225____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_225_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_262____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_262____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_262____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_262____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_262____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_262____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_262____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_262____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_262____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_262_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_299____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_299____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_299____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_299____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_299____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_299____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_299____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_299____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_299____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_299_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_336____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_336____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_336____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_336____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_336____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_336____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_336____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_336____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_336____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_336_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_373____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_373____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_373____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_373____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_373____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_373____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_373____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_373____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_373____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_373_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
