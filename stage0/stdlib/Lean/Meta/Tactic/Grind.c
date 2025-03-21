// Lean compiler output
// Module: Lean.Meta.Tactic.Grind
// Imports: Lean.Meta.Tactic.Grind.Attr Lean.Meta.Tactic.Grind.RevertAll Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.Util Lean.Meta.Tactic.Grind.Cases Lean.Meta.Tactic.Grind.Injection Lean.Meta.Tactic.Grind.Core Lean.Meta.Tactic.Grind.Canon Lean.Meta.Tactic.Grind.MarkNestedProofs Lean.Meta.Tactic.Grind.Inv Lean.Meta.Tactic.Grind.Proof Lean.Meta.Tactic.Grind.Propagate Lean.Meta.Tactic.Grind.PP Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Grind.Ctor Lean.Meta.Tactic.Grind.Parser Lean.Meta.Tactic.Grind.EMatchTheorem Lean.Meta.Tactic.Grind.EMatch Lean.Meta.Tactic.Grind.Main Lean.Meta.Tactic.Grind.CasesMatch Lean.Meta.Tactic.Grind.Arith Lean.Meta.Tactic.Grind.Ext Lean.Meta.Tactic.Grind.MatchCond Lean.Meta.Tactic.Grind.MatchDiscrOnly Lean.Meta.Tactic.Grind.Diseq
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
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_745____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_78____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_856____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__8;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__9;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_559____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_671____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_300____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1115____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1041_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_226_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1189____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_708____closed__1;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1004_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__14;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__10;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_226____closed__3;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1189_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_671_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_819_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_448____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_485____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_708____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_337____closed__3;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_745_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_448____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__13;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_411____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_930____closed__2;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_893_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_152____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_819____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189____closed__2;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1115_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__11;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_448_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_819____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1004____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_411____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1078____closed__2;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1078_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_745____closed__1;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_115_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_263____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_559____closed__3;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_559_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_115____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_671____closed__2;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_41____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_337____closed__1;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_152_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_300_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_485____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_374____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_967____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_226____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1078____closed__1;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_374_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_893____closed__2;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1004____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_596____closed__3;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_708_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__6;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_300____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_596____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_671____closed__1;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_78_(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__5;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1152____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_263____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_41____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__12;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1152_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_78____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_485____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_559____closed__1;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1152____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1115____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_893____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1041____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_596____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_226____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__16;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_448____closed__3;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_152____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_893____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_374____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_856____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_856____closed__2;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_930_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_819____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_745____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_374____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1115____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_782____closed__1;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_967_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1189____closed__3;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_41_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_930____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_782____closed__2;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_782_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_337____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__15;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_263____closed__1;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_411_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_967____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_300____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_967____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1189____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_337_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_522____closed__3;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_411____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_115____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__18;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_856_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_596_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_522____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_522____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1041____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_708____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__7;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__4;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_115____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1152____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_782____closed__3;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_485_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_263_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_152____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_78____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_41____closed__2;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_522_(lean_object*);
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__4;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__6;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__8;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__9;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__11;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__13;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__15;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__16;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(4u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__18;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_41____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_41____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_41____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_41____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(41u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_41_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_41____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_41____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_78____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assert", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_78____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_78____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_78____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(78u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_78_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_78____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_78____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_115____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eqc", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_115____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_115____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_115____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(115u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_115_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_115____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_115____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_152____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internalize", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_152____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_152____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_152____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(152u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_152_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_152____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_152____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ematch", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(189u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_226____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pattern", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_226____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_226____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_226____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(226u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_226_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_226____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_226____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_263____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("search", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_263____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_226____closed__1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_263____closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_263____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(263u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_263_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_263____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_263____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_300____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instance", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_300____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_300____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_300____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(300u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_300_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_300____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_300____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_337____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assignment", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_337____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_300____closed__1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_337____closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_337____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(337u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_337_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_337____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_337____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_374____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eqResolution", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_374____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_374____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_374____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(374u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_374_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_374____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_374____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_411____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("issues", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_411____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_411____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_411____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(411u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_411_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_411____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_411____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_448____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_448____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_448____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_448____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(448u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_448_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_448____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_448____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_485____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("split", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_485____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_485____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_485____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(485u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_485_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_485____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_485____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_522____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("candidate", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_522____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_485____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_522____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_522____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(522u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_522_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_522____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_522____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_559____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("resolved", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_559____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_485____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_559____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_559____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(559u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_559_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_559____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_559____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_596____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("beta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_596____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_596____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_596____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(596u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_596_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_596____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_596____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(634u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_671____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proofs", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_671____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_671____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_671____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(671u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_671_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_671____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_671____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_708____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congr", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_708____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_708____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_708____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(708u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_708_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_708____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_708____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_745____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proof", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_745____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_745____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_745____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(745u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_745_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_745____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_745____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_782____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proj", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_782____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_782____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_782____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(782u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_782_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_782____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_782____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_819____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("parent", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_819____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_819____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_819____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(819u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_819_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_819____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_819____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_856____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("final", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_856____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_856____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_856____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(856u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_856_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_856____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_856____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_893____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("forallPropagator", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_893____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_893____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_893____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(893u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_893_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_893____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_893____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_930____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_485____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_930____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(930u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_930_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_930____closed__1;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_930____closed__2;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_967____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("canon", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_967____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_967____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_967____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(967u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_967_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_967____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_967____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1004____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189____closed__1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_226____closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1004____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(1004u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1004_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1004____closed__1;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1004____closed__2;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1041____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_596____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1041____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(1041u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1041_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1041____closed__1;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1041____closed__2;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1078____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_152____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1078____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(1078u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1078_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1078____closed__1;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1078____closed__2;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1115____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("matchCond", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1115____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1115____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1115____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(1115u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1115_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1115____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1115____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1152____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lambda", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1152____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1115____closed__1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1152____closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1152____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(1152u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1152_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1152____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1152____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1189____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proveFalse", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1189____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1115____closed__1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1189____closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1189____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17;
x_2 = lean_unsigned_to_nat(1189u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1189_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1189____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1189____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_RevertAll(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
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
lean_object* initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_EMatch(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_CasesMatch(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Ext(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_MatchCond(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Diseq(uint8_t builtin, lean_object*);
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
res = initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_EMatch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Main(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_CasesMatch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Ext(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MatchCond(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Diseq(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__3);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__4 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__4);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__5 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__5);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__6 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__6();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__6);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__7 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__7();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__7);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__8 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__8();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__8);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__9 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__9();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__9);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__10 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__10();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__10);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__11 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__11();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__11);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__12 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__12();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__12);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__13 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__13();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__13);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__14 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__14();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__14);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__15 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__15();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__15);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__16 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__16();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__16);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__17);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__18 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__18();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4____closed__18);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_41____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_41____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_41____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_41____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_41____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_41____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_41____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_41____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_41____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_41_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_78____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_78____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_78____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_78____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_78____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_78____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_78____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_78____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_78____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_78_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_115____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_115____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_115____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_115____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_115____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_115____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_115____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_115____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_115____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_115_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_152____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_152____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_152____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_152____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_152____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_152____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_152____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_152____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_152____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_152_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_226____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_226____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_226____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_226____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_226____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_226____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_226____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_226____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_226____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_226_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_263____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_263____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_263____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_263____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_263____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_263____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_263____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_263____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_263____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_263_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_300____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_300____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_300____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_300____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_300____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_300____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_300____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_300____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_300____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_300_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_337____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_337____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_337____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_337____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_337____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_337____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_337____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_337____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_337____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_337_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_374____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_374____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_374____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_374____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_374____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_374____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_374____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_374____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_374____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_374_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_411____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_411____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_411____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_411____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_411____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_411____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_411____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_411____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_411____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_411_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_448____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_448____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_448____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_448____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_448____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_448____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_448____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_448____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_448____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_448_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_485____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_485____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_485____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_485____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_485____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_485____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_485____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_485____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_485____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_485_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_522____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_522____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_522____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_522____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_522____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_522____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_522____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_522____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_522____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_522_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_559____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_559____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_559____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_559____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_559____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_559____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_559____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_559____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_559____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_559_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_596____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_596____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_596____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_596____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_596____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_596____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_596____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_596____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_596____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_596_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_634_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_671____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_671____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_671____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_671____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_671____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_671____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_671____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_671____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_671____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_671_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_708____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_708____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_708____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_708____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_708____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_708____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_708____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_708____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_708____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_708_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_745____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_745____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_745____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_745____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_745____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_745____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_745____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_745____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_745____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_745_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_782____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_782____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_782____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_782____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_782____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_782____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_782____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_782____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_782____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_782_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_819____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_819____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_819____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_819____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_819____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_819____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_819____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_819____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_819____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_819_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_856____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_856____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_856____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_856____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_856____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_856____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_856____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_856____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_856____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_856_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_893____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_893____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_893____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_893____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_893____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_893____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_893____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_893____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_893____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_893_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_930____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_930____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_930____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_930____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_930____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_930____closed__2);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_930_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_967____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_967____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_967____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_967____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_967____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_967____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_967____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_967____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_967____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_967_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1004____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1004____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1004____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1004____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1004____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1004____closed__2);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1004_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1041____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1041____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1041____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1041____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1041____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1041____closed__2);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1041_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1078____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1078____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1078____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1078____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1078____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1078____closed__2);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1078_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1115____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1115____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1115____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1115____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1115____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1115____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1115____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1115____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1115____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1115_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1152____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1152____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1152____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1152____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1152____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1152____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1152____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1152____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1152____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1152_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1189____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1189____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1189____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1189____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1189____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1189____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1189____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1189____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1189____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1189_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
