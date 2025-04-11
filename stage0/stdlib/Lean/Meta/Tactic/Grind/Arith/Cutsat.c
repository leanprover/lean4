// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat
// Imports: Lean.Util.Trace Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr Lean.Meta.Tactic.Grind.Arith.Cutsat.Search Lean.Meta.Tactic.Grind.Arith.Cutsat.Inv Lean.Meta.Tactic.Grind.Arith.Cutsat.Proof Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Lean.Meta.Tactic.Grind.Arith.Cutsat.Util Lean.Meta.Tactic.Grind.Arith.Cutsat.Var Lean.Meta.Tactic.Grind.Arith.Cutsat.EqCnstr Lean.Meta.Tactic.Grind.Arith.Cutsat.SearchM Lean.Meta.Tactic.Grind.Arith.Cutsat.Model Lean.Meta.Tactic.Grind.Arith.Cutsat.MBTC
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
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__4;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85____closed__3;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__8;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208____closed__1;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__18;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__6;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457____closed__2;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__23;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__10;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__20;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__19;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85_(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44____closed__1;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__21;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__17;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__9;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__16;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167____closed__3;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__4;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__15;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__12;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__5;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__13;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__7;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44____closed__3;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499____closed__1;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__11;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__14;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415____closed__1;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331____closed__2;
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cutsat", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__5;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__7;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__9;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__10;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__12;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__14;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Arith", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__16;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__17;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Cutsat", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__18;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__19;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__20;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__21;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(3u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__3;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__23;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("model", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(44u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assert", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(85u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trivial", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85____closed__1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126____closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(126u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85____closed__1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167____closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(167u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("store", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85____closed__1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208____closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(208u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subst", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(249u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__3;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__4;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("search", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290____closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(290u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("split", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290____closed__1;
x_5 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331____closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(331u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331____closed__2;
x_3 = 1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assign", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290____closed__1;
x_5 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373____closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(373u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373____closed__2;
x_3 = 1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("conflict", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290____closed__1;
x_5 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415____closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(415u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415____closed__2;
x_3 = 1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("backtrack", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290____closed__1;
x_5 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457____closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(457u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457____closed__2;
x_3 = 1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internalize", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499____closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(499u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Lean_Util_Trace(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_Trace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__3);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__4 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__4);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__5 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__5);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__6 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__6();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__6);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__7 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__7();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__7);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__8 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__8();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__8);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__9 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__9();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__9);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__10 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__10();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__10);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__11 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__11();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__11);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__12 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__12();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__12);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__13 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__13();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__13);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__14 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__14();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__14);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__15 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__15();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__15);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__16 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__16();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__16);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__17 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__17();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__17);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__18 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__18();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__18);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__19 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__19();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__19);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__20 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__20();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__20);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__21 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__21();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__21);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__23 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__23();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__23);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__3);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__4 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249____closed__4);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
