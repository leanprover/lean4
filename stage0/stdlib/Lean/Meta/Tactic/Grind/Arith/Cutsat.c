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
static lean_object* l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208_;
static lean_object* l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457_(lean_object*);
static lean_object* l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85_;
static lean_object* l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
static lean_object* l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
static lean_object* l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
static lean_object* l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457_;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167_;
static lean_object* l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208_;
static lean_object* l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415_;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85_;
static lean_object* l_Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
static lean_object* l_Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85_(lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457_;
static lean_object* l_Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167_(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208_(lean_object*);
static lean_object* l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415_;
static lean_object* l_Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44_(lean_object*);
static lean_object* l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
static lean_object* l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415_(lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331_;
static lean_object* l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499_(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_;
static lean_object* l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331_(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85_;
static lean_object* l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_(lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126_(lean_object*);
static lean_object* l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126_;
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cutsat", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_2 = l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_2 = l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_2 = l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_2 = l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_2 = l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_2 = l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Arith", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_2 = l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Cutsat", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_2 = l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_2 = l_Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("model", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(44u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assert", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(85u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trivial", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(126u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(167u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("store", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(208u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subst", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(249u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("search", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(290u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("split", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_;
x_5 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(331u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331_;
x_3 = lean_box(1);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assign", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_;
x_5 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(373u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373_;
x_3 = lean_box(1);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("conflict", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_;
x_5 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(415u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415_;
x_3 = lean_box(1);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("backtrack", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_;
x_5 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(457u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457_;
x_3 = lean_box(1);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internalize", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(499u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
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
l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_);
l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_ = _init_l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_);
l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_ = _init_l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_);
l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_ = _init_l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_);
l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_ = _init_l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_);
l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_ = _init_l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_);
l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_ = _init_l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_);
l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_ = _init_l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_);
l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_ = _init_l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_);
l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_ = _init_l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_);
l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_ = _init_l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_);
l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_ = _init_l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_);
l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_ = _init_l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_);
l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_ = _init_l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_);
l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_ = _init_l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_);
l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_ = _init_l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_);
l_Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_ = _init_l_Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_);
l_Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_ = _init_l_Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_);
l_Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_ = _init_l_Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_);
l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_ = _init_l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_);
l_Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_ = _init_l_Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_167_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_208_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_);
l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_ = _init_l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_();
lean_mark_persistent(l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_249_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_290_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_331_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_373_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_415_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_457_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_499_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
