// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing
// Imports: Lean.Util.Trace Lean.Meta.Tactic.Grind.Arith.CommRing.Poly Lean.Meta.Tactic.Grind.Arith.CommRing.Types Lean.Meta.Tactic.Grind.Arith.CommRing.RingId Lean.Meta.Tactic.Grind.Arith.CommRing.Internalize Lean.Meta.Tactic.Grind.Arith.CommRing.ToExpr Lean.Meta.Tactic.Grind.Arith.CommRing.Var Lean.Meta.Tactic.Grind.Arith.CommRing.Reify Lean.Meta.Tactic.Grind.Arith.CommRing.EqCnstr Lean.Meta.Tactic.Grind.Arith.CommRing.Proof Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr Lean.Meta.Tactic.Grind.Arith.CommRing.Inv Lean.Meta.Tactic.Grind.Arith.CommRing.PP
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
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_418_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
static lean_object* l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
static lean_object* l_Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
static lean_object* l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_664_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_500_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_664_;
static lean_object* l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_252_;
static lean_object* l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_44_;
static lean_object* l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
static lean_object* l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_168_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_459_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_252_(lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_126_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_500_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_294_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_336_(lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_168_;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_541_;
static lean_object* l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_623_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_44_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_705_(lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_210_;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_294_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_377_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_126_(lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_377_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_377_(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_582_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_705_;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_582_(lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_336_;
static lean_object* l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_459_;
static lean_object* l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_210_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_418_;
static lean_object* l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
static lean_object* l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_541_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_44_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_623_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_294_(lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_126_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_500_(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_294_;
static lean_object* l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_377_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_168_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_459_(lean_object*);
static lean_object* l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_210_(lean_object*);
static lean_object* l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_336_;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_500_;
static lean_object* l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
static lean_object* l_Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_623_(lean_object*);
static lean_object* l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_252_;
static lean_object* l_Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_168_(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_541_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_582_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_541_(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_418_;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_336_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_623_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_705_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_126_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_664_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_418_(lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_44_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_210_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_252_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_459_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_705_;
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ring", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_2 = l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_2 = l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_2 = l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_2 = l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_2 = l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_2 = l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Arith", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_2 = l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("CommRing", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_2 = l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_2 = l_Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = 0;
x_4 = l_Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_44_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internalize", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_44_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_44_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_44_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(44u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_44_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_44_;
x_3 = 0;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_44_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assert", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(85u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_;
x_3 = 0;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_126_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_126_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_126_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_126_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(126u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_126_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_126_;
x_3 = 1;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_126_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_168_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trivial", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_168_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_168_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_168_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(168u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_168_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_168_;
x_3 = 1;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_168_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_210_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("queue", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_210_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_210_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_210_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(210u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_210_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_210_;
x_3 = 1;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_210_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_252_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("basis", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_252_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_252_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_252_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(252u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_252_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_252_;
x_3 = 1;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_252_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_294_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("store", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_294_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_294_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_294_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(294u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_294_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_294_;
x_3 = 1;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_294_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_336_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_336_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_336_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_336_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(336u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_336_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_336_;
x_3 = 0;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_336_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_377_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("superpose", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_377_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_377_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_377_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(377u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_377_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_377_;
x_3 = 0;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_377_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_418_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("impEq", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_418_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_418_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_418_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(418u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_418_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_418_;
x_3 = 0;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_418_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_459_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_459_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_336_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_459_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_459_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(459u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_459_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_459_;
x_3 = 0;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_459_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_500_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proof", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_500_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_500_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_459_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_500_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(500u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_500_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_500_;
x_3 = 0;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_500_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_541_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("check", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_541_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_541_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_459_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_541_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(541u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_541_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_541_;
x_3 = 0;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_541_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_582_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_418_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_459_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_582_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(582u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_582_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_582_;
x_3 = 0;
x_4 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_582_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_623_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpBasis", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_623_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_623_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_459_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_623_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(623u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_623_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_623_;
x_3 = 0;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_623_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_664_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_252_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_459_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_664_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(664u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_664_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_664_;
x_3 = 0;
x_4 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_664_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_705_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rabinowitsch", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_705_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_705_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_459_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_705_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(705u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_705_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_705_;
x_3 = 0;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_705_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Lean_Util_Trace(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_ToExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Var(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Proof(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_PP(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_Trace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_ToExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Var(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Proof(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_PP(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_);
l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_ = _init_l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_);
l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_ = _init_l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_);
l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_ = _init_l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_);
l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_ = _init_l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_);
l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_ = _init_l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_);
l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_ = _init_l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_);
l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_ = _init_l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_);
l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_ = _init_l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_);
l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_ = _init_l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_);
l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_ = _init_l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_);
l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_ = _init_l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_);
l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_ = _init_l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_);
l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_ = _init_l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_);
l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_ = _init_l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_);
l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_ = _init_l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_);
l_Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_ = _init_l_Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_);
l_Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_ = _init_l_Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_);
l_Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_ = _init_l_Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_);
l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_ = _init_l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_);
l_Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_ = _init_l_Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_44_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_44_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_44_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_44_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_44_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_44_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_44_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_44_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_44_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_44_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_126_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_126_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_126_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_126_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_126_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_126_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_126_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_126_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_126_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_126_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_168_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_168_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_168_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_168_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_168_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_168_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_168_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_168_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_168_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_168_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_210_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_210_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_210_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_210_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_210_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_210_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_210_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_210_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_210_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_210_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_252_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_252_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_252_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_252_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_252_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_252_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_252_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_252_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_252_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_252_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_294_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_294_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_294_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_294_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_294_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_294_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_294_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_294_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_294_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_294_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_336_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_336_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_336_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_336_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_336_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_336_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_336_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_336_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_336_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_336_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_377_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_377_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_377_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_377_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_377_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_377_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_377_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_377_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_377_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_377_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_418_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_418_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_418_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_418_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_418_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_418_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_418_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_418_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_418_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_418_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_459_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_459_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_459_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_459_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_459_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_459_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_459_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_459_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_459_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_459_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_500_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_500_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_500_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_500_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_500_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_500_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_500_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_500_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_500_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_500_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_541_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_541_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_541_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_541_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_541_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_541_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_541_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_541_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_541_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_541_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_582_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_582_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_582_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_582_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_582_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_582_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_582_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_623_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_623_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_623_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_623_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_623_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_623_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_623_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_623_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_623_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_623_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_664_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_664_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_664_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_664_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_664_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_664_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_664_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_705_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_705_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_705_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_705_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_705_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_705_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_705_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_705_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_705_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_705_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
