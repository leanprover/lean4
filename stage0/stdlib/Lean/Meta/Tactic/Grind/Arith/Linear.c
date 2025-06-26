// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear
// Imports: Lean.Meta.Tactic.Grind.Arith.Linear.Types Lean.Meta.Tactic.Grind.Arith.Linear.Util Lean.Meta.Tactic.Grind.Arith.Linear.Var Lean.Meta.Tactic.Grind.Arith.Linear.StructId Lean.Meta.Tactic.Grind.Arith.Linear.IneqCnstr Lean.Meta.Tactic.Grind.Arith.Linear.Reify Lean.Meta.Tactic.Grind.Arith.Linear.DenoteExpr Lean.Meta.Tactic.Grind.Arith.Linear.ToExpr Lean.Meta.Tactic.Grind.Arith.Linear.Proof Lean.Meta.Tactic.Grind.Arith.Linear.SearchM Lean.Meta.Tactic.Grind.Arith.Linear.Search Lean.Meta.Tactic.Grind.Arith.Linear.PropagateEq Lean.Meta.Tactic.Grind.Arith.Linear.Internalize Lean.Meta.Tactic.Grind.Arith.Linear.Model Lean.Meta.Tactic.Grind.Arith.Linear.PP Lean.Meta.Tactic.Grind.Arith.Linear.MBTC
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
static lean_object* l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_460_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_;
static lean_object* l_Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_376_(lean_object*);
static lean_object* l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_293_(lean_object*);
static lean_object* l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
static lean_object* l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_544_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_126_(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_251_;
static lean_object* l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
static lean_object* l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_376_;
static lean_object* l_Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_502_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_126_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_44_(lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_85_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_293_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_502_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_251_(lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_544_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_209_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_376_;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_209_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_251_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_167_;
static lean_object* l_Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_418_(lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_502_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_44_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_293_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_167_;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_418_;
static lean_object* l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
static lean_object* l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_85_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_418_;
static lean_object* l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_293_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_544_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_167_(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_85_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_460_(lean_object*);
static lean_object* l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
static lean_object* l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_44_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_502_(lean_object*);
static lean_object* l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
static lean_object* l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_209_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_44_;
static lean_object* l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_376_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_460_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_(lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_418_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_126_;
static lean_object* l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
static lean_object* l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_251_;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_85_(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_544_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_126_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_209_(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_460_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_167_;
static lean_object* l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("linarith", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_2 = l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_2 = l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_2 = l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_2 = l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_2 = l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_2 = l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Arith", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_2 = l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Linear", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_2 = l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_2 = l_Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_44_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internalize", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_44_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_44_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_44_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(44u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_44_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_44_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_44_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_85_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assert", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_85_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_85_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_85_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(85u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_85_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_85_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_85_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_126_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("model", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_126_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_126_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_126_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(126u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_126_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_126_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_126_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_167_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_167_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_167_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_85_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_167_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(167u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_167_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_167_;
x_3 = lean_box(1);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_167_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_209_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trivial", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_209_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_209_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_85_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_209_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(209u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_209_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_209_;
x_3 = lean_box(1);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_209_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_251_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("store", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_251_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_251_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_85_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_251_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(251u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_251_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_251_;
x_3 = lean_box(1);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_251_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_293_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ignored", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_293_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_293_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_85_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_293_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(293u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_293_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_293_;
x_3 = lean_box(1);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_293_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("search", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(335u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_376_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("conflict", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_376_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_376_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_;
x_5 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_376_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(376u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_376_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_376_;
x_3 = lean_box(1);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_376_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_418_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assign", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_418_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_418_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_;
x_5 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_418_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(418u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_418_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_418_;
x_3 = lean_box(1);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_418_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_460_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("split", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_460_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_460_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_;
x_5 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_460_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(460u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_460_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_460_;
x_3 = lean_box(1);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_460_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_502_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("backtrack", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_502_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_502_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_;
x_5 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_502_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(502u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_502_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_502_;
x_3 = lean_box(1);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_502_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_544_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subst", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_544_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_544_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_544_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(544u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_544_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_544_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_544_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Search(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Search(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_);
l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_ = _init_l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_);
l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_ = _init_l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_);
l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_ = _init_l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_);
l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_ = _init_l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_);
l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_ = _init_l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_);
l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_ = _init_l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_);
l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_ = _init_l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_);
l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_ = _init_l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_);
l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_ = _init_l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_);
l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_ = _init_l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_);
l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_ = _init_l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_);
l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_ = _init_l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_);
l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_ = _init_l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_);
l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_ = _init_l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_);
l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_ = _init_l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_);
l_Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_ = _init_l_Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_);
l_Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_ = _init_l_Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_);
l_Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_ = _init_l_Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_);
l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_ = _init_l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_);
l_Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_ = _init_l_Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_44_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_44_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_44_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_44_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_44_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_44_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_44_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_44_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_44_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_44_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_85_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_85_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_85_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_85_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_85_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_85_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_85_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_85_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_85_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_85_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_126_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_126_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_126_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_126_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_126_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_126_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_126_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_126_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_126_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_126_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_167_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_167_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_167_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_167_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_167_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_167_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_167_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_167_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_167_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_167_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_209_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_209_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_209_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_209_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_209_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_209_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_209_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_209_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_209_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_209_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_251_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_251_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_251_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_251_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_251_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_251_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_251_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_251_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_251_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_251_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_293_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_293_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_293_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_293_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_293_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_293_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_293_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_293_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_293_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_293_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_);
l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_ = _init_l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_();
lean_mark_persistent(l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_335_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_376_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_376_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_376_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_376_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_376_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_376_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_376_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_376_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_376_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_376_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_418_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_418_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_418_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_418_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_418_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_418_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_418_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_418_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_418_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_418_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_460_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_460_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_460_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_460_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_460_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_460_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_460_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_460_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_460_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_460_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_502_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_502_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_502_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_502_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_502_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_502_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_502_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_502_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_502_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_502_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_544_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_544_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_544_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_544_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_544_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_544_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_544_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_544_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_544_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_544_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
