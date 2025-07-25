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
static lean_object* l_Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
static lean_object* l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
static lean_object* l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
static lean_object* l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_252_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_545_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_545_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_419_;
static lean_object* l_Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_86_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_252_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_168_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_86_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_210_;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_294_(lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_419_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_45_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_377_(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_294_;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_168_(lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_545_;
static lean_object* l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_503_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_86_(lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_127_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_86_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_377_;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_45_(lean_object*);
static lean_object* l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
static lean_object* l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
static lean_object* l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_461_;
static lean_object* l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_461_;
static lean_object* l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_294_;
static lean_object* l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
static lean_object* l_Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_503_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_210_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_461_(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_45_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_168_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_294_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_127_(lean_object*);
static lean_object* l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_252_(lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_377_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_503_(lean_object*);
static lean_object* l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_210_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_252_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_545_(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_168_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_419_(lean_object*);
static lean_object* l_Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_461_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_377_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_210_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_127_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_127_;
static lean_object* l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
static lean_object* l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_45_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_419_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_503_;
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("linarith", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_2 = l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_2 = l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_2 = l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_2 = l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_2 = l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_2 = l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Arith", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_2 = l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Linear", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_2 = l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_2 = l_Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = 0;
x_4 = l_Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_45_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internalize", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_45_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_45_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_45_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(45u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_45_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_45_;
x_3 = 0;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_45_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_86_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assert", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_86_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_86_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_86_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(86u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_86_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_86_;
x_3 = 0;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_86_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_127_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("model", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_127_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_127_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_127_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(127u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_127_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_127_;
x_3 = 0;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_127_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_168_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_168_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_168_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_86_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_168_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(168u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_168_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_168_;
x_3 = 1;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_168_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_210_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trivial", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_210_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_210_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_86_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_210_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(210u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_210_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_210_;
x_3 = 1;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_210_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_252_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("store", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_252_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_252_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_86_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_252_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(252u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_252_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_252_;
x_3 = 1;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_252_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_294_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ignored", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_294_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_294_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_86_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_294_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(294u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_294_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_294_;
x_3 = 1;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_294_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("search", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(336u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_;
x_3 = 0;
x_4 = l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_377_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("conflict", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_377_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_377_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_;
x_5 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_377_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(377u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_377_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_377_;
x_3 = 1;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_377_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_419_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assign", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_419_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_419_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_;
x_5 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_419_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(419u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_419_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_419_;
x_3 = 1;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_419_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_461_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("split", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_461_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_461_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_;
x_5 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_461_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(461u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_461_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_461_;
x_3 = 1;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_461_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_503_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("backtrack", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_503_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_503_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_;
x_5 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_503_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(503u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_503_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_503_;
x_3 = 1;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_503_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_545_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subst", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_545_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_545_;
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_545_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(545u);
x_2 = l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_545_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_545_;
x_3 = 0;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_545_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
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
l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_);
l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_ = _init_l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_);
l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_ = _init_l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_);
l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_ = _init_l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_);
l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_ = _init_l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_);
l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_ = _init_l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_);
l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_ = _init_l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_);
l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_ = _init_l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_);
l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_ = _init_l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_);
l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_ = _init_l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_);
l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_ = _init_l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_);
l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_ = _init_l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_);
l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_ = _init_l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_);
l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_ = _init_l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_);
l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_ = _init_l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_);
l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_ = _init_l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_);
l_Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_ = _init_l_Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_);
l_Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_ = _init_l_Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_);
l_Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_ = _init_l_Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_);
l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_ = _init_l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_);
l_Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_ = _init_l_Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_45_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_45_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_45_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_45_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_45_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_45_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_45_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_45_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_45_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_45_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_86_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_86_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_86_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_86_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_86_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_86_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_86_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_86_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_86_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_86_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_127_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_127_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_127_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_127_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_127_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_127_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_127_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_127_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_127_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_127_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_168_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_168_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_168_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_168_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_168_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_168_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_168_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_168_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_168_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_168_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_210_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_210_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_210_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_210_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_210_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_210_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_210_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_210_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_210_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_210_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_252_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_252_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_252_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_252_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_252_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_252_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_252_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_252_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_252_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_252_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_294_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_294_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_294_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_294_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_294_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_294_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_294_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_294_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_294_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_294_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_);
l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_ = _init_l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_();
lean_mark_persistent(l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_336_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_377_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_377_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_377_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_377_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_377_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_377_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_377_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_377_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_377_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_377_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_419_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_419_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_419_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_419_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_419_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_419_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_419_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_419_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_419_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_419_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_461_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_461_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_461_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_461_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_461_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_461_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_461_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_461_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_461_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_461_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_503_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_503_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_503_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_503_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_503_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_503_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_503_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_503_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_503_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_503_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_545_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_545_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_545_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_545_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_545_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_545_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_545_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_545_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_545_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Linear___hyg_545_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
