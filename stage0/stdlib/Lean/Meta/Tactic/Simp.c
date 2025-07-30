// Lean compiler output
// Module: Lean.Meta.Tactic.Simp
// Imports: Lean.Meta.Tactic.Simp.SimpTheorems Lean.Meta.Tactic.Simp.SimpCongrTheorems Lean.Meta.Tactic.Simp.Types Lean.Meta.Tactic.Simp.Main Lean.Meta.Tactic.Simp.Rewrite Lean.Meta.Tactic.Simp.SimpAll Lean.Meta.Tactic.Simp.Simproc Lean.Meta.Tactic.Simp.BuiltinSimprocs Lean.Meta.Tactic.Simp.RegisterCommand Lean.Meta.Tactic.Simp.Attr Lean.Meta.Tactic.Simp.Diagnostics Lean.Meta.Tactic.Simp.Arith
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_451_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_353_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_253_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_153_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Simp___hyg_4_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Simp___hyg_4_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_203_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Simp___hyg_4_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Simp___hyg_4_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_500_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_153_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__24____x40_Lean_Meta_Tactic_Simp___hyg_4_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_353_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_103_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_402_;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_303_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_4_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Simp___hyg_4_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Simp___hyg_4_;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Simp___hyg_4_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_53_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_253_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_153_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Simp___hyg_4_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_4_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Simp___hyg_4_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_103_;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Simp___hyg_4_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_253_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_303_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_203_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Simp___hyg_4_;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_402_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Simp___hyg_4_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Simp___hyg_4_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_451_;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_303_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_53_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_451_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Simp___hyg_4_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_103_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Simp___hyg_4_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Simp___hyg_4_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_451_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Simp___hyg_4_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_203_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_500_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_53_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_53_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_103_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Simp___hyg_4_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_253_(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_203_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_353_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_303_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Simp___hyg_4_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_500_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_153_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_353_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_402_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23____x40_Lean_Meta_Tactic_Simp___hyg_4_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Simp___hyg_4_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_4_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_402_;
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Simp___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Simp___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Simp___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Simp___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Simp___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Simp___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Simp___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Simp___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Simp___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Simp___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Simp___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Simp___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Simp___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Simp___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Simp___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Simp___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Simp___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Simp___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Simp___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Simp___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23____x40_Lean_Meta_Tactic_Simp___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__24____x40_Lean_Meta_Tactic_Simp___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = 0;
x_4 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__24____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_53_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congr", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_53_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_53_;
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_4 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_53_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(53u);
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_53_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_53_;
x_3 = 1;
x_4 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_53_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_103_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("discharge", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_103_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_103_;
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_4 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_103_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(103u);
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_103_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_103_;
x_3 = 1;
x_4 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_103_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_153_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rewrite", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_153_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_153_;
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_4 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_153_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(153u);
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_153_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_153_;
x_3 = 1;
x_4 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_153_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_203_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unify", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_203_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_203_;
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_4 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_203_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(203u);
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_203_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_203_;
x_3 = 1;
x_4 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_203_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_253_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ground", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_253_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_253_;
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_4 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_253_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(253u);
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_253_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_253_;
x_3 = 1;
x_4 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_253_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_303_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("loopProtection", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_303_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_303_;
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_4 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_303_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(303u);
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_303_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_303_;
x_3 = 1;
x_4 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_303_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_353_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("numSteps", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_353_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_353_;
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_4 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_353_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(353u);
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_353_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_353_;
x_3 = 0;
x_4 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_353_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_402_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("heads", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_402_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_402_;
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_4 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_402_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(402u);
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_402_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_402_;
x_3 = 0;
x_4 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_402_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_451_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_451_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_4 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_451_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_451_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(451u);
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_451_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_451_;
x_3 = 0;
x_4 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_451_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_500_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_53_;
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_4 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_5 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_451_;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_500_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(500u);
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23____x40_Lean_Meta_Tactic_Simp___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_500_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_500_;
x_3 = 1;
x_4 = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_500_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpTheorems(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpAll(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_RegisterCommand(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Diagnostics(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_SimpAll(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_RegisterCommand(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Attr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Diagnostics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Arith(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_4_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_4_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_4_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_4_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_4_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_4_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_4_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_4_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_4_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Simp___hyg_4_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Simp___hyg_4_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Simp___hyg_4_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Simp___hyg_4_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Simp___hyg_4_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Simp___hyg_4_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Simp___hyg_4_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Simp___hyg_4_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Simp___hyg_4_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Simp___hyg_4_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Simp___hyg_4_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Simp___hyg_4_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Simp___hyg_4_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Simp___hyg_4_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Simp___hyg_4_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Simp___hyg_4_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Simp___hyg_4_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Simp___hyg_4_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Simp___hyg_4_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Simp___hyg_4_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Simp___hyg_4_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Simp___hyg_4_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Simp___hyg_4_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Simp___hyg_4_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Simp___hyg_4_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Simp___hyg_4_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Simp___hyg_4_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Simp___hyg_4_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Simp___hyg_4_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Simp___hyg_4_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Simp___hyg_4_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Simp___hyg_4_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Simp___hyg_4_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Simp___hyg_4_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Simp___hyg_4_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Simp___hyg_4_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Simp___hyg_4_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Simp___hyg_4_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Simp___hyg_4_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Simp___hyg_4_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Simp___hyg_4_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Simp___hyg_4_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Simp___hyg_4_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Simp___hyg_4_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Simp___hyg_4_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Simp___hyg_4_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Simp___hyg_4_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__18____x40_Lean_Meta_Tactic_Simp___hyg_4_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Simp___hyg_4_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Simp___hyg_4_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__19____x40_Lean_Meta_Tactic_Simp___hyg_4_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Simp___hyg_4_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Simp___hyg_4_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__20____x40_Lean_Meta_Tactic_Simp___hyg_4_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Simp___hyg_4_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Simp___hyg_4_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21____x40_Lean_Meta_Tactic_Simp___hyg_4_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Simp___hyg_4_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Simp___hyg_4_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__22____x40_Lean_Meta_Tactic_Simp___hyg_4_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23____x40_Lean_Meta_Tactic_Simp___hyg_4_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23____x40_Lean_Meta_Tactic_Simp___hyg_4_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23____x40_Lean_Meta_Tactic_Simp___hyg_4_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__24____x40_Lean_Meta_Tactic_Simp___hyg_4_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__24____x40_Lean_Meta_Tactic_Simp___hyg_4_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__24____x40_Lean_Meta_Tactic_Simp___hyg_4_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_53_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_53_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_53_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_53_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_53_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_53_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_53_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_53_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_53_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_53_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_103_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_103_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_103_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_103_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_103_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_103_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_103_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_103_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_103_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_103_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_153_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_153_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_153_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_153_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_153_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_153_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_153_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_153_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_153_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_153_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_203_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_203_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_203_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_203_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_203_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_203_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_203_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_203_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_203_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_203_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_253_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_253_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_253_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_253_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_253_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_253_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_253_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_253_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_253_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_253_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_303_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_303_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_303_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_303_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_303_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_303_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_303_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_303_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_303_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_303_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_353_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_353_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_353_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_353_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_353_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_353_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_353_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_353_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_353_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_353_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_402_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_402_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_402_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_402_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_402_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_402_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_402_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_402_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_402_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_402_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_451_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_451_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_451_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_451_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_451_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_451_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_451_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_451_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Simp___hyg_451_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_451_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_500_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_500_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Simp___hyg_500_);
l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_500_ = _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_500_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Simp___hyg_500_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_500_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
