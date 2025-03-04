// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat
// Imports: Lean.Util.Trace Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr Lean.Meta.Tactic.Grind.Arith.Cutsat.Search Lean.Meta.Tactic.Grind.Arith.Cutsat.Inv Lean.Meta.Tactic.Grind.Arith.Cutsat.Proof Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Lean.Meta.Tactic.Grind.Arith.Cutsat.Util Lean.Meta.Tactic.Grind.Arith.Cutsat.Var Lean.Meta.Tactic.Grind.Arith.Cutsat.EqCnstr
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
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_876_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_168____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_292____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_333____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_333____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_834____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_543____closed__3;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_750_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85____closed__3;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_543_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_959____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_543____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_792____closed__1;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_792_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_668____closed__2;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_626_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_750____closed__2;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_709_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_459____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__8;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_417____closed__2;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_210_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_876____closed__2;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_168_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_251____closed__3;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_585_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_626____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_375____closed__2;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_292_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_333____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__18;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__6;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85____closed__2;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__23;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_543____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__10;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_417____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_459____closed__1;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_251_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_501____closed__3;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_459_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_375_(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_792____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_585____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_709____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__20;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__19;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_210____closed__3;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_959_(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_876____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__21;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_210____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__17;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_668____closed__3;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__9;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_668____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_501____closed__1;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_417_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_834____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_251____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__16;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_375____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_959____closed__3;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_210____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__4;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__15;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_834_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_834____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_750____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__12;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_292____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_459____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_876____closed__3;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__5;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_918____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_168____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__13;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__7;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_168____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_626____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_959____closed__2;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_501_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_585____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_251____closed__1;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_333_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44____closed__3;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_501____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_918____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__11;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_668_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_626____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_44____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__14;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_918_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_709____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_585____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_918____closed__1;
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
x_1 = lean_mk_string_unchecked("subst", 5, 5);
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
x_1 = lean_mk_string_unchecked("eq", 2, 2);
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
x_1 = lean_mk_string_unchecked("unsat", 5, 5);
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
x_3 = 1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_168____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trivial", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_168____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_85____closed__1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_168____closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_168____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(168u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_168_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_168____closed__2;
x_3 = 1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_168____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_210____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assert", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_210____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_210____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_210____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(210u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_210_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_210____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_210____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_251____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dvd", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_251____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_210____closed__1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_251____closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_251____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(251u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_251_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_251____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_251____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_292____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_251____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_292____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(292u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_292_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_292____closed__1;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_292____closed__2;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_333____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("update", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_333____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_251____closed__1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_333____closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_333____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(333u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_333_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_333____closed__2;
x_3 = 1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_333____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_375____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_251____closed__1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126____closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_375____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(375u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_375_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_375____closed__1;
x_3 = 1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_375____closed__2;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_417____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_251____closed__1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_168____closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_417____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(417u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_417_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_417____closed__1;
x_3 = 1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_417____closed__2;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_459____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("solve", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_459____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_251____closed__1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_459____closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_459____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(459u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_459_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_459____closed__2;
x_3 = 1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_459____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_501____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("combine", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_501____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_251____closed__1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_459____closed__1;
x_5 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_501____closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_501____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(501u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_501_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_501____closed__2;
x_3 = 1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_501____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_543____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elim", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_543____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_251____closed__1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_459____closed__1;
x_5 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_543____closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_543____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(543u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_543_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_543____closed__2;
x_3 = 1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_543____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_585____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internalize", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_585____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_585____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_585____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(585u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_585_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_585____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_585____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_626____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_626____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_585____closed__1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_626____closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_626____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(626u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_626_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_626____closed__2;
x_3 = 1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_626____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_668____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_668____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_210____closed__1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_668____closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_668____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(668u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_668_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_668____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_668____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_709____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_668____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_709____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(709u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_709_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_709____closed__1;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_709____closed__2;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_750____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_668____closed__1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_126____closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_750____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(750u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_750_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_750____closed__1;
x_3 = 1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_750____closed__2;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_792____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_668____closed__1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_168____closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_792____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(792u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_792_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_792____closed__1;
x_3 = 1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_792____closed__2;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_834____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lower", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_834____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_668____closed__1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_834____closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_834____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(834u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_834_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_834____closed__2;
x_3 = 1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_834____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_876____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("upper", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_876____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_668____closed__1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_876____closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_876____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(876u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_876_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_876____closed__2;
x_3 = 1;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_876____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_918____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assign", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_918____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_918____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_918____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(918u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_918_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_918____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_918____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_959____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("conflict", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_959____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_959____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_959____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_3____closed__22;
x_2 = lean_unsigned_to_nat(959u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_959_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_959____closed__2;
x_3 = 0;
x_4 = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_959____closed__3;
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
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_168____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_168____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_168____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_168____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_168____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_168____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_168____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_168____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_168____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_168_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_210____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_210____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_210____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_210____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_210____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_210____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_210____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_210____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_210____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_210_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_251____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_251____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_251____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_251____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_251____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_251____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_251____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_251____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_251____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_251_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_292____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_292____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_292____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_292____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_292____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_292____closed__2);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_292_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_333____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_333____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_333____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_333____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_333____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_333____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_333____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_333____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_333____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_333_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_375____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_375____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_375____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_375____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_375____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_375____closed__2);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_375_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_417____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_417____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_417____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_417____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_417____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_417____closed__2);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_417_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_459____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_459____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_459____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_459____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_459____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_459____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_459____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_459____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_459____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_459_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_501____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_501____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_501____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_501____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_501____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_501____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_501____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_501____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_501____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_501_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_543____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_543____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_543____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_543____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_543____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_543____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_543____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_543____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_543____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_543_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_585____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_585____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_585____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_585____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_585____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_585____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_585____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_585____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_585____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_585_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_626____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_626____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_626____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_626____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_626____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_626____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_626____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_626____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_626____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_626_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_668____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_668____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_668____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_668____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_668____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_668____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_668____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_668____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_668____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_668_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_709____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_709____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_709____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_709____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_709____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_709____closed__2);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_709_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_750____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_750____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_750____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_750____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_750____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_750____closed__2);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_750_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_792____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_792____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_792____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_792____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_792____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_792____closed__2);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_792_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_834____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_834____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_834____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_834____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_834____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_834____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_834____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_834____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_834____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_834_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_876____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_876____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_876____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_876____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_876____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_876____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_876____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_876____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_876____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_876_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_918____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_918____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_918____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_918____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_918____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_918____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_918____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_918____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_918____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_918_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_959____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_959____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_959____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_959____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_959____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_959____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_959____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_959____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_959____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat___hyg_959_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
