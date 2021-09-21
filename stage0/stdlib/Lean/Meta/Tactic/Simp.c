// Lean compiler output
// Module: Lean.Meta.Tactic.Simp
// Imports: Init Lean.Meta.Tactic.Simp.SimpLemmas Lean.Meta.Tactic.Simp.CongrLemmas Lean.Meta.Tactic.Simp.Types Lean.Meta.Tactic.Simp.Main Lean.Meta.Tactic.Simp.Rewrite Lean.Meta.Tactic.Simp.SimpAll
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
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__4;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__5;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__5;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__4;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__6;
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Meta");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Tactic");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__2;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("simp");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__4;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__6;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Debug");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__2;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__3;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__4;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__5;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpLemmas(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_CongrLemmas(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Types(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Rewrite(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpAll(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_SimpLemmas(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_CongrLemmas(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Types(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Rewrite(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_SimpAll(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__3);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__4 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__4);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__5 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__5);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__6 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__6();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3____closed__6);
res = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__3);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__4 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__4);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__5 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12____closed__5);
res = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_12_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
