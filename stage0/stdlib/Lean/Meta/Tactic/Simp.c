// Lean compiler output
// Module: Lean.Meta.Tactic.Simp
// Imports: Init Lean.Meta.Tactic.Simp.SimpTheorems Lean.Meta.Tactic.Simp.SimpCongrTheorems Lean.Meta.Tactic.Simp.Types Lean.Meta.Tactic.Simp.Main Lean.Meta.Tactic.Simp.Rewrite Lean.Meta.Tactic.Simp.SimpAll
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
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_63_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_18_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_48_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_33_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__4;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__5;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__5;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_63____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_63____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_48____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_48____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_18____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_18____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__4;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_33____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__6;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_33____closed__2;
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__2;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simp", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__4;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__6;
x_3 = 0;
x_4 = l_Lean_registerTraceClass(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_18____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("congr", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_18____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__6;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_18____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_18_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_18____closed__2;
x_3 = 1;
x_4 = l_Lean_registerTraceClass(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_33____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("discharge", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_33____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__6;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_33____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_33_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_33____closed__2;
x_3 = 1;
x_4 = l_Lean_registerTraceClass(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_48____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rewrite", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_48____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__6;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_48____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_48_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_48____closed__2;
x_3 = 1;
x_4 = l_Lean_registerTraceClass(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_63____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unify", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_63____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__6;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_63____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_63_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_63____closed__2;
x_3 = 1;
x_4 = l_Lean_registerTraceClass(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Debug", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__2;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__3;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__4;
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__5;
x_3 = 0;
x_4 = l_Lean_registerTraceClass(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpTheorems(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpAll(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__3);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__4 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__4);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__5 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__5);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__6 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__6();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4____closed__6);
res = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_18____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_18____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_18____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_18____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_18____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_18____closed__2);
res = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_18_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_33____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_33____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_33____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_33____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_33____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_33____closed__2);
res = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_33_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_48____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_48____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_48____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_48____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_48____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_48____closed__2);
res = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_48_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_63____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_63____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_63____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_63____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_63____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_63____closed__2);
res = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_63_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__1);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__2);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__3);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__4 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__4);
l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__5 = _init_l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78____closed__5);
res = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
