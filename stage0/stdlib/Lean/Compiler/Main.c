// Lean compiler output
// Module: Lean.Compiler.Main
// Imports: Init Lean.Compiler.LCNF
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
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__10;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__13;
lean_object* l_Lean_Compiler_LCNF_compile(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__5;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__6;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__1;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__17;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50_(lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__7;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__12;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__4;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__14;
LEAN_EXPORT lean_object* l_Lean_Compiler_compile(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__11;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_profileitM___at_Lean_addDecl___spec__14___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__9;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__16;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__18;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__3;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__15;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__2;
static lean_object* l_Lean_Compiler_compile___closed__1;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__8;
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_compile(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_dec(x_7);
x_8 = lean_box(0);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_compile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("compiler new", 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_Compiler_compile___lambda__1), 4, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_Lean_Compiler_compile___closed__1;
x_8 = lean_box(0);
x_9 = l_Lean_profileitM___at_Lean_addDecl___spec__14___rarg(x_7, x_5, x_6, x_8, x_2, x_3, x_4);
lean_dec(x_5);
return x_9;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Compiler", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__4;
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initFn", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__5;
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_@", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__7;
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__9;
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__10;
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Main", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__11;
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_hyg", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__13;
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__15;
x_2 = lean_unsigned_to_nat(50u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("stat", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__1;
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__17;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__2;
x_3 = 0;
x_4 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__16;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__18;
x_8 = l_Lean_registerTraceClass(x_7, x_3, x_4, x_6);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_Main(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_compile___closed__1 = _init_l_Lean_Compiler_compile___closed__1();
lean_mark_persistent(l_Lean_Compiler_compile___closed__1);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__1 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__1();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__1);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__2 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__2();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__2);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__3 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__3();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__3);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__4 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__4();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__4);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__5 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__5();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__5);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__6 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__6();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__6);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__7 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__7();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__7);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__8 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__8();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__8);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__9 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__9();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__9);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__10 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__10();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__10);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__11 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__11();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__11);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__12 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__12();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__12);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__13 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__13();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__13);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__14 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__14();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__14);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__15 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__15();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__15);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__16 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__16();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__16);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__17 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__17();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__17);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__18 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__18();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50____closed__18);
if (builtin) {res = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_50_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
