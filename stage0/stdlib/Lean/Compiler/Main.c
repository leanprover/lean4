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
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_49____closed__4;
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Compiler_compile___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_49_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compile(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_compile_stage1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_49____closed__3;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_49____closed__1;
static lean_object* l_Lean_Compiler_compile___closed__1;
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Compiler_compile___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_profileitIOUnsafe___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_49____closed__2;
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Compiler_compile___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Compiler_compile___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_2(x_3, x_4, x_5);
x_8 = l_Lean_profileitIOUnsafe___rarg(x_1, x_2, x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Compiler_compile___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_profileitM___at_Lean_Compiler_compile___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_compile_stage1(x_1, x_2, x_3, x_4);
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_Compiler_compile___lambda__1), 4, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_Lean_Compiler_compile___closed__1;
x_8 = l_Lean_profileitM___at_Lean_Compiler_compile___spec__1___rarg(x_7, x_5, x_6, x_2, x_3, x_4);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Compiler_compile___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_profileitM___at_Lean_Compiler_compile___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_49____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Compiler", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_49____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_49____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_49____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("stat", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_49____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_49____closed__2;
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_49____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_49_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_49____closed__2;
x_3 = 0;
x_4 = l_Lean_registerTraceClass(x_2, x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_49____closed__4;
x_7 = l_Lean_registerTraceClass(x_6, x_3, x_5);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
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
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_49____closed__1 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_49____closed__1();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_49____closed__1);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_49____closed__2 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_49____closed__2();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_49____closed__2);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_49____closed__3 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_49____closed__3();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_49____closed__3);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_49____closed__4 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_49____closed__4();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_49____closed__4);
res = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_49_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
