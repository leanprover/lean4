// Lean compiler output
// Module: Lean.Compiler.Main
// Imports: Lean.Compiler.LCNF
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
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__7;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__6;
lean_object* l_Lean_MessageData_ofList(lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__2;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__3;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Compiler_LCNF_compile(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_compile___lambda__1___closed__2;
static lean_object* l_Lean_Compiler_compile___lambda__1___closed__1;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__8;
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__9;
lean_object* l_Lean_profileitM___at_Lean_Compiler_LCNF_main___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__15;
static lean_object* l_Lean_Compiler_compile___lambda__1___closed__4;
static lean_object* l_Lean_Compiler_compile___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_compile(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__10;
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89_(lean_object*);
static lean_object* l_Lean_Compiler_compile___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__4;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__16;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__12;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__14;
static lean_object* l_Lean_Compiler_compile___closed__3;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__11;
lean_object* l_List_mapTR_loop___at_Lean_compileDecl___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_compile___closed__1;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__13;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__5;
static lean_object* _init_l_Lean_Compiler_compile___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compiling: ", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_compile___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_compile___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_compile___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_compile___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_compile___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_to_list(x_1);
x_7 = lean_box(0);
x_8 = l_List_mapTR_loop___at_Lean_compileDecl___spec__1(x_6, x_7);
x_9 = l_Lean_MessageData_ofList(x_8);
x_10 = l_Lean_Compiler_compile___lambda__1___closed__2;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_Compiler_compile___lambda__1___closed__4;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_1 = lean_mk_string_unchecked("Compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_compile___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_compile___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_compile___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compiler new", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Compiler_compile___lambda__1___boxed), 5, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_compile___lambda__2), 4, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Compiler_compile___closed__2;
x_9 = 1;
x_10 = l_Lean_Compiler_compile___lambda__1___closed__3;
x_11 = lean_box(x_9);
x_12 = lean_alloc_closure((void*)(l_Lean_withTraceNode___at_Lean_Compiler_LCNF_main___spec__1___boxed), 8, 5);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_6);
lean_closure_set(x_12, 2, x_7);
lean_closure_set(x_12, 3, x_11);
lean_closure_set(x_12, 4, x_10);
x_13 = l_Lean_Compiler_compile___closed__3;
x_14 = lean_box(0);
x_15 = l_Lean_profileitM___at_Lean_Compiler_LCNF_main___spec__3___rarg(x_13, x_5, x_12, x_14, x_2, x_3, x_4);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_compile___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__2;
x_2 = l_Lean_Compiler_compile___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__3;
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__5;
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__7;
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__8;
x_2 = l_Lean_Compiler_compile___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Main", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__9;
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__11;
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__13;
x_2 = lean_unsigned_to_nat(89u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stat", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_compile___closed__1;
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__15;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_compile___closed__2;
x_3 = 0;
x_4 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__14;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__16;
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
lean_object* initialize_Lean_Compiler_LCNF(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_Main(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_compile___lambda__1___closed__1 = _init_l_Lean_Compiler_compile___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_compile___lambda__1___closed__1);
l_Lean_Compiler_compile___lambda__1___closed__2 = _init_l_Lean_Compiler_compile___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Compiler_compile___lambda__1___closed__2);
l_Lean_Compiler_compile___lambda__1___closed__3 = _init_l_Lean_Compiler_compile___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Compiler_compile___lambda__1___closed__3);
l_Lean_Compiler_compile___lambda__1___closed__4 = _init_l_Lean_Compiler_compile___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Compiler_compile___lambda__1___closed__4);
l_Lean_Compiler_compile___closed__1 = _init_l_Lean_Compiler_compile___closed__1();
lean_mark_persistent(l_Lean_Compiler_compile___closed__1);
l_Lean_Compiler_compile___closed__2 = _init_l_Lean_Compiler_compile___closed__2();
lean_mark_persistent(l_Lean_Compiler_compile___closed__2);
l_Lean_Compiler_compile___closed__3 = _init_l_Lean_Compiler_compile___closed__3();
lean_mark_persistent(l_Lean_Compiler_compile___closed__3);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__1 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__1();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__1);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__2 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__2();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__2);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__3 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__3();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__3);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__4 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__4();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__4);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__5 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__5();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__5);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__6 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__6();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__6);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__7 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__7();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__7);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__8 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__8();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__8);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__9 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__9();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__9);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__10 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__10();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__10);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__11 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__11();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__11);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__12 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__12();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__12);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__13 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__13();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__13);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__14 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__14();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__14);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__15 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__15();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__15);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__16 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__16();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89____closed__16);
if (builtin) {res = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
