// Lean compiler output
// Module: Lean.Elab.Tactic.Location
// Imports: Init
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
lean_object* l_Lean_Elab_Tactic_expandOptLocation___boxed(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandLocation___boxed(lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__4;
lean_object* l_Lean_Elab_Tactic_expandLocation___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandLocation___closed__6;
lean_object* l_Lean_Elab_Tactic_expandLocation___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
lean_object* l_Lean_Elab_Tactic_expandLocation(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_expandLocation___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandLocation___closed__4;
lean_object* l_Lean_Elab_Tactic_expandLocation___closed__3;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_Tactic_expandLocation___closed__5;
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_expandLocation___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = x_2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = x_6;
x_10 = l_Lean_Syntax_getId(x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
x_13 = x_10;
x_14 = lean_array_fset(x_8, x_1, x_13);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_14;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_expandLocation___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Tactic");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_expandLocation___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__4;
x_2 = l_Lean_Elab_Tactic_expandLocation___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_expandLocation___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("locationWildcard");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_expandLocation___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_expandLocation___closed__2;
x_2 = l_Lean_Elab_Tactic_expandLocation___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_expandLocation___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("locationTarget");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_expandLocation___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_expandLocation___closed__2;
x_2 = l_Lean_Elab_Tactic_expandLocation___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_expandLocation(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
lean_inc(x_3);
x_4 = l_Lean_Syntax_getKind(x_3);
x_5 = l_Lean_Elab_Tactic_expandLocation___closed__4;
x_6 = lean_name_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Elab_Tactic_expandLocation___closed__6;
x_8 = lean_name_eq(x_4, x_7);
lean_dec(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_3, x_9);
lean_dec(x_3);
x_11 = l_Lean_Syntax_getArgs(x_10);
lean_dec(x_10);
x_12 = x_11;
x_13 = l_Array_umapMAux___main___at_Lean_Elab_Tactic_expandLocation___spec__1(x_9, x_12);
x_14 = x_13;
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_3);
x_16 = lean_box(1);
return x_16;
}
}
else
{
lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_3);
x_17 = lean_box(0);
return x_17;
}
}
}
lean_object* l_Lean_Elab_Tactic_expandLocation___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_expandLocation(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Syntax_isNone(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Syntax_getArg(x_1, x_3);
x_5 = l_Lean_Elab_Tactic_expandLocation(x_4);
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_box(1);
return x_6;
}
}
}
lean_object* l_Lean_Elab_Tactic_expandOptLocation___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_expandOptLocation(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Tactic_Location(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_expandLocation___closed__1 = _init_l_Lean_Elab_Tactic_expandLocation___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_expandLocation___closed__1);
l_Lean_Elab_Tactic_expandLocation___closed__2 = _init_l_Lean_Elab_Tactic_expandLocation___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_expandLocation___closed__2);
l_Lean_Elab_Tactic_expandLocation___closed__3 = _init_l_Lean_Elab_Tactic_expandLocation___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_expandLocation___closed__3);
l_Lean_Elab_Tactic_expandLocation___closed__4 = _init_l_Lean_Elab_Tactic_expandLocation___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_expandLocation___closed__4);
l_Lean_Elab_Tactic_expandLocation___closed__5 = _init_l_Lean_Elab_Tactic_expandLocation___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_expandLocation___closed__5);
l_Lean_Elab_Tactic_expandLocation___closed__6 = _init_l_Lean_Elab_Tactic_expandLocation___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_expandLocation___closed__6);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
