// Lean compiler output
// Module: Init.SizeOf
// Imports: Init.Notation
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
lean_object* l_instSizeOf(lean_object*);
lean_object* l_instSizeOfNat(lean_object*);
lean_object* l_instSizeOf___closed__1;
lean_object* l_Lean_Name_sizeOf_match__1(lean_object*);
lean_object* l_default_sizeOf___boxed(lean_object*, lean_object*);
lean_object* l_instSizeOfNat___boxed(lean_object*);
lean_object* l_default_sizeOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_sizeOf_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_default_sizeOf(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
lean_object* l_default_sizeOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_default_sizeOf(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
#define _init_l_instSizeOf___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l_default_sizeOf___boxed), 2, 1);\
lean_closure_set(x_1, 0, lean_box(0));\
__INIT_VAR__ = x_1; goto l_instSizeOf___closed__1_end;\
}\
l_instSizeOf___closed__1_end: ((void) 0);}
lean_object* l_instSizeOf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instSizeOf___closed__1;
return x_2;
}
}
lean_object* l_instSizeOfNat(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_instSizeOfNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instSizeOfNat(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Name_sizeOf_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_10 = lean_box_uint64(x_9);
x_11 = lean_apply_3(x_3, x_7, x_8, x_10);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_15 = lean_box_uint64(x_14);
x_16 = lean_apply_3(x_4, x_12, x_13, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_Name_sizeOf_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Name_sizeOf_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* initialize_Init_Notation(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_SizeOf(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Notation(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
_init_l_instSizeOf___closed__1(l_instSizeOf___closed__1);
lean_mark_persistent(l_instSizeOf___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
