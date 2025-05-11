// Lean compiler output
// Module: Std.Classes.Ord.Basic
// Imports: Init.Data.Ord
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
uint8_t l_instDecidableEqOrdering(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_beqOfOrd(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Classes_Ord_Basic_0__Ordering_swap_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_beqOfOrd___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Classes_Ord_Basic_0__Ordering_swap_match__1_splitter___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_beqOfOrd___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Classes_Ord_Basic_0__Ordering_swap_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Classes_Ord_Basic_0__Ordering_swap_match__1_splitter___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (x_1) {
case 0:
{
lean_inc(x_2);
return x_2;
}
case 1:
{
lean_inc(x_3);
return x_3;
}
default: 
{
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Classes_Ord_Basic_0__Ordering_swap_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Std_Classes_Ord_Basic_0__Ordering_swap_match__1_splitter___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Classes_Ord_Basic_0__Ordering_swap_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Std_Classes_Ord_Basic_0__Ordering_swap_match__1_splitter___rarg(x_5, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_beqOfOrd___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; 
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = 1;
x_7 = l_instDecidableEqOrdering(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_beqOfOrd(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Internal_beqOfOrd___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_beqOfOrd___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_Internal_beqOfOrd___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* initialize_Init_Data_Ord(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Classes_Ord_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Ord(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
