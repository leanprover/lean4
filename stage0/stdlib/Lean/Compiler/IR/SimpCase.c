// Lean compiler output
// Module: Lean.Compiler.IR.SimpCase
// Imports: public import Lean.Compiler.IR.Basic
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_IR_Alt_isDefault(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_ensureHasDefault_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_ensureHasDefault_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedAlt_default__1;
lean_object* l_Array_back_x21___redArg(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_IR_Alt_body(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ensureHasDefault(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_ensureHasDefault_spec__0(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget_borrowed(x_1, x_2);
x_6 = l_Lean_IR_Alt_isDefault(x_5);
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
goto _start;
}
else
{
return x_6;
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_ensureHasDefault_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_ensureHasDefault_spec__0(x_1, x_4, x_5);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ensureHasDefault(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_13; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_2, x_3);
if (x_13 == 0)
{
goto block_12;
}
else
{
if (x_13 == 0)
{
goto block_12;
}
else
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_3);
x_16 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_ensureHasDefault_spec__0(x_1, x_14, x_15);
if (x_16 == 0)
{
goto block_12;
}
else
{
return x_1;
}
}
}
block_12:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = l_Lean_IR_instInhabitedAlt_default__1;
x_7 = l_Array_back_x21___redArg(x_6, x_1);
x_8 = lean_array_pop(x_1);
x_9 = l_Lean_IR_Alt_body(x_7);
lean_dec(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_array_push(x_8, x_10);
return x_11;
}
else
{
return x_1;
}
}
}
}
lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_SimpCase(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
