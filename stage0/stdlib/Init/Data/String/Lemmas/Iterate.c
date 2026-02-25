// Lean compiler output
// Module: Init.Data.String.Lemmas.Iterate
// Imports: public import Init.Data.String.Iterate public import Init.Data.Iterators.Consumers.Collect public import Init.Data.String.Lemmas.Splits import all Init.Data.String.Iterate import Init.Data.String.Termination import Init.Data.Iterators.Lemmas.Consumers.Collect import Init.ByCases import Init.Data.Iterators.Lemmas.Combinators.FilterMap import Init.Data.String.Lemmas.Basic import Init.Data.Iterators.Lemmas.Consumers.Loop
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Model_positionsFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Model_positionsFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Iterate_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Iterate_0__Std_Iter_toArray__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Model_revPositionsFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Model_revPositionsFrom___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_String_Model_positionsFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Model_positionsFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Iterate_0__String_Internal_ofToSliceWithProof_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Iterate_0__String_Internal_ofToSliceWithProof_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Iterate_0__String_Internal_ofToSliceWithProof_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Model_revPositionsFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Model_revPositionsFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Model_positionsFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_nat_sub(x_5, x_4);
x_7 = lean_nat_dec_eq(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_nat_add(x_4, x_2);
x_9 = lean_string_utf8_next_fast(x_3, x_8);
lean_dec(x_8);
x_10 = lean_nat_sub(x_9, x_4);
x_11 = l_String_Slice_Model_positionsFrom(x_1, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_2);
x_13 = lean_box(0);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Model_positionsFrom___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Model_positionsFrom(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Iterate_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
default: 
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_4, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Iterate_0__Std_Iter_toArray__eq__match__step_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_String_Lemmas_Iterate_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Model_revPositionsFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
x_7 = l_String_Slice_posLE(x_1, x_6);
x_8 = l_String_Slice_Model_revPositionsFrom(x_1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Model_revPositionsFrom___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Model_revPositionsFrom(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Model_positionsFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_string_utf8_next_fast(x_1, x_2);
x_6 = l_String_Model_positionsFrom(x_1, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_box(0);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_String_Model_positionsFrom___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Model_positionsFrom(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Iterate_0__String_Internal_ofToSliceWithProof_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_2, x_1, lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Iterate_0__String_Internal_ofToSliceWithProof_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_4, x_3, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Iterate_0__String_Internal_ofToSliceWithProof_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_String_Lemmas_Iterate_0__String_Internal_ofToSliceWithProof_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Model_revPositionsFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
x_9 = l_String_Slice_posLE(x_6, x_8);
lean_dec_ref(x_6);
x_10 = l_String_Model_revPositionsFrom(x_1, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec_ref(x_1);
x_12 = lean_box(0);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_String_Model_revPositionsFrom___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Model_revPositionsFrom(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Splits(uint8_t builtin);
lean_object* initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Lemmas_Iterate(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Splits(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
