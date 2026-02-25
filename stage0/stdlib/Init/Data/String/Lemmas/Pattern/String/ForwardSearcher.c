// Lean compiler output
// Module: Init.Data.String.Lemmas.Pattern.String.ForwardSearcher
// Imports: public import Init.Data.String.Lemmas.Pattern.String.Basic public import Init.Data.String.Pattern.String import all Init.Data.String.Pattern.String import Init.Data.String.Lemmas.IsEmpty import Init.Data.Vector.Lemmas import Init.Data.Iterators.Lemmas.Basic import Init.Data.Iterators.Lemmas.Consumers.Collect import Init.Data.String.Lemmas.Basic import Init.Data.String.OrderInstances
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
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Nat_decidableBallLT___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_7 = lean_byte_array_fget(x_1, x_5);
x_8 = lean_nat_sub(x_2, x_3);
x_9 = lean_nat_add(x_8, x_5);
lean_dec(x_8);
x_10 = lean_byte_array_fget(x_4, x_9);
lean_dec(x_9);
x_11 = lean_uint8_dec_eq(x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_byte_array_size(x_2);
x_6 = lean_nat_dec_le(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_byte_array_size(x_1);
x_8 = lean_nat_dec_le(x_3, x_7);
if (x_8 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_3, x_4);
if (x_9 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
lean_inc(x_3);
x_10 = lean_alloc_closure((void*)(l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___lam__0___boxed), 6, 4);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_2);
x_11 = l_Nat_decidableBallLT___redArg(x_3, x_10);
lean_dec(x_3);
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
lean_inc(x_3);
lean_inc_ref_n(x_1, 2);
x_6 = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch(x_1, x_1, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_nat_sub(x_3, x_4);
lean_dec(x_3);
x_3 = x_7;
goto _start;
}
else
{
lean_dec_ref(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(x_1, x_2, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(x_1, x_2, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; 
x_4 = lean_byte_array_fget(x_1, x_3);
x_5 = lean_byte_array_fget(x_1, x_2);
x_6 = lean_uint8_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_3, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_3, x_9);
lean_dec(x_3);
lean_inc(x_10);
lean_inc_ref(x_1);
x_11 = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(x_1, x_10, x_10);
lean_dec(x_10);
x_3 = x_11;
goto _start;
}
else
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_7;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_1);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
lean_dec(x_3);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_nat_sub(x_4, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
lean_object* initialize_Init_Data_String_Lemmas_Pattern_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Pattern_String(uint8_t builtin);
lean_object* initialize_Init_Data_String_Pattern_String(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_IsEmpty(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_OrderInstances(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Lemmas_Pattern_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Pattern_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Pattern_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
