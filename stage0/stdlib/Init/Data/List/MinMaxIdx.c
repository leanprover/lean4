// Lean compiler output
// Module: Init.Data.List.MinMaxIdx
// Imports: public import Init.Data.List.MinMaxOn import Init.Data.List.MinMaxOn public import Init.Data.List.Pairwise public import Init.Data.Subtype.Order import Init.Data.Order.Lemmas import Init.Data.List.Nat.TakeDrop import Init.Data.Order.Opposite import Init.Data.Nat.Order
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
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_minIdxOn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_minIdxOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_minIdxOn_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_minIdxOn_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_maxIdxOn___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_maxIdxOn___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_maxIdxOn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_maxIdxOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_maxIdxOn_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_maxIdxOn_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_get___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
lean_inc(x_2);
lean_inc(x_3);
x_9 = lean_apply_1(x_2, x_3);
lean_inc(x_2);
lean_inc(x_7);
x_10 = lean_apply_1(x_2, x_7);
lean_inc_ref(x_1);
x_11 = lean_apply_2(x_1, x_9, x_10);
x_12 = lean_unbox(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
x_3 = x_7;
x_4 = x_5;
x_5 = x_14;
x_6 = x_8;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_5, x_16);
lean_dec(x_5);
x_5 = x_17;
x_6 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_minIdxOn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_unsigned_to_nat(1u);
x_8 = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(x_1, x_2, x_4, x_6, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_minIdxOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(x_4, x_5, x_8, x_10, x_11, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_minIdxOn_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(x_1, x_2, x_5, x_7, x_8, x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_List_minIdxOn_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec_ref(x_4);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(x_4, x_5, x_8, x_10, x_11, x_9);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_List_maxIdxOn___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_2(x_1, x_3, x_2);
x_5 = lean_unbox(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_maxIdxOn___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_maxIdxOn___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_maxIdxOn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_closure((void*)(l_List_maxIdxOn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(x_6, x_2, x_4, x_7, x_8, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_maxIdxOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_closure((void*)(l_List_maxIdxOn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_10, 0, x_4);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_unsigned_to_nat(1u);
x_13 = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(x_10, x_5, x_8, x_11, x_12, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_maxIdxOn_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = lean_alloc_closure((void*)(l_List_maxIdxOn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_unsigned_to_nat(1u);
x_10 = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(x_7, x_2, x_5, x_8, x_9, x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_List_maxIdxOn_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec_ref(x_4);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = lean_alloc_closure((void*)(l_List_maxIdxOn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_10, 0, x_4);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_unsigned_to_nat(1u);
x_13 = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(x_10, x_5, x_8, x_11, x_12, x_9);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_inc(x_5);
x_7 = l_List_get___redArg(x_3, x_5);
lean_inc(x_2);
x_8 = lean_apply_1(x_2, x_7);
lean_inc(x_6);
x_9 = l_List_get___redArg(x_4, x_6);
x_10 = lean_apply_1(x_2, x_9);
x_11 = lean_apply_2(x_1, x_8, x_10);
x_12 = lean_unbox(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_13 = l_List_lengthTR___redArg(x_3);
x_14 = lean_nat_add(x_13, x_6);
lean_dec(x_6);
lean_dec(x_13);
return x_14;
}
else
{
lean_dec(x_6);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___redArg(x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_6);
return x_12;
}
}
lean_object* initialize_Init_Data_List_MinMaxOn(uint8_t builtin);
lean_object* initialize_Init_Data_List_MinMaxOn(uint8_t builtin);
lean_object* initialize_Init_Data_List_Pairwise(uint8_t builtin);
lean_object* initialize_Init_Data_Subtype_Order(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Opposite(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Order(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_MinMaxIdx(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_MinMaxOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_MinMaxOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Pairwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Subtype_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Opposite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
