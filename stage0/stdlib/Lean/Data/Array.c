// Lean compiler output
// Module: Lean.Data.Array
// Imports: import Init.Data.Stream public import Init.Data.Range.Polymorphic.Nat public import Init.Data.Range.Polymorphic.Iterators
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
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__5(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__15(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__18(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_mask___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_mask___redArg___closed__0 = (const lean_object*)&l_Array_mask___redArg___closed__0_value;
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_mask___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mask___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mask(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mask___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Array_zipMasked___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mask___redArg___closed__0_value)}};
static const lean_object* l_Array_zipMasked___redArg___closed__0 = (const lean_object*)&l_Array_zipMasked___redArg___closed__0_value;
static const lean_ctor_object l_Array_zipMasked___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_zipMasked___redArg___closed__0_value)}};
static const lean_object* l_Array_zipMasked___redArg___closed__1 = (const lean_object*)&l_Array_zipMasked___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Array_zipMasked___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipMasked___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipMasked(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipMasked___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
x_10 = lean_apply_4(x_3, x_9, x_7, lean_box(0), lean_box(0));
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_filterPairsM___redArg___lam__3(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_lt(x_8, x_1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_apply_2(x_2, lean_box(0), x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_inc(x_8);
lean_inc(x_2);
x_14 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__3___boxed), 4, 3);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_8);
lean_closure_set(x_14, 2, x_11);
x_19 = lean_box(x_5);
x_20 = lean_array_get_borrowed(x_19, x_6, x_8);
x_21 = lean_unbox(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_array_fget_borrowed(x_7, x_8);
lean_dec(x_8);
lean_inc(x_22);
x_23 = lean_array_push(x_9, x_22);
lean_inc(x_2);
x_24 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__4), 3, 2);
lean_closure_set(x_24, 0, x_23);
lean_closure_set(x_24, 1, x_2);
x_25 = lean_box(0);
x_26 = lean_apply_2(x_2, lean_box(0), x_25);
lean_inc(x_3);
x_27 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_26, x_24);
x_15 = x_27;
goto block_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_8);
lean_inc(x_2);
x_28 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__5), 3, 2);
lean_closure_set(x_28, 0, x_9);
lean_closure_set(x_28, 1, x_2);
x_29 = lean_box(0);
x_30 = lean_apply_2(x_2, lean_box(0), x_29);
lean_inc(x_3);
x_31 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_30, x_28);
x_15 = x_31;
goto block_18;
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
lean_inc(x_3);
x_16 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_15, x_4);
x_17 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_16, x_14);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
x_13 = l_Array_filterPairsM___redArg___lam__6(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_box(x_5);
lean_inc(x_3);
x_12 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__6___boxed), 11, 7);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_11);
lean_closure_set(x_12, 5, x_10);
lean_closure_set(x_12, 6, x_6);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_mk_empty_array_with_capacity(x_9);
lean_dec(x_9);
x_15 = l_WellFounded_opaqueFix_u2083___redArg(x_12, x_13, x_14, lean_box(0));
x_16 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_15, x_7);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
x_10 = l_Array_filterPairsM___redArg___lam__7(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__8), 3, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
x_5 = lean_box(0);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
x_7 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
x_10 = lean_apply_4(x_3, x_9, x_7, lean_box(0), lean_box(0));
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_filterPairsM___redArg___lam__10(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = lean_nat_add(x_2, x_3);
x_10 = lean_apply_4(x_4, x_9, x_8, lean_box(0), lean_box(0));
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_filterPairsM___redArg___lam__11(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_apply_2(x_3, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_apply_2(x_3, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_apply_2(x_3, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__15(uint8_t x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (x_1 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_nat_add(x_7, x_2);
lean_dec(x_7);
x_11 = lean_box(x_4);
x_12 = lean_array_set(x_8, x_3, x_11);
lean_inc(x_5);
x_13 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__13), 4, 3);
lean_closure_set(x_13, 0, x_10);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_5);
x_14 = lean_box(0);
x_15 = lean_apply_2(x_5, lean_box(0), x_14);
x_16 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_15, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_5);
x_17 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__14), 4, 3);
lean_closure_set(x_17, 0, x_7);
lean_closure_set(x_17, 1, x_8);
lean_closure_set(x_17, 2, x_5);
x_18 = lean_box(0);
x_19 = lean_apply_2(x_5, lean_box(0), x_18);
x_20 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_19, x_17);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox(x_4);
x_12 = l_Array_filterPairsM___redArg___lam__15(x_10, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__18(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_box(x_3);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__15___boxed), 9, 6);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_12);
lean_closure_set(x_13, 4, x_4);
lean_closure_set(x_13, 5, x_5);
x_14 = lean_unbox(x_10);
lean_dec(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_nat_add(x_6, x_1);
lean_dec(x_1);
lean_dec(x_6);
x_16 = lean_box(x_3);
x_17 = lean_array_set(x_7, x_8, x_16);
x_18 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__16), 4, 3);
lean_closure_set(x_18, 0, x_13);
lean_closure_set(x_18, 1, x_15);
lean_closure_set(x_18, 2, x_17);
x_19 = lean_box(0);
x_20 = lean_apply_2(x_4, lean_box(0), x_19);
x_21 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_20, x_18);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_22 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__17), 4, 3);
lean_closure_set(x_22, 0, x_13);
lean_closure_set(x_22, 1, x_6);
lean_closure_set(x_22, 2, x_7);
x_23 = lean_box(0);
x_24 = lean_apply_2(x_4, lean_box(0), x_23);
x_25 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_24, x_22);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Array_filterPairsM___redArg___lam__18(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_10, x_1);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_apply_2(x_2, lean_box(0), x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec_ref(x_11);
lean_inc(x_3);
lean_inc(x_10);
lean_inc(x_2);
x_18 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__11___boxed), 5, 4);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_10);
lean_closure_set(x_18, 2, x_3);
lean_closure_set(x_18, 3, x_13);
lean_inc(x_2);
lean_inc(x_17);
lean_inc(x_16);
x_23 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__12), 4, 3);
lean_closure_set(x_23, 0, x_16);
lean_closure_set(x_23, 1, x_17);
lean_closure_set(x_23, 2, x_2);
x_24 = lean_box(x_14);
lean_inc(x_6);
lean_inc(x_17);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_10);
x_25 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__18___boxed), 9, 8);
lean_closure_set(x_25, 0, x_3);
lean_closure_set(x_25, 1, x_10);
lean_closure_set(x_25, 2, x_24);
lean_closure_set(x_25, 3, x_2);
lean_closure_set(x_25, 4, x_4);
lean_closure_set(x_25, 5, x_16);
lean_closure_set(x_25, 6, x_17);
lean_closure_set(x_25, 7, x_6);
x_35 = lean_box(x_9);
x_36 = lean_array_get_borrowed(x_35, x_17, x_6);
x_37 = lean_unbox(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_box(x_9);
x_39 = lean_array_get(x_38, x_17, x_10);
lean_dec(x_17);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
x_26 = x_40;
goto block_34;
}
else
{
uint8_t x_41; 
lean_inc(x_36);
lean_dec(x_17);
x_41 = lean_unbox(x_36);
lean_dec(x_36);
x_26 = x_41;
goto block_34;
}
block_22:
{
lean_object* x_20; lean_object* x_21; 
lean_inc(x_4);
x_20 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_19, x_5);
x_21 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_20, x_18);
return x_21;
}
block_34:
{
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_23);
lean_dec(x_2);
x_27 = lean_array_fget_borrowed(x_7, x_6);
lean_dec(x_6);
x_28 = lean_array_fget_borrowed(x_7, x_10);
lean_dec(x_10);
lean_inc(x_28);
lean_inc(x_27);
x_29 = lean_apply_2(x_8, x_27, x_28);
lean_inc(x_4);
x_30 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_29, x_25);
x_19 = x_30;
goto block_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec_ref(x_25);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
x_31 = lean_box(0);
x_32 = lean_apply_2(x_2, lean_box(0), x_31);
lean_inc(x_4);
x_33 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_32, x_23);
x_19 = x_33;
goto block_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_9);
x_15 = l_Array_filterPairsM___redArg___lam__19(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14, x_10, x_11, x_12, x_13);
lean_dec_ref(x_7);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_10, x_1);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = lean_apply_2(x_2, lean_box(0), x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_33; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
x_33 = !lean_is_exclusive(x_11);
if (x_33 == 0)
{
x_18 = x_11;
x_19 = x_33;
goto block_32;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_box(0);
x_19 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc(x_10);
lean_inc(x_2);
x_20 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__10___boxed), 4, 3);
lean_closure_set(x_20, 0, x_2);
lean_closure_set(x_20, 1, x_10);
lean_closure_set(x_20, 2, x_13);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_box(x_7);
lean_inc(x_10);
lean_inc(x_3);
x_23 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__19___boxed), 13, 9);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_2);
lean_closure_set(x_23, 2, x_21);
lean_closure_set(x_23, 3, x_3);
lean_closure_set(x_23, 4, x_4);
lean_closure_set(x_23, 5, x_10);
lean_closure_set(x_23, 6, x_5);
lean_closure_set(x_23, 7, x_6);
lean_closure_set(x_23, 8, x_22);
x_24 = lean_nat_add(x_10, x_21);
lean_dec(x_10);
if (x_19 == 0)
{
x_25 = x_18;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_16);
lean_ctor_set(x_31, 1, x_17);
x_25 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = l_WellFounded_opaqueFix_u2083___redArg(x_23, x_24, x_25, lean_box(0));
lean_inc(x_3);
x_27 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_26, x_8);
lean_inc(x_3);
x_28 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_27, x_9);
x_29 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_28, x_20);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_7);
x_15 = l_Array_filterPairsM___redArg___lam__20(x_1, x_2, x_3, x_4, x_5, x_6, x_14, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_28; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_28 = !lean_is_exclusive(x_1);
if (x_28 == 0)
{
x_6 = x_1;
x_7 = x_28;
goto block_27;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = 0;
x_10 = lean_array_get_size(x_2);
x_11 = lean_box(x_9);
x_12 = lean_mk_array(x_10, x_11);
lean_inc(x_8);
x_13 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__0), 2, 1);
lean_closure_set(x_13, 0, x_8);
lean_inc(x_8);
x_14 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__2), 2, 1);
lean_closure_set(x_14, 0, x_8);
lean_inc(x_8);
x_15 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__1), 2, 1);
lean_closure_set(x_15, 0, x_8);
x_16 = lean_box(x_9);
lean_inc_ref(x_2);
lean_inc(x_5);
lean_inc(x_8);
x_17 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__7___boxed), 8, 7);
lean_closure_set(x_17, 0, x_10);
lean_closure_set(x_17, 1, x_8);
lean_closure_set(x_17, 2, x_5);
lean_closure_set(x_17, 3, x_14);
lean_closure_set(x_17, 4, x_16);
lean_closure_set(x_17, 5, x_2);
lean_closure_set(x_17, 6, x_15);
lean_inc(x_5);
lean_inc(x_8);
x_18 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__9), 3, 2);
lean_closure_set(x_18, 0, x_8);
lean_closure_set(x_18, 1, x_5);
x_19 = lean_box(x_9);
lean_inc_ref(x_13);
lean_inc(x_5);
x_20 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__20___boxed), 13, 9);
lean_closure_set(x_20, 0, x_10);
lean_closure_set(x_20, 1, x_8);
lean_closure_set(x_20, 2, x_5);
lean_closure_set(x_20, 3, x_13);
lean_closure_set(x_20, 4, x_2);
lean_closure_set(x_20, 5, x_3);
lean_closure_set(x_20, 6, x_19);
lean_closure_set(x_20, 7, x_18);
lean_closure_set(x_20, 8, x_13);
x_21 = lean_unsigned_to_nat(0u);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_12);
lean_ctor_set(x_6, 0, x_21);
x_22 = x_6;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_12);
x_22 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_WellFounded_opaqueFix_u2083___redArg(x_20, x_21, x_22, lean_box(0));
x_24 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_23, x_17);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_filterPairsM___redArg(x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_45; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_45 = !lean_is_exclusive(x_4);
if (x_45 == 0)
{
x_13 = x_4;
x_14 = x_45;
goto block_44;
}
else
{
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_13 = lean_box(0);
x_14 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_nat_dec_lt(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
if (x_14 == 0)
{
x_19 = x_13;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_12);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
else
{
lean_object* x_22; uint8_t x_23; uint8_t x_40; 
lean_inc(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
x_40 = !lean_is_exclusive(x_11);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_11, 2);
lean_dec(x_41);
x_42 = lean_ctor_get(x_11, 1);
lean_dec(x_42);
x_43 = lean_ctor_get(x_11, 0);
lean_dec(x_43);
x_22 = x_11;
x_23 = x_40;
goto block_39;
}
else
{
lean_dec(x_11);
x_22 = lean_box(0);
x_23 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_array_uget_borrowed(x_1, x_3);
x_25 = lean_array_fget(x_15, x_16);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_16, x_26);
lean_dec(x_16);
if (x_23 == 0)
{
lean_ctor_set(x_22, 1, x_27);
x_28 = x_22;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_15);
lean_ctor_set(x_38, 1, x_27);
lean_ctor_set(x_38, 2, x_17);
x_28 = x_38;
goto block_37;
}
block_37:
{
uint8_t x_29; 
x_29 = lean_unbox(x_24);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_25);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_28);
x_30 = x_13;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_12);
x_30 = x_32;
goto block_31;
}
block_31:
{
x_5 = x_30;
goto block_9;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_array_push(x_12, x_25);
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_33);
lean_ctor_set(x_13, 0, x_28);
x_34 = x_13;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
x_5 = x_34;
goto block_9;
}
}
}
}
}
}
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_3, x_6);
x_3 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___redArg(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mask___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = ((lean_object*)(l_Array_mask___redArg___closed__0));
x_5 = lean_array_get_size(x_2);
x_6 = l_Array_toSubarray___redArg(x_2, x_3, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
x_8 = lean_array_size(x_1);
x_9 = 0;
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___redArg(x_1, x_8, x_9, x_7);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec_ref(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mask___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mask___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mask(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_mask___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_mask(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_62; 
x_13 = lean_ctor_get(x_6, 1);
x_14 = lean_ctor_get(x_6, 0);
x_62 = !lean_is_exclusive(x_6);
if (x_62 == 0)
{
x_15 = x_6;
x_16 = x_62;
goto block_61;
}
else
{
lean_inc(x_13);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_60; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
x_60 = !lean_is_exclusive(x_13);
if (x_60 == 0)
{
x_19 = x_13;
x_20 = x_60;
goto block_59;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_array_uget_borrowed(x_3, x_5);
x_22 = lean_unbox(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_array_get_size(x_1);
x_24 = lean_nat_dec_lt(x_14, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
if (x_20 == 0)
{
x_25 = x_19;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_30, 1, x_18);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 1, x_25);
x_26 = x_15;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
x_7 = x_26;
goto block_11;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_array_fget_borrowed(x_1, x_14);
lean_inc(x_31);
x_32 = lean_array_push(x_18, x_31);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_14, x_33);
lean_dec(x_14);
if (x_20 == 0)
{
lean_ctor_set(x_19, 1, x_32);
x_35 = x_19;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_17);
lean_ctor_set(x_40, 1, x_32);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 1, x_35);
lean_ctor_set(x_15, 0, x_34);
x_36 = x_15;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
x_7 = x_36;
goto block_11;
}
}
}
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_array_get_size(x_2);
x_42 = lean_nat_dec_lt(x_17, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
if (x_20 == 0)
{
x_43 = x_19;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_17);
lean_ctor_set(x_48, 1, x_18);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 1, x_43);
x_44 = x_15;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_14);
lean_ctor_set(x_46, 1, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
x_7 = x_44;
goto block_11;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_array_fget_borrowed(x_2, x_17);
lean_inc(x_49);
x_50 = lean_array_push(x_18, x_49);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_17, x_51);
lean_dec(x_17);
if (x_20 == 0)
{
lean_ctor_set(x_19, 1, x_50);
lean_ctor_set(x_19, 0, x_52);
x_53 = x_19;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_50);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 1, x_53);
x_54 = x_15;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_14);
lean_ctor_set(x_56, 1, x_53);
x_54 = x_56;
goto block_55;
}
block_55:
{
x_7 = x_54;
goto block_11;
}
}
}
}
}
}
}
block_11:
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_5, x_8);
x_5 = x_9;
x_6 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___redArg(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_zipMasked___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = ((lean_object*)(l_Array_zipMasked___redArg___closed__1));
x_5 = lean_array_size(x_1);
x_6 = 0;
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___redArg(x_2, x_3, x_1, x_5, x_6, x_4);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_zipMasked___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_zipMasked___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_zipMasked(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_zipMasked___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_zipMasked___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_zipMasked(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
lean_object* runtime_initialize_Init_Data_Stream(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Array(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Stream(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Array(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Stream(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Array(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Stream(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Nat(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Array(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Array(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Array(builtin);
}
#ifdef __cplusplus
}
#endif
