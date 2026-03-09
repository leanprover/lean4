// Lean compiler output
// Module: Init.Data.Stream
// Imports: public import Init.Data.Range public import Init.Data.Array.Subarray import Init.Data.Slice.Array.Basic
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
LEAN_EXPORT lean_object* l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Stream_0__Std_Stream_forIn_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Stream_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Stream_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInOfMonadOfStream___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInOfMonadOfStream___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInOfMonadOfStream(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instToStreamList___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_instToStreamList___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_instToStreamList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instToStreamList___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instToStreamList___closed__0 = (const lean_object*)&l_Std_instToStreamList___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instToStreamList(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instToStreamArraySubarray___lam__0(lean_object*);
static const lean_closure_object l_Std_instToStreamArraySubarray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instToStreamArraySubarray___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instToStreamArraySubarray___closed__0 = (const lean_object*)&l_Std_instToStreamArraySubarray___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instToStreamArraySubarray(lean_object*);
LEAN_EXPORT lean_object* l_Std_instToStreamSubarray___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_instToStreamSubarray___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_instToStreamSubarray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instToStreamSubarray___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instToStreamSubarray___closed__0 = (const lean_object*)&l_Std_instToStreamSubarray___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instToStreamSubarray(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_instToStreamStringRaw___lam__0(lean_object*);
static const lean_closure_object l_Std_instToStreamStringRaw___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instToStreamStringRaw___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instToStreamStringRaw___closed__0 = (const lean_object*)&l_Std_instToStreamStringRaw___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instToStreamStringRaw = (const lean_object*)&l_Std_instToStreamStringRaw___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instToStreamRange___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_instToStreamRange___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_instToStreamRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instToStreamRange___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instToStreamRange___closed__0 = (const lean_object*)&l_Std_instToStreamRange___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instToStreamRange = (const lean_object*)&l_Std_instToStreamRange___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instStreamProd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instStreamProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instStreamProd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instStreamList___lam__0(lean_object*);
static const lean_closure_object l_Std_instStreamList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instStreamList___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instStreamList___closed__0 = (const lean_object*)&l_Std_instStreamList___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instStreamList(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instStreamSubarray___lam__0(lean_object*);
static const lean_closure_object l_Std_instStreamSubarray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instStreamSubarray___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instStreamSubarray___closed__0 = (const lean_object*)&l_Std_instStreamSubarray___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instStreamSubarray(lean_object*);
LEAN_EXPORT lean_object* l_Std_instStreamRangeNat___lam__0(lean_object*);
static const lean_closure_object l_Std_instStreamRangeNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instStreamRangeNat___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instStreamRangeNat___closed__0 = (const lean_object*)&l_Std_instStreamRangeNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instStreamRangeNat = (const lean_object*)&l_Std_instStreamRangeNat___closed__0_value;
LEAN_EXPORT lean_object* l_Stream_next_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Stream_next_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ToStream_toStream___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ToStream_toStream(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_inc_ref(x_1);
x_9 = lean_apply_1(x_1, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_10 = lean_apply_2(x_8, lean_box(0), x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_3);
x_14 = lean_alloc_closure((void*)(l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg___lam__0), 6, 5);
lean_closure_set(x_14, 0, x_8);
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_3);
lean_closure_set(x_14, 4, x_13);
x_15 = lean_apply_2(x_3, x_12, x_5);
x_16 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_15, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg(x_2, x_3, x_4, x_5, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Stream_0__Std_Stream_forIn_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg(x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Stream_forIn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg(x_1, x_2, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Stream_forIn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg(x_5, x_6, x_9, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_instForInOfMonadOfStream___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_instForInOfMonadOfStream___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_instForInOfMonadOfStream___redArg___lam__0), 6, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_instForInOfMonadOfStream(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Std_instForInOfMonadOfStream___redArg___lam__0), 6, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamList___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamList___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_instToStreamList___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Std_instToStreamList___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamArraySubarray___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_array_get_size(x_1);
x_4 = l_Array_toSubarray___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamArraySubarray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Std_instToStreamArraySubarray___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamSubarray___lam__0(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamSubarray___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_instToStreamSubarray___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamSubarray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Std_instToStreamSubarray___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamStringRaw___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamRange___lam__0(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamRange___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_instToStreamRange___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_instStreamProd___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_43; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_43 = !lean_is_exclusive(x_3);
if (x_43 == 0)
{
x_6 = x_3;
x_7 = x_43;
goto block_42;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_8; 
x_8 = lean_apply_1(x_1, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_del_object(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_41; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_ctor_get(x_10, 0);
x_12 = lean_ctor_get(x_10, 1);
x_41 = !lean_is_exclusive(x_10);
if (x_41 == 0)
{
x_13 = x_10;
x_14 = x_41;
goto block_40;
}
else
{
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_15; 
x_15 = lean_apply_1(x_2, x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_del_object(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_del_object(x_6);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_39; 
x_17 = lean_ctor_get(x_15, 0);
x_39 = !lean_is_exclusive(x_15);
if (x_39 == 0)
{
x_18 = x_15;
x_19 = x_39;
goto block_38;
}
else
{
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_37; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
x_37 = !lean_is_exclusive(x_17);
if (x_37 == 0)
{
x_22 = x_17;
x_23 = x_37;
goto block_36;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_24; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 0, x_11);
x_24 = x_22;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_11);
lean_ctor_set(x_35, 1, x_20);
x_24 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_25; 
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_21);
lean_ctor_set(x_13, 0, x_12);
x_25 = x_13;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_12);
lean_ctor_set(x_33, 1, x_21);
x_25 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_26; 
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_25);
lean_ctor_set(x_6, 0, x_24);
x_26 = x_6;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_25);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_26);
x_27 = x_18;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instStreamProd___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_instStreamProd___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_instStreamProd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Std_instStreamProd___redArg___lam__0), 3, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_instStreamList___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_12; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
x_5 = x_1;
x_6 = x_12;
goto block_11;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_7; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 0);
x_7 = x_5;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_4);
x_7 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instStreamList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Std_instStreamList___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_instStreamSubarray___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_18; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
x_5 = x_1;
x_6 = x_18;
goto block_17;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; 
lean_del_object(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_fget(x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_11);
x_12 = x_5;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_4);
x_12 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instStreamSubarray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Std_instStreamSubarray___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_instStreamRangeNat___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_16; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
x_5 = x_1;
x_6 = x_16;
goto block_15;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_16;
goto block_15;
}
block_15:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_del_object(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_nat_add(x_2, x_4);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_9);
x_10 = x_5;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_4);
x_10 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Stream_next_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Stream_next_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ToStream_toStream___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ToStream_toStream(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
lean_object* runtime_initialize_Init_Data_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Subarray(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Array_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Stream(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Range(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Subarray(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Array_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Stream(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Range(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Subarray(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Array_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Stream(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Range(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Subarray(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Array_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Stream(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Stream(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Stream(builtin);
}
#ifdef __cplusplus
}
#endif
