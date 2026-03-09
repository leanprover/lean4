// Lean compiler output
// Module: Init.Data.Slice.List.Iterator
// Imports: public import Init.Data.Slice.List.Basic public import Init.Data.Iterators.Producers.List public import Init.Data.Iterators.Combinators.Take import all Init.Data.Range.Polymorphic.Basic public import Init.Data.Slice.Operations
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
LEAN_EXPORT lean_object* l_ListSlice_instToIterator___lam__0(lean_object*);
static const lean_closure_object l_ListSlice_instToIterator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ListSlice_instToIterator___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ListSlice_instToIterator___closed__0 = (const lean_object*)&l_ListSlice_instToIterator___closed__0_value;
LEAN_EXPORT lean_object* l_ListSlice_instToIterator(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_instSliceSizeListSliceData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceSizeListSliceData___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceSizeListSliceData___closed__0 = (const lean_object*)&l_instSliceSizeListSliceData___closed__0_value;
static const lean_closure_object l_instSliceSizeListSliceData___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceSizeListSliceData___lam__1, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_instSliceSizeListSliceData___closed__0_value)} };
static const lean_object* l_instSliceSizeListSliceData___closed__1 = (const lean_object*)&l_instSliceSizeListSliceData___closed__1_value;
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData(lean_object*);
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instAppendListSlice___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_List_instAppendListSlice___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_instAppendListSlice___lam__2___closed__0 = (const lean_object*)&l_List_instAppendListSlice___lam__2___closed__0_value;
lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_List_toSlice___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instAppendListSlice___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_instAppendListSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_instAppendListSlice___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_instAppendListSlice___closed__0 = (const lean_object*)&l_List_instAppendListSlice___closed__0_value;
static lean_once_cell_t l_List_instAppendListSlice___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_instAppendListSlice___closed__1;
LEAN_EXPORT lean_object* l_List_instAppendListSlice(lean_object*);
static const lean_string_object l_List_ListSlice_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = ".toSlice 0 "};
static const lean_object* l_List_ListSlice_repr___redArg___closed__0 = (const lean_object*)&l_List_ListSlice_repr___redArg___closed__0_value;
static const lean_ctor_object l_List_ListSlice_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_ListSlice_repr___redArg___closed__0_value)}};
static const lean_object* l_List_ListSlice_repr___redArg___closed__1 = (const lean_object*)&l_List_ListSlice_repr___redArg___closed__1_value;
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_List_ListSlice_repr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_ListSlice_repr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_instReprListSlice(lean_object*, lean_object*);
static const lean_string_object l_List_instToStringListSlice___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_List_instToStringListSlice___redArg___lam__1___closed__0 = (const lean_object*)&l_List_instToStringListSlice___redArg___lam__1___closed__0_value;
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instToStringListSlice___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instToStringListSlice___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_instToStringListSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ListSlice_instToIterator___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_1, 1);
lean_dec(x_12);
x_4 = x_1;
x_5 = x_11;
goto block_10;
}
else
{
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
if (x_5 == 0)
{
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 0, x_6);
x_7 = x_4;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_3);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_23; 
lean_inc_ref(x_2);
x_13 = lean_ctor_get(x_1, 0);
x_23 = !lean_is_exclusive(x_1);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_1, 1);
lean_dec(x_24);
x_14 = x_1;
x_15 = x_23;
goto block_22;
}
else
{
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec_ref(x_2);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_16, x_17);
lean_dec(x_16);
if (x_15 == 0)
{
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 0, x_18);
x_19 = x_14;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_13);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ListSlice_instToIterator(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_ListSlice_instToIterator___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_19; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
x_7 = x_1;
x_8 = x_19;
goto block_18;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_dec_eq(x_5, x_9);
if (x_10 == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_del_object(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec_ref(x_6);
x_12 = lean_nat_sub(x_5, x_9);
lean_dec(x_5);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_11);
lean_ctor_set(x_7, 0, x_12);
x_13 = x_7;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_11);
x_13 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_nat_add(x_2, x_9);
x_15 = lean_apply_4(x_4, x_13, x_14, lean_box(0), lean_box(0));
return x_15;
}
}
}
else
{
lean_del_object(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_inc(x_2);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_instSliceSizeListSliceData___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_16; 
x_8 = lean_ctor_get(x_2, 0);
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_2, 1);
lean_dec(x_17);
x_9 = x_2;
x_10 = x_16;
goto block_15;
}
else
{
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
if (x_10 == 0)
{
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 0, x_11);
x_12 = x_9;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_8);
x_12 = x_14;
goto block_13;
}
block_13:
{
x_3 = x_12;
goto block_6;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_28; 
lean_inc_ref(x_7);
x_18 = lean_ctor_get(x_2, 0);
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_2, 1);
lean_dec(x_29);
x_19 = x_2;
x_20 = x_28;
goto block_27;
}
else
{
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_7, 0);
lean_inc(x_21);
lean_dec_ref(x_7);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_21, x_22);
lean_dec(x_21);
if (x_20 == 0)
{
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 0, x_23);
x_24 = x_19;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_18);
x_24 = x_26;
goto block_25;
}
block_25:
{
x_3 = x_24;
goto block_6;
}
}
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_WellFounded_opaqueFix_u2083___redArg(x_1, x_3, x_4, lean_box(0));
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_instSliceSizeListSliceData___closed__1));
return x_2;
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_apply_4(x_2, x_3, x_7, lean_box(0), lean_box(0));
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_28; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
x_28 = !lean_is_exclusive(x_5);
if (x_28 == 0)
{
x_11 = x_5;
x_12 = x_28;
goto block_27;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_dec_eq(x_9, x_13);
if (x_14 == 0)
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_15; 
lean_del_object(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_apply_2(x_1, lean_box(0), x_6);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec_ref(x_10);
x_18 = lean_nat_sub(x_9, x_13);
lean_dec(x_9);
if (x_12 == 0)
{
lean_ctor_set(x_11, 1, x_17);
lean_ctor_set(x_11, 0, x_18);
x_19 = x_11;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_17);
x_19 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__1), 4, 3);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_8);
lean_closure_set(x_20, 2, x_19);
x_21 = lean_apply_2(x_2, x_16, x_6);
lean_inc(x_3);
x_22 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_21, x_4);
x_23 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_22, x_20);
return x_23;
}
}
}
else
{
lean_object* x_26; 
lean_del_object(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_apply_2(x_1, lean_box(0), x_6);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_14; 
x_14 = lean_ctor_get(x_3, 1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_23; 
x_15 = lean_ctor_get(x_3, 0);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_3, 1);
lean_dec(x_24);
x_16 = x_3;
x_17 = x_23;
goto block_22;
}
else
{
lean_inc(x_15);
lean_dec(x_3);
x_16 = lean_box(0);
x_17 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_unsigned_to_nat(0u);
if (x_17 == 0)
{
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 0, x_18);
x_19 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_15);
x_19 = x_21;
goto block_20;
}
block_20:
{
x_6 = x_19;
goto block_13;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_35; 
lean_inc_ref(x_14);
x_25 = lean_ctor_get(x_3, 0);
x_35 = !lean_is_exclusive(x_3);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_3, 1);
lean_dec(x_36);
x_26 = x_3;
x_27 = x_35;
goto block_34;
}
else
{
lean_inc(x_25);
lean_dec(x_3);
x_26 = lean_box(0);
x_27 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec_ref(x_14);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_28, x_29);
lean_dec(x_28);
if (x_27 == 0)
{
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 0, x_30);
x_31 = x_26;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_25);
x_31 = x_33;
goto block_32;
}
block_32:
{
x_6 = x_31;
goto block_13;
}
}
}
block_13:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__2), 8, 4);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_5);
lean_closure_set(x_11, 2, x_8);
lean_closure_set(x_11, 3, x_10);
x_12 = l_WellFounded_opaqueFix_u2083___redArg(x_11, x_6, x_4, lean_box(0));
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_instAppendListSlice___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_19; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
x_6 = x_1;
x_7 = x_19;
goto block_18;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_dec_eq(x_4, x_8);
if (x_9 == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_del_object(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec_ref(x_5);
x_12 = lean_nat_sub(x_4, x_8);
lean_dec(x_4);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_11);
lean_ctor_set(x_6, 0, x_12);
x_13 = x_6;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_11);
x_13 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_push(x_2, x_10);
x_15 = lean_apply_3(x_3, x_13, x_14, lean_box(0));
return x_15;
}
}
}
else
{
lean_del_object(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_List_instAppendListSlice___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_15; lean_object* x_36; 
x_36 = lean_ctor_get(x_3, 1);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_45; 
x_37 = lean_ctor_get(x_3, 0);
x_45 = !lean_is_exclusive(x_3);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_3, 1);
lean_dec(x_46);
x_38 = x_3;
x_39 = x_45;
goto block_44;
}
else
{
lean_inc(x_37);
lean_dec(x_3);
x_38 = lean_box(0);
x_39 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_unsigned_to_nat(0u);
if (x_39 == 0)
{
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 0, x_40);
x_41 = x_38;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_37);
x_41 = x_43;
goto block_42;
}
block_42:
{
x_15 = x_41;
goto block_35;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_57; 
lean_inc_ref(x_36);
x_47 = lean_ctor_get(x_3, 0);
x_57 = !lean_is_exclusive(x_3);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_3, 1);
lean_dec(x_58);
x_48 = x_3;
x_49 = x_57;
goto block_56;
}
else
{
lean_inc(x_47);
lean_dec(x_3);
x_48 = lean_box(0);
x_49 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_36, 0);
lean_inc(x_50);
lean_dec_ref(x_36);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_50, x_51);
lean_dec(x_50);
if (x_49 == 0)
{
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 0, x_52);
x_53 = x_48;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_47);
x_53 = x_55;
goto block_54;
}
block_54:
{
x_15 = x_53;
goto block_35;
}
}
}
block_14:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_1, x_8, x_7);
x_10 = lean_array_to_list(x_9);
x_11 = l_List_appendTR___redArg(x_6, x_10);
x_12 = l_List_lengthTR___redArg(x_11);
x_13 = l_List_toSlice___redArg(x_11, x_5, x_12);
lean_dec(x_12);
lean_dec(x_11);
return x_13;
}
block_35:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_34; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
x_34 = !lean_is_exclusive(x_4);
if (x_34 == 0)
{
x_18 = x_4;
x_19 = x_34;
goto block_33;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = lean_box(0);
x_19 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = ((lean_object*)(l_List_instAppendListSlice___lam__2___closed__0));
x_22 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_2, x_15, x_21);
x_23 = lean_array_to_list(x_22);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_24; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 0, x_20);
x_24 = x_18;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_16);
x_24 = x_26;
goto block_25;
}
block_25:
{
x_5 = x_20;
x_6 = x_23;
x_7 = x_21;
x_8 = x_24;
goto block_14;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
lean_dec_ref(x_17);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_27, x_28);
lean_dec(x_27);
if (x_19 == 0)
{
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 0, x_29);
x_30 = x_18;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_16);
x_30 = x_32;
goto block_31;
}
block_31:
{
x_5 = x_20;
x_6 = x_23;
x_7 = x_21;
x_8 = x_30;
goto block_14;
}
}
}
}
}
}
static lean_object* _init_l_List_instAppendListSlice___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_instAppendListSlice___closed__0));
x_2 = lean_alloc_closure((void*)(l_List_instAppendListSlice___lam__2), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_instAppendListSlice(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_obj_once(&l_List_instAppendListSlice___closed__1, &l_List_instAppendListSlice___closed__1_once, _init_l_List_instAppendListSlice___closed__1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_ListSlice_repr___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_29; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_29 = !lean_is_exclusive(x_2);
if (x_29 == 0)
{
x_5 = x_2;
x_6 = x_29;
goto block_28;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_7; lean_object* x_8; 
x_7 = ((lean_object*)(l_List_instAppendListSlice___closed__0));
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_3);
x_8 = x_23;
goto block_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
lean_dec_ref(x_4);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_24, x_25);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_3);
x_8 = x_27;
goto block_21;
}
block_21:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = ((lean_object*)(l_List_instAppendListSlice___lam__2___closed__0));
x_10 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_7, x_8, x_9);
x_11 = lean_array_to_list(x_10);
lean_inc(x_11);
x_12 = l_List_repr___redArg(x_1, x_11);
x_13 = ((lean_object*)(l_List_ListSlice_repr___redArg___closed__1));
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 5);
lean_ctor_set(x_5, 1, x_13);
lean_ctor_set(x_5, 0, x_12);
x_14 = x_5;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_13);
x_14 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_List_lengthTR___redArg(x_11);
lean_dec(x_11);
x_16 = l_Nat_reprFast(x_15);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_ListSlice_repr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_ListSlice_repr___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_ListSlice_repr___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_instReprListSlice___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_instReprListSlice___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_instReprListSlice(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_instReprListSlice___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_instToStringListSlice___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_12; 
x_12 = lean_ctor_get(x_3, 1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_21; 
x_13 = lean_ctor_get(x_3, 0);
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_3, 1);
lean_dec(x_22);
x_14 = x_3;
x_15 = x_21;
goto block_20;
}
else
{
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(0u);
if (x_15 == 0)
{
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 0, x_16);
x_17 = x_14;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_13);
x_17 = x_19;
goto block_18;
}
block_18:
{
x_4 = x_17;
goto block_11;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_33; 
lean_inc_ref(x_12);
x_23 = lean_ctor_get(x_3, 0);
x_33 = !lean_is_exclusive(x_3);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_3, 1);
lean_dec(x_34);
x_24 = x_3;
x_25 = x_33;
goto block_32;
}
else
{
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_box(0);
x_25 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_12, 0);
lean_inc(x_26);
lean_dec_ref(x_12);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_26, x_27);
lean_dec(x_26);
if (x_25 == 0)
{
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 0, x_28);
x_29 = x_24;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_23);
x_29 = x_31;
goto block_30;
}
block_30:
{
x_4 = x_29;
goto block_11;
}
}
}
block_11:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = ((lean_object*)(l_List_instAppendListSlice___lam__2___closed__0));
x_6 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_1, x_4, x_5);
x_7 = ((lean_object*)(l_List_instToStringListSlice___redArg___lam__1___closed__0));
x_8 = lean_array_to_list(x_6);
x_9 = l_List_toString___redArg(x_2, x_8);
x_10 = lean_string_append(x_7, x_9);
lean_dec_ref(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_List_instToStringListSlice___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_List_instAppendListSlice___closed__0));
x_3 = lean_alloc_closure((void*)(l_List_instToStringListSlice___redArg___lam__1), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_instToStringListSlice(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_instToStringListSlice___redArg(x_2);
return x_3;
}
}
lean_object* runtime_initialize_Init_Data_Slice_List_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Producers_List(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Take(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Operations(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Slice_List_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Slice_List_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Producers_List(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Combinators_Take(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Operations(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Slice_List_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Slice_List_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Producers_List(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Combinators_Take(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Operations(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Slice_List_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Slice_List_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Producers_List(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Combinators_Take(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Operations(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_List_Iterator(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Slice_List_Iterator(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Slice_List_Iterator(builtin);
}
#ifdef __cplusplus
}
#endif
