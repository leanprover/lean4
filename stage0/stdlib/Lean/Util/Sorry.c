// Lean compiler output
// Module: Lean.Util.Sorry
// Imports: Init Lean.Message Lean.Exception
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
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Expr_hasSyntheticSorry_match__1(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Lean_Expr_isSyntheticSorry(lean_object*);
lean_object* l_Lean_MessageData_hasSorry_match__1(lean_object*);
lean_object* l_Lean_MessageData_hasSyntheticSorry___boxed(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hasSyntheticSorry_visit_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_MessageData_instantiateMVars(lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
extern lean_object* l_instReprBool___closed__2;
extern lean_object* l_Lean_instQuoteBool___closed__1;
uint8_t l_Lean_MessageData_hasSyntheticSorry_visit(lean_object*);
lean_object* l_Lean_Expr_hasSyntheticSorry___boxed(lean_object*);
lean_object* l_Lean_Expr_isSyntheticSorry___boxed(lean_object*);
uint8_t l_Lean_Exception_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Expr_isSyntheticSorry_match__1(lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSyntheticSorry_visit___spec__1(lean_object*, size_t, size_t);
lean_object* l_Lean_Expr_isSyntheticSorry_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_hasSyntheticSorry_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hasSyntheticSorry_visit___boxed(lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_MessageData_hasSorry___boxed(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_MessageData_hasSorry_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isSorry___boxed(lean_object*);
lean_object* l_Lean_Expr_isSorry_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_hasSorry_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hasSyntheticSorry_visit_match__1(lean_object*);
lean_object* l_Lean_Expr_isSorry_match__1(lean_object*);
lean_object* l_Lean_Expr_isSorry_match__1___rarg___closed__1;
lean_object* l_Lean_Exception_hasSyntheticSorry___boxed(lean_object*);
lean_object* l_Lean_Expr_hasSorry___closed__1;
uint8_t l_Lean_Expr_hasSorry(lean_object*);
lean_object* l_Lean_Expr_hasSorry___boxed(lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSorry___spec__1(lean_object*, size_t, size_t);
lean_object* l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSorry___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_hasSyntheticSorry_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSyntheticSorry_visit___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_hasSorry_match__1(lean_object*);
uint8_t l_Lean_MessageData_hasSorry(lean_object*);
lean_object* l_Lean_Exception_hasSyntheticSorry_match__1(lean_object*);
uint8_t l_Lean_Expr_isSorry(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
#define _init_l_Lean_Expr_isSorry_match__1___rarg___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("sorryAx");\
__INIT_VAR__ = x_1; goto l_Lean_Expr_isSorry_match__1___rarg___closed__1_end;\
}\
l_Lean_Expr_isSorry_match__1___rarg___closed__1_end: ((void) 0);}
lean_object* l_Lean_Expr_isSorry_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 5)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint64_t x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; uint64_t x_13; lean_object* x_14; uint64_t x_15; lean_object* x_16; uint8_t x_17; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
lean_dec(x_4);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
x_13 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_dec(x_5);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
x_15 = lean_ctor_get_uint64(x_6, sizeof(void*)*2);
lean_dec(x_6);
x_16 = l_Lean_Expr_isSorry_match__1___rarg___closed__1;
x_17 = lean_string_dec_eq(x_14, x_16);
lean_dec(x_14);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_18 = lean_apply_1(x_3, x_1);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_3);
lean_dec(x_1);
x_19 = lean_box_uint64(x_13);
x_20 = lean_box_uint64(x_11);
x_21 = lean_box_uint64(x_9);
x_22 = lean_box_uint64(x_15);
x_23 = lean_apply_7(x_2, x_12, x_19, x_10, x_20, x_8, x_21, x_22);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_24 = lean_apply_1(x_3, x_1);
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_25 = lean_apply_1(x_3, x_1);
return x_25;
}
}
else
{
lean_object* x_26; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_26 = lean_apply_1(x_3, x_1);
return x_26;
}
}
else
{
lean_object* x_27; 
lean_dec(x_4);
lean_dec(x_2);
x_27 = lean_apply_1(x_3, x_1);
return x_27;
}
}
else
{
lean_object* x_28; 
lean_dec(x_2);
x_28 = lean_apply_1(x_3, x_1);
return x_28;
}
}
}
lean_object* l_Lean_Expr_isSorry_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_isSorry_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Expr_isSorry(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = l_Lean_Expr_isSorry_match__1___rarg___closed__1;
x_8 = lean_string_dec_eq(x_6, x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
lean_object* l_Lean_Expr_isSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isSorry(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_isSyntheticSorry_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 5)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
uint64_t x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_13 = lean_ctor_get(x_4, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; uint64_t x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
x_17 = lean_ctor_get(x_5, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
lean_object* x_19; uint64_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get_uint64(x_6, sizeof(void*)*2);
x_21 = lean_ctor_get(x_6, 0);
lean_dec(x_21);
x_22 = l_Lean_Expr_isSorry_match__1___rarg___closed__1;
x_23 = lean_string_dec_eq(x_19, x_22);
lean_dec(x_19);
if (x_23 == 0)
{
lean_object* x_24; 
lean_free_object(x_6);
lean_free_object(x_5);
lean_dec(x_15);
lean_free_object(x_4);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_2);
x_24 = lean_apply_1(x_3, x_1);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_1);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_1, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_1, 0);
lean_dec(x_27);
if (lean_obj_tag(x_8) == 4)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_8, 0);
lean_inc(x_28);
switch (lean_obj_tag(x_28)) {
case 0:
{
lean_object* x_29; 
lean_dec(x_2);
lean_ctor_set(x_6, 1, x_22);
lean_ctor_set(x_6, 0, x_28);
x_29 = lean_apply_1(x_3, x_1);
return x_29;
}
case 1:
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
switch (lean_obj_tag(x_30)) {
case 0:
{
uint8_t x_31; 
lean_free_object(x_6);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_dec(x_32);
x_33 = lean_ctor_get(x_28, 0);
lean_dec(x_33);
lean_ctor_set(x_28, 1, x_22);
lean_ctor_set_uint64(x_28, sizeof(void*)*2, x_20);
lean_ctor_set(x_5, 0, x_28);
x_34 = lean_apply_1(x_3, x_1);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_28);
x_35 = lean_alloc_ctor(1, 2, 8);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_22);
lean_ctor_set_uint64(x_35, sizeof(void*)*2, x_20);
lean_ctor_set(x_5, 0, x_35);
x_36 = lean_apply_1(x_3, x_1);
return x_36;
}
}
case 1:
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
switch (lean_obj_tag(x_37)) {
case 0:
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_8, 1);
lean_inc(x_38);
x_39 = !lean_is_exclusive(x_28);
if (x_39 == 0)
{
uint64_t x_40; lean_object* x_41; uint64_t x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get_uint64(x_8, sizeof(void*)*2);
x_41 = lean_ctor_get(x_28, 1);
x_42 = lean_ctor_get_uint64(x_28, sizeof(void*)*2);
x_43 = lean_ctor_get(x_28, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_30);
if (x_44 == 0)
{
lean_object* x_45; uint64_t x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_30, 1);
x_46 = lean_ctor_get_uint64(x_30, sizeof(void*)*2);
x_47 = lean_ctor_get(x_30, 0);
lean_dec(x_47);
x_48 = l_Lean_instQuoteBool___closed__1;
x_49 = lean_string_dec_eq(x_45, x_48);
lean_dec(x_45);
if (x_49 == 0)
{
lean_object* x_50; 
lean_free_object(x_28);
lean_dec(x_41);
lean_dec(x_38);
lean_free_object(x_6);
lean_dec(x_2);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set_uint64(x_30, sizeof(void*)*2, x_20);
lean_ctor_set(x_5, 0, x_30);
x_50 = lean_apply_1(x_3, x_1);
return x_50;
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_8);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_8, 1);
lean_dec(x_52);
x_53 = lean_ctor_get(x_8, 0);
lean_dec(x_53);
x_54 = l_instReprBool___closed__2;
x_55 = lean_string_dec_eq(x_41, x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_2);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set_uint64(x_30, sizeof(void*)*2, x_20);
lean_ctor_set(x_8, 1, x_15);
lean_ctor_set(x_8, 0, x_30);
lean_ctor_set_uint64(x_8, sizeof(void*)*2, x_16);
lean_ctor_set_tag(x_5, 5);
lean_ctor_set(x_5, 1, x_11);
lean_ctor_set(x_5, 0, x_8);
lean_ctor_set_uint64(x_5, sizeof(void*)*2, x_12);
lean_ctor_set(x_28, 1, x_48);
lean_ctor_set(x_28, 0, x_37);
lean_ctor_set_uint64(x_28, sizeof(void*)*2, x_46);
lean_ctor_set(x_6, 1, x_41);
lean_ctor_set(x_6, 0, x_28);
lean_ctor_set_uint64(x_6, sizeof(void*)*2, x_42);
lean_ctor_set_tag(x_4, 4);
lean_ctor_set(x_4, 1, x_38);
lean_ctor_set(x_4, 0, x_6);
lean_ctor_set_uint64(x_4, sizeof(void*)*2, x_40);
lean_ctor_set(x_1, 1, x_4);
lean_ctor_set(x_1, 0, x_5);
x_56 = lean_apply_1(x_3, x_1);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_free_object(x_8);
lean_free_object(x_30);
lean_free_object(x_28);
lean_dec(x_41);
lean_free_object(x_1);
lean_free_object(x_6);
lean_free_object(x_5);
lean_free_object(x_4);
lean_dec(x_3);
x_57 = lean_box_uint64(x_16);
x_58 = lean_box_uint64(x_12);
x_59 = lean_box_uint64(x_40);
x_60 = lean_box_uint64(x_10);
x_61 = lean_box_uint64(x_20);
x_62 = lean_box_uint64(x_46);
x_63 = lean_box_uint64(x_42);
x_64 = lean_apply_10(x_2, x_15, x_57, x_11, x_58, x_38, x_59, x_60, x_61, x_62, x_63);
return x_64;
}
}
else
{
lean_object* x_65; uint8_t x_66; 
lean_dec(x_8);
x_65 = l_instReprBool___closed__2;
x_66 = lean_string_dec_eq(x_41, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_2);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set_uint64(x_30, sizeof(void*)*2, x_20);
x_67 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_67, 0, x_30);
lean_ctor_set(x_67, 1, x_15);
lean_ctor_set_uint64(x_67, sizeof(void*)*2, x_16);
lean_ctor_set_tag(x_5, 5);
lean_ctor_set(x_5, 1, x_11);
lean_ctor_set(x_5, 0, x_67);
lean_ctor_set_uint64(x_5, sizeof(void*)*2, x_12);
lean_ctor_set(x_28, 1, x_48);
lean_ctor_set(x_28, 0, x_37);
lean_ctor_set_uint64(x_28, sizeof(void*)*2, x_46);
lean_ctor_set(x_6, 1, x_41);
lean_ctor_set(x_6, 0, x_28);
lean_ctor_set_uint64(x_6, sizeof(void*)*2, x_42);
lean_ctor_set_tag(x_4, 4);
lean_ctor_set(x_4, 1, x_38);
lean_ctor_set(x_4, 0, x_6);
lean_ctor_set_uint64(x_4, sizeof(void*)*2, x_40);
lean_ctor_set(x_1, 1, x_4);
lean_ctor_set(x_1, 0, x_5);
x_68 = lean_apply_1(x_3, x_1);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_free_object(x_30);
lean_free_object(x_28);
lean_dec(x_41);
lean_free_object(x_1);
lean_free_object(x_6);
lean_free_object(x_5);
lean_free_object(x_4);
lean_dec(x_3);
x_69 = lean_box_uint64(x_16);
x_70 = lean_box_uint64(x_12);
x_71 = lean_box_uint64(x_40);
x_72 = lean_box_uint64(x_10);
x_73 = lean_box_uint64(x_20);
x_74 = lean_box_uint64(x_46);
x_75 = lean_box_uint64(x_42);
x_76 = lean_apply_10(x_2, x_15, x_69, x_11, x_70, x_38, x_71, x_72, x_73, x_74, x_75);
return x_76;
}
}
}
}
else
{
lean_object* x_77; uint64_t x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_30, 1);
x_78 = lean_ctor_get_uint64(x_30, sizeof(void*)*2);
lean_inc(x_77);
lean_dec(x_30);
x_79 = l_Lean_instQuoteBool___closed__1;
x_80 = lean_string_dec_eq(x_77, x_79);
lean_dec(x_77);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_free_object(x_28);
lean_dec(x_41);
lean_dec(x_38);
lean_free_object(x_6);
lean_dec(x_2);
x_81 = lean_alloc_ctor(1, 2, 8);
lean_ctor_set(x_81, 0, x_37);
lean_ctor_set(x_81, 1, x_22);
lean_ctor_set_uint64(x_81, sizeof(void*)*2, x_20);
lean_ctor_set(x_5, 0, x_81);
x_82 = lean_apply_1(x_3, x_1);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_83 = x_8;
} else {
 lean_dec_ref(x_8);
 x_83 = lean_box(0);
}
x_84 = l_instReprBool___closed__2;
x_85 = lean_string_dec_eq(x_41, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_2);
x_86 = lean_alloc_ctor(1, 2, 8);
lean_ctor_set(x_86, 0, x_37);
lean_ctor_set(x_86, 1, x_22);
lean_ctor_set_uint64(x_86, sizeof(void*)*2, x_20);
if (lean_is_scalar(x_83)) {
 x_87 = lean_alloc_ctor(4, 2, 8);
} else {
 x_87 = x_83;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_15);
lean_ctor_set_uint64(x_87, sizeof(void*)*2, x_16);
lean_ctor_set_tag(x_5, 5);
lean_ctor_set(x_5, 1, x_11);
lean_ctor_set(x_5, 0, x_87);
lean_ctor_set_uint64(x_5, sizeof(void*)*2, x_12);
lean_ctor_set(x_28, 1, x_79);
lean_ctor_set(x_28, 0, x_37);
lean_ctor_set_uint64(x_28, sizeof(void*)*2, x_78);
lean_ctor_set(x_6, 1, x_41);
lean_ctor_set(x_6, 0, x_28);
lean_ctor_set_uint64(x_6, sizeof(void*)*2, x_42);
lean_ctor_set_tag(x_4, 4);
lean_ctor_set(x_4, 1, x_38);
lean_ctor_set(x_4, 0, x_6);
lean_ctor_set_uint64(x_4, sizeof(void*)*2, x_40);
lean_ctor_set(x_1, 1, x_4);
lean_ctor_set(x_1, 0, x_5);
x_88 = lean_apply_1(x_3, x_1);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_83);
lean_free_object(x_28);
lean_dec(x_41);
lean_free_object(x_1);
lean_free_object(x_6);
lean_free_object(x_5);
lean_free_object(x_4);
lean_dec(x_3);
x_89 = lean_box_uint64(x_16);
x_90 = lean_box_uint64(x_12);
x_91 = lean_box_uint64(x_40);
x_92 = lean_box_uint64(x_10);
x_93 = lean_box_uint64(x_20);
x_94 = lean_box_uint64(x_78);
x_95 = lean_box_uint64(x_42);
x_96 = lean_apply_10(x_2, x_15, x_89, x_11, x_90, x_38, x_91, x_92, x_93, x_94, x_95);
return x_96;
}
}
}
}
else
{
uint64_t x_97; lean_object* x_98; uint64_t x_99; lean_object* x_100; uint64_t x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_97 = lean_ctor_get_uint64(x_8, sizeof(void*)*2);
x_98 = lean_ctor_get(x_28, 1);
x_99 = lean_ctor_get_uint64(x_28, sizeof(void*)*2);
lean_inc(x_98);
lean_dec(x_28);
x_100 = lean_ctor_get(x_30, 1);
lean_inc(x_100);
x_101 = lean_ctor_get_uint64(x_30, sizeof(void*)*2);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_102 = x_30;
} else {
 lean_dec_ref(x_30);
 x_102 = lean_box(0);
}
x_103 = l_Lean_instQuoteBool___closed__1;
x_104 = lean_string_dec_eq(x_100, x_103);
lean_dec(x_100);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_98);
lean_dec(x_38);
lean_free_object(x_6);
lean_dec(x_2);
if (lean_is_scalar(x_102)) {
 x_105 = lean_alloc_ctor(1, 2, 8);
} else {
 x_105 = x_102;
}
lean_ctor_set(x_105, 0, x_37);
lean_ctor_set(x_105, 1, x_22);
lean_ctor_set_uint64(x_105, sizeof(void*)*2, x_20);
lean_ctor_set(x_5, 0, x_105);
x_106 = lean_apply_1(x_3, x_1);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_107 = x_8;
} else {
 lean_dec_ref(x_8);
 x_107 = lean_box(0);
}
x_108 = l_instReprBool___closed__2;
x_109 = lean_string_dec_eq(x_98, x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_2);
if (lean_is_scalar(x_102)) {
 x_110 = lean_alloc_ctor(1, 2, 8);
} else {
 x_110 = x_102;
}
lean_ctor_set(x_110, 0, x_37);
lean_ctor_set(x_110, 1, x_22);
lean_ctor_set_uint64(x_110, sizeof(void*)*2, x_20);
if (lean_is_scalar(x_107)) {
 x_111 = lean_alloc_ctor(4, 2, 8);
} else {
 x_111 = x_107;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_15);
lean_ctor_set_uint64(x_111, sizeof(void*)*2, x_16);
lean_ctor_set_tag(x_5, 5);
lean_ctor_set(x_5, 1, x_11);
lean_ctor_set(x_5, 0, x_111);
lean_ctor_set_uint64(x_5, sizeof(void*)*2, x_12);
x_112 = lean_alloc_ctor(1, 2, 8);
lean_ctor_set(x_112, 0, x_37);
lean_ctor_set(x_112, 1, x_103);
lean_ctor_set_uint64(x_112, sizeof(void*)*2, x_101);
lean_ctor_set(x_6, 1, x_98);
lean_ctor_set(x_6, 0, x_112);
lean_ctor_set_uint64(x_6, sizeof(void*)*2, x_99);
lean_ctor_set_tag(x_4, 4);
lean_ctor_set(x_4, 1, x_38);
lean_ctor_set(x_4, 0, x_6);
lean_ctor_set_uint64(x_4, sizeof(void*)*2, x_97);
lean_ctor_set(x_1, 1, x_4);
lean_ctor_set(x_1, 0, x_5);
x_113 = lean_apply_1(x_3, x_1);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_107);
lean_dec(x_102);
lean_dec(x_98);
lean_free_object(x_1);
lean_free_object(x_6);
lean_free_object(x_5);
lean_free_object(x_4);
lean_dec(x_3);
x_114 = lean_box_uint64(x_16);
x_115 = lean_box_uint64(x_12);
x_116 = lean_box_uint64(x_97);
x_117 = lean_box_uint64(x_10);
x_118 = lean_box_uint64(x_20);
x_119 = lean_box_uint64(x_101);
x_120 = lean_box_uint64(x_99);
x_121 = lean_apply_10(x_2, x_15, x_114, x_11, x_115, x_38, x_116, x_117, x_118, x_119, x_120);
return x_121;
}
}
}
}
case 1:
{
uint8_t x_122; 
lean_dec(x_30);
lean_dec(x_28);
lean_free_object(x_6);
lean_dec(x_2);
x_122 = !lean_is_exclusive(x_37);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_37, 1);
lean_dec(x_123);
x_124 = lean_ctor_get(x_37, 0);
lean_dec(x_124);
lean_ctor_set(x_37, 1, x_22);
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set_uint64(x_37, sizeof(void*)*2, x_20);
lean_ctor_set(x_5, 0, x_37);
x_125 = lean_apply_1(x_3, x_1);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_37);
x_126 = lean_alloc_ctor(1, 2, 8);
lean_ctor_set(x_126, 0, x_7);
lean_ctor_set(x_126, 1, x_22);
lean_ctor_set_uint64(x_126, sizeof(void*)*2, x_20);
lean_ctor_set(x_5, 0, x_126);
x_127 = lean_apply_1(x_3, x_1);
return x_127;
}
}
default: 
{
uint8_t x_128; 
lean_dec(x_30);
lean_dec(x_28);
lean_free_object(x_6);
lean_dec(x_2);
x_128 = !lean_is_exclusive(x_37);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_37, 1);
lean_dec(x_129);
x_130 = lean_ctor_get(x_37, 0);
lean_dec(x_130);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_22);
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set_uint64(x_37, sizeof(void*)*2, x_20);
lean_ctor_set(x_5, 0, x_37);
x_131 = lean_apply_1(x_3, x_1);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_37);
x_132 = lean_alloc_ctor(1, 2, 8);
lean_ctor_set(x_132, 0, x_7);
lean_ctor_set(x_132, 1, x_22);
lean_ctor_set_uint64(x_132, sizeof(void*)*2, x_20);
lean_ctor_set(x_5, 0, x_132);
x_133 = lean_apply_1(x_3, x_1);
return x_133;
}
}
}
}
default: 
{
uint8_t x_134; 
lean_dec(x_28);
lean_free_object(x_6);
lean_dec(x_2);
x_134 = !lean_is_exclusive(x_30);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_30, 1);
lean_dec(x_135);
x_136 = lean_ctor_get(x_30, 0);
lean_dec(x_136);
lean_ctor_set_tag(x_30, 1);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set_uint64(x_30, sizeof(void*)*2, x_20);
lean_ctor_set(x_5, 0, x_30);
x_137 = lean_apply_1(x_3, x_1);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_30);
x_138 = lean_alloc_ctor(1, 2, 8);
lean_ctor_set(x_138, 0, x_7);
lean_ctor_set(x_138, 1, x_22);
lean_ctor_set_uint64(x_138, sizeof(void*)*2, x_20);
lean_ctor_set(x_5, 0, x_138);
x_139 = lean_apply_1(x_3, x_1);
return x_139;
}
}
}
}
default: 
{
uint8_t x_140; 
lean_free_object(x_6);
lean_dec(x_2);
x_140 = !lean_is_exclusive(x_28);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_28, 1);
lean_dec(x_141);
x_142 = lean_ctor_get(x_28, 0);
lean_dec(x_142);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 1, x_22);
lean_ctor_set(x_28, 0, x_7);
lean_ctor_set_uint64(x_28, sizeof(void*)*2, x_20);
lean_ctor_set(x_5, 0, x_28);
x_143 = lean_apply_1(x_3, x_1);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_28);
x_144 = lean_alloc_ctor(1, 2, 8);
lean_ctor_set(x_144, 0, x_7);
lean_ctor_set(x_144, 1, x_22);
lean_ctor_set_uint64(x_144, sizeof(void*)*2, x_20);
lean_ctor_set(x_5, 0, x_144);
x_145 = lean_apply_1(x_3, x_1);
return x_145;
}
}
}
}
else
{
lean_object* x_146; 
lean_dec(x_2);
lean_ctor_set(x_6, 1, x_22);
x_146 = lean_apply_1(x_3, x_1);
return x_146;
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_8) == 4)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_8, 0);
lean_inc(x_147);
switch (lean_obj_tag(x_147)) {
case 0:
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_2);
lean_ctor_set(x_6, 1, x_22);
lean_ctor_set(x_6, 0, x_147);
x_148 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_148, 0, x_4);
lean_ctor_set(x_148, 1, x_8);
lean_ctor_set_uint64(x_148, sizeof(void*)*2, x_10);
x_149 = lean_apply_1(x_3, x_148);
return x_149;
}
case 1:
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_147, 0);
lean_inc(x_150);
switch (lean_obj_tag(x_150)) {
case 0:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_free_object(x_6);
lean_dec(x_2);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_151 = x_147;
} else {
 lean_dec_ref(x_147);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 8);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_22);
lean_ctor_set_uint64(x_152, sizeof(void*)*2, x_20);
lean_ctor_set(x_5, 0, x_152);
x_153 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_153, 0, x_4);
lean_ctor_set(x_153, 1, x_8);
lean_ctor_set_uint64(x_153, sizeof(void*)*2, x_10);
x_154 = lean_apply_1(x_3, x_153);
return x_154;
}
case 1:
{
lean_object* x_155; 
x_155 = lean_ctor_get(x_150, 0);
lean_inc(x_155);
switch (lean_obj_tag(x_155)) {
case 0:
{
lean_object* x_156; uint64_t x_157; lean_object* x_158; uint64_t x_159; lean_object* x_160; lean_object* x_161; uint64_t x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_156 = lean_ctor_get(x_8, 1);
lean_inc(x_156);
x_157 = lean_ctor_get_uint64(x_8, sizeof(void*)*2);
x_158 = lean_ctor_get(x_147, 1);
lean_inc(x_158);
x_159 = lean_ctor_get_uint64(x_147, sizeof(void*)*2);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_160 = x_147;
} else {
 lean_dec_ref(x_147);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_150, 1);
lean_inc(x_161);
x_162 = lean_ctor_get_uint64(x_150, sizeof(void*)*2);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_163 = x_150;
} else {
 lean_dec_ref(x_150);
 x_163 = lean_box(0);
}
x_164 = l_Lean_instQuoteBool___closed__1;
x_165 = lean_string_dec_eq(x_161, x_164);
lean_dec(x_161);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_156);
lean_free_object(x_6);
lean_dec(x_2);
if (lean_is_scalar(x_163)) {
 x_166 = lean_alloc_ctor(1, 2, 8);
} else {
 x_166 = x_163;
}
lean_ctor_set(x_166, 0, x_155);
lean_ctor_set(x_166, 1, x_22);
lean_ctor_set_uint64(x_166, sizeof(void*)*2, x_20);
lean_ctor_set(x_5, 0, x_166);
x_167 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_167, 0, x_4);
lean_ctor_set(x_167, 1, x_8);
lean_ctor_set_uint64(x_167, sizeof(void*)*2, x_10);
x_168 = lean_apply_1(x_3, x_167);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; 
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_169 = x_8;
} else {
 lean_dec_ref(x_8);
 x_169 = lean_box(0);
}
x_170 = l_instReprBool___closed__2;
x_171 = lean_string_dec_eq(x_158, x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_2);
if (lean_is_scalar(x_163)) {
 x_172 = lean_alloc_ctor(1, 2, 8);
} else {
 x_172 = x_163;
}
lean_ctor_set(x_172, 0, x_155);
lean_ctor_set(x_172, 1, x_22);
lean_ctor_set_uint64(x_172, sizeof(void*)*2, x_20);
if (lean_is_scalar(x_169)) {
 x_173 = lean_alloc_ctor(4, 2, 8);
} else {
 x_173 = x_169;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_15);
lean_ctor_set_uint64(x_173, sizeof(void*)*2, x_16);
lean_ctor_set_tag(x_5, 5);
lean_ctor_set(x_5, 1, x_11);
lean_ctor_set(x_5, 0, x_173);
lean_ctor_set_uint64(x_5, sizeof(void*)*2, x_12);
if (lean_is_scalar(x_160)) {
 x_174 = lean_alloc_ctor(1, 2, 8);
} else {
 x_174 = x_160;
}
lean_ctor_set(x_174, 0, x_155);
lean_ctor_set(x_174, 1, x_164);
lean_ctor_set_uint64(x_174, sizeof(void*)*2, x_162);
lean_ctor_set(x_6, 1, x_158);
lean_ctor_set(x_6, 0, x_174);
lean_ctor_set_uint64(x_6, sizeof(void*)*2, x_159);
lean_ctor_set_tag(x_4, 4);
lean_ctor_set(x_4, 1, x_156);
lean_ctor_set(x_4, 0, x_6);
lean_ctor_set_uint64(x_4, sizeof(void*)*2, x_157);
x_175 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_175, 0, x_5);
lean_ctor_set(x_175, 1, x_4);
lean_ctor_set_uint64(x_175, sizeof(void*)*2, x_10);
x_176 = lean_apply_1(x_3, x_175);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_169);
lean_dec(x_163);
lean_dec(x_160);
lean_dec(x_158);
lean_free_object(x_6);
lean_free_object(x_5);
lean_free_object(x_4);
lean_dec(x_3);
x_177 = lean_box_uint64(x_16);
x_178 = lean_box_uint64(x_12);
x_179 = lean_box_uint64(x_157);
x_180 = lean_box_uint64(x_10);
x_181 = lean_box_uint64(x_20);
x_182 = lean_box_uint64(x_162);
x_183 = lean_box_uint64(x_159);
x_184 = lean_apply_10(x_2, x_15, x_177, x_11, x_178, x_156, x_179, x_180, x_181, x_182, x_183);
return x_184;
}
}
}
case 1:
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_150);
lean_dec(x_147);
lean_free_object(x_6);
lean_dec(x_2);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_185 = x_155;
} else {
 lean_dec_ref(x_155);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 2, 8);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_7);
lean_ctor_set(x_186, 1, x_22);
lean_ctor_set_uint64(x_186, sizeof(void*)*2, x_20);
lean_ctor_set(x_5, 0, x_186);
x_187 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_187, 0, x_4);
lean_ctor_set(x_187, 1, x_8);
lean_ctor_set_uint64(x_187, sizeof(void*)*2, x_10);
x_188 = lean_apply_1(x_3, x_187);
return x_188;
}
default: 
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_150);
lean_dec(x_147);
lean_free_object(x_6);
lean_dec(x_2);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_189 = x_155;
} else {
 lean_dec_ref(x_155);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 2, 8);
} else {
 x_190 = x_189;
 lean_ctor_set_tag(x_190, 1);
}
lean_ctor_set(x_190, 0, x_7);
lean_ctor_set(x_190, 1, x_22);
lean_ctor_set_uint64(x_190, sizeof(void*)*2, x_20);
lean_ctor_set(x_5, 0, x_190);
x_191 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_191, 0, x_4);
lean_ctor_set(x_191, 1, x_8);
lean_ctor_set_uint64(x_191, sizeof(void*)*2, x_10);
x_192 = lean_apply_1(x_3, x_191);
return x_192;
}
}
}
default: 
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_147);
lean_free_object(x_6);
lean_dec(x_2);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_193 = x_150;
} else {
 lean_dec_ref(x_150);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 8);
} else {
 x_194 = x_193;
 lean_ctor_set_tag(x_194, 1);
}
lean_ctor_set(x_194, 0, x_7);
lean_ctor_set(x_194, 1, x_22);
lean_ctor_set_uint64(x_194, sizeof(void*)*2, x_20);
lean_ctor_set(x_5, 0, x_194);
x_195 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_195, 0, x_4);
lean_ctor_set(x_195, 1, x_8);
lean_ctor_set_uint64(x_195, sizeof(void*)*2, x_10);
x_196 = lean_apply_1(x_3, x_195);
return x_196;
}
}
}
default: 
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_free_object(x_6);
lean_dec(x_2);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_197 = x_147;
} else {
 lean_dec_ref(x_147);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 8);
} else {
 x_198 = x_197;
 lean_ctor_set_tag(x_198, 1);
}
lean_ctor_set(x_198, 0, x_7);
lean_ctor_set(x_198, 1, x_22);
lean_ctor_set_uint64(x_198, sizeof(void*)*2, x_20);
lean_ctor_set(x_5, 0, x_198);
x_199 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_199, 0, x_4);
lean_ctor_set(x_199, 1, x_8);
lean_ctor_set_uint64(x_199, sizeof(void*)*2, x_10);
x_200 = lean_apply_1(x_3, x_199);
return x_200;
}
}
}
else
{
lean_object* x_201; lean_object* x_202; 
lean_dec(x_2);
lean_ctor_set(x_6, 1, x_22);
x_201 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_201, 0, x_4);
lean_ctor_set(x_201, 1, x_8);
lean_ctor_set_uint64(x_201, sizeof(void*)*2, x_10);
x_202 = lean_apply_1(x_3, x_201);
return x_202;
}
}
}
}
else
{
lean_object* x_203; uint64_t x_204; lean_object* x_205; uint8_t x_206; 
x_203 = lean_ctor_get(x_6, 1);
x_204 = lean_ctor_get_uint64(x_6, sizeof(void*)*2);
lean_inc(x_203);
lean_dec(x_6);
x_205 = l_Lean_Expr_isSorry_match__1___rarg___closed__1;
x_206 = lean_string_dec_eq(x_203, x_205);
lean_dec(x_203);
if (x_206 == 0)
{
lean_object* x_207; 
lean_free_object(x_5);
lean_dec(x_15);
lean_free_object(x_4);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_2);
x_207 = lean_apply_1(x_3, x_1);
return x_207;
}
else
{
lean_object* x_208; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_208 = x_1;
} else {
 lean_dec_ref(x_1);
 x_208 = lean_box(0);
}
if (lean_obj_tag(x_8) == 4)
{
lean_object* x_209; 
x_209 = lean_ctor_get(x_8, 0);
lean_inc(x_209);
switch (lean_obj_tag(x_209)) {
case 0:
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_2);
x_210 = lean_alloc_ctor(1, 2, 8);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_205);
lean_ctor_set_uint64(x_210, sizeof(void*)*2, x_204);
lean_ctor_set(x_5, 0, x_210);
if (lean_is_scalar(x_208)) {
 x_211 = lean_alloc_ctor(5, 2, 8);
} else {
 x_211 = x_208;
}
lean_ctor_set(x_211, 0, x_4);
lean_ctor_set(x_211, 1, x_8);
lean_ctor_set_uint64(x_211, sizeof(void*)*2, x_10);
x_212 = lean_apply_1(x_3, x_211);
return x_212;
}
case 1:
{
lean_object* x_213; 
x_213 = lean_ctor_get(x_209, 0);
lean_inc(x_213);
switch (lean_obj_tag(x_213)) {
case 0:
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_2);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_214 = x_209;
} else {
 lean_dec_ref(x_209);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(1, 2, 8);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_205);
lean_ctor_set_uint64(x_215, sizeof(void*)*2, x_204);
lean_ctor_set(x_5, 0, x_215);
if (lean_is_scalar(x_208)) {
 x_216 = lean_alloc_ctor(5, 2, 8);
} else {
 x_216 = x_208;
}
lean_ctor_set(x_216, 0, x_4);
lean_ctor_set(x_216, 1, x_8);
lean_ctor_set_uint64(x_216, sizeof(void*)*2, x_10);
x_217 = lean_apply_1(x_3, x_216);
return x_217;
}
case 1:
{
lean_object* x_218; 
x_218 = lean_ctor_get(x_213, 0);
lean_inc(x_218);
switch (lean_obj_tag(x_218)) {
case 0:
{
lean_object* x_219; uint64_t x_220; lean_object* x_221; uint64_t x_222; lean_object* x_223; lean_object* x_224; uint64_t x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; 
x_219 = lean_ctor_get(x_8, 1);
lean_inc(x_219);
x_220 = lean_ctor_get_uint64(x_8, sizeof(void*)*2);
x_221 = lean_ctor_get(x_209, 1);
lean_inc(x_221);
x_222 = lean_ctor_get_uint64(x_209, sizeof(void*)*2);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_223 = x_209;
} else {
 lean_dec_ref(x_209);
 x_223 = lean_box(0);
}
x_224 = lean_ctor_get(x_213, 1);
lean_inc(x_224);
x_225 = lean_ctor_get_uint64(x_213, sizeof(void*)*2);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_226 = x_213;
} else {
 lean_dec_ref(x_213);
 x_226 = lean_box(0);
}
x_227 = l_Lean_instQuoteBool___closed__1;
x_228 = lean_string_dec_eq(x_224, x_227);
lean_dec(x_224);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_223);
lean_dec(x_221);
lean_dec(x_219);
lean_dec(x_2);
if (lean_is_scalar(x_226)) {
 x_229 = lean_alloc_ctor(1, 2, 8);
} else {
 x_229 = x_226;
}
lean_ctor_set(x_229, 0, x_218);
lean_ctor_set(x_229, 1, x_205);
lean_ctor_set_uint64(x_229, sizeof(void*)*2, x_204);
lean_ctor_set(x_5, 0, x_229);
if (lean_is_scalar(x_208)) {
 x_230 = lean_alloc_ctor(5, 2, 8);
} else {
 x_230 = x_208;
}
lean_ctor_set(x_230, 0, x_4);
lean_ctor_set(x_230, 1, x_8);
lean_ctor_set_uint64(x_230, sizeof(void*)*2, x_10);
x_231 = lean_apply_1(x_3, x_230);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; uint8_t x_234; 
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_232 = x_8;
} else {
 lean_dec_ref(x_8);
 x_232 = lean_box(0);
}
x_233 = l_instReprBool___closed__2;
x_234 = lean_string_dec_eq(x_221, x_233);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_2);
if (lean_is_scalar(x_226)) {
 x_235 = lean_alloc_ctor(1, 2, 8);
} else {
 x_235 = x_226;
}
lean_ctor_set(x_235, 0, x_218);
lean_ctor_set(x_235, 1, x_205);
lean_ctor_set_uint64(x_235, sizeof(void*)*2, x_204);
if (lean_is_scalar(x_232)) {
 x_236 = lean_alloc_ctor(4, 2, 8);
} else {
 x_236 = x_232;
}
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_15);
lean_ctor_set_uint64(x_236, sizeof(void*)*2, x_16);
lean_ctor_set_tag(x_5, 5);
lean_ctor_set(x_5, 1, x_11);
lean_ctor_set(x_5, 0, x_236);
lean_ctor_set_uint64(x_5, sizeof(void*)*2, x_12);
if (lean_is_scalar(x_223)) {
 x_237 = lean_alloc_ctor(1, 2, 8);
} else {
 x_237 = x_223;
}
lean_ctor_set(x_237, 0, x_218);
lean_ctor_set(x_237, 1, x_227);
lean_ctor_set_uint64(x_237, sizeof(void*)*2, x_225);
x_238 = lean_alloc_ctor(1, 2, 8);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_221);
lean_ctor_set_uint64(x_238, sizeof(void*)*2, x_222);
lean_ctor_set_tag(x_4, 4);
lean_ctor_set(x_4, 1, x_219);
lean_ctor_set(x_4, 0, x_238);
lean_ctor_set_uint64(x_4, sizeof(void*)*2, x_220);
if (lean_is_scalar(x_208)) {
 x_239 = lean_alloc_ctor(5, 2, 8);
} else {
 x_239 = x_208;
}
lean_ctor_set(x_239, 0, x_5);
lean_ctor_set(x_239, 1, x_4);
lean_ctor_set_uint64(x_239, sizeof(void*)*2, x_10);
x_240 = lean_apply_1(x_3, x_239);
return x_240;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_232);
lean_dec(x_226);
lean_dec(x_223);
lean_dec(x_221);
lean_dec(x_208);
lean_free_object(x_5);
lean_free_object(x_4);
lean_dec(x_3);
x_241 = lean_box_uint64(x_16);
x_242 = lean_box_uint64(x_12);
x_243 = lean_box_uint64(x_220);
x_244 = lean_box_uint64(x_10);
x_245 = lean_box_uint64(x_204);
x_246 = lean_box_uint64(x_225);
x_247 = lean_box_uint64(x_222);
x_248 = lean_apply_10(x_2, x_15, x_241, x_11, x_242, x_219, x_243, x_244, x_245, x_246, x_247);
return x_248;
}
}
}
case 1:
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_213);
lean_dec(x_209);
lean_dec(x_2);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_249 = x_218;
} else {
 lean_dec_ref(x_218);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(1, 2, 8);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_7);
lean_ctor_set(x_250, 1, x_205);
lean_ctor_set_uint64(x_250, sizeof(void*)*2, x_204);
lean_ctor_set(x_5, 0, x_250);
if (lean_is_scalar(x_208)) {
 x_251 = lean_alloc_ctor(5, 2, 8);
} else {
 x_251 = x_208;
}
lean_ctor_set(x_251, 0, x_4);
lean_ctor_set(x_251, 1, x_8);
lean_ctor_set_uint64(x_251, sizeof(void*)*2, x_10);
x_252 = lean_apply_1(x_3, x_251);
return x_252;
}
default: 
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_213);
lean_dec(x_209);
lean_dec(x_2);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_253 = x_218;
} else {
 lean_dec_ref(x_218);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(1, 2, 8);
} else {
 x_254 = x_253;
 lean_ctor_set_tag(x_254, 1);
}
lean_ctor_set(x_254, 0, x_7);
lean_ctor_set(x_254, 1, x_205);
lean_ctor_set_uint64(x_254, sizeof(void*)*2, x_204);
lean_ctor_set(x_5, 0, x_254);
if (lean_is_scalar(x_208)) {
 x_255 = lean_alloc_ctor(5, 2, 8);
} else {
 x_255 = x_208;
}
lean_ctor_set(x_255, 0, x_4);
lean_ctor_set(x_255, 1, x_8);
lean_ctor_set_uint64(x_255, sizeof(void*)*2, x_10);
x_256 = lean_apply_1(x_3, x_255);
return x_256;
}
}
}
default: 
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_209);
lean_dec(x_2);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_257 = x_213;
} else {
 lean_dec_ref(x_213);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(1, 2, 8);
} else {
 x_258 = x_257;
 lean_ctor_set_tag(x_258, 1);
}
lean_ctor_set(x_258, 0, x_7);
lean_ctor_set(x_258, 1, x_205);
lean_ctor_set_uint64(x_258, sizeof(void*)*2, x_204);
lean_ctor_set(x_5, 0, x_258);
if (lean_is_scalar(x_208)) {
 x_259 = lean_alloc_ctor(5, 2, 8);
} else {
 x_259 = x_208;
}
lean_ctor_set(x_259, 0, x_4);
lean_ctor_set(x_259, 1, x_8);
lean_ctor_set_uint64(x_259, sizeof(void*)*2, x_10);
x_260 = lean_apply_1(x_3, x_259);
return x_260;
}
}
}
default: 
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_2);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_261 = x_209;
} else {
 lean_dec_ref(x_209);
 x_261 = lean_box(0);
}
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(1, 2, 8);
} else {
 x_262 = x_261;
 lean_ctor_set_tag(x_262, 1);
}
lean_ctor_set(x_262, 0, x_7);
lean_ctor_set(x_262, 1, x_205);
lean_ctor_set_uint64(x_262, sizeof(void*)*2, x_204);
lean_ctor_set(x_5, 0, x_262);
if (lean_is_scalar(x_208)) {
 x_263 = lean_alloc_ctor(5, 2, 8);
} else {
 x_263 = x_208;
}
lean_ctor_set(x_263, 0, x_4);
lean_ctor_set(x_263, 1, x_8);
lean_ctor_set_uint64(x_263, sizeof(void*)*2, x_10);
x_264 = lean_apply_1(x_3, x_263);
return x_264;
}
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_2);
x_265 = lean_alloc_ctor(1, 2, 8);
lean_ctor_set(x_265, 0, x_7);
lean_ctor_set(x_265, 1, x_205);
lean_ctor_set_uint64(x_265, sizeof(void*)*2, x_204);
lean_ctor_set(x_5, 0, x_265);
if (lean_is_scalar(x_208)) {
 x_266 = lean_alloc_ctor(5, 2, 8);
} else {
 x_266 = x_208;
}
lean_ctor_set(x_266, 0, x_4);
lean_ctor_set(x_266, 1, x_8);
lean_ctor_set_uint64(x_266, sizeof(void*)*2, x_10);
x_267 = lean_apply_1(x_3, x_266);
return x_267;
}
}
}
}
else
{
lean_object* x_268; uint64_t x_269; lean_object* x_270; uint64_t x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; 
x_268 = lean_ctor_get(x_5, 1);
x_269 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_268);
lean_dec(x_5);
x_270 = lean_ctor_get(x_6, 1);
lean_inc(x_270);
x_271 = lean_ctor_get_uint64(x_6, sizeof(void*)*2);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_272 = x_6;
} else {
 lean_dec_ref(x_6);
 x_272 = lean_box(0);
}
x_273 = l_Lean_Expr_isSorry_match__1___rarg___closed__1;
x_274 = lean_string_dec_eq(x_270, x_273);
lean_dec(x_270);
if (x_274 == 0)
{
lean_object* x_275; 
lean_dec(x_272);
lean_dec(x_268);
lean_free_object(x_4);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_2);
x_275 = lean_apply_1(x_3, x_1);
return x_275;
}
else
{
lean_object* x_276; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_276 = x_1;
} else {
 lean_dec_ref(x_1);
 x_276 = lean_box(0);
}
if (lean_obj_tag(x_8) == 4)
{
lean_object* x_277; 
x_277 = lean_ctor_get(x_8, 0);
lean_inc(x_277);
switch (lean_obj_tag(x_277)) {
case 0:
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_2);
if (lean_is_scalar(x_272)) {
 x_278 = lean_alloc_ctor(1, 2, 8);
} else {
 x_278 = x_272;
}
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_273);
lean_ctor_set_uint64(x_278, sizeof(void*)*2, x_271);
x_279 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_268);
lean_ctor_set_uint64(x_279, sizeof(void*)*2, x_269);
lean_ctor_set(x_4, 0, x_279);
if (lean_is_scalar(x_276)) {
 x_280 = lean_alloc_ctor(5, 2, 8);
} else {
 x_280 = x_276;
}
lean_ctor_set(x_280, 0, x_4);
lean_ctor_set(x_280, 1, x_8);
lean_ctor_set_uint64(x_280, sizeof(void*)*2, x_10);
x_281 = lean_apply_1(x_3, x_280);
return x_281;
}
case 1:
{
lean_object* x_282; 
x_282 = lean_ctor_get(x_277, 0);
lean_inc(x_282);
switch (lean_obj_tag(x_282)) {
case 0:
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
lean_dec(x_272);
lean_dec(x_2);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_283 = x_277;
} else {
 lean_dec_ref(x_277);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(1, 2, 8);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_273);
lean_ctor_set_uint64(x_284, sizeof(void*)*2, x_271);
x_285 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_268);
lean_ctor_set_uint64(x_285, sizeof(void*)*2, x_269);
lean_ctor_set(x_4, 0, x_285);
if (lean_is_scalar(x_276)) {
 x_286 = lean_alloc_ctor(5, 2, 8);
} else {
 x_286 = x_276;
}
lean_ctor_set(x_286, 0, x_4);
lean_ctor_set(x_286, 1, x_8);
lean_ctor_set_uint64(x_286, sizeof(void*)*2, x_10);
x_287 = lean_apply_1(x_3, x_286);
return x_287;
}
case 1:
{
lean_object* x_288; 
x_288 = lean_ctor_get(x_282, 0);
lean_inc(x_288);
switch (lean_obj_tag(x_288)) {
case 0:
{
lean_object* x_289; uint64_t x_290; lean_object* x_291; uint64_t x_292; lean_object* x_293; lean_object* x_294; uint64_t x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_289 = lean_ctor_get(x_8, 1);
lean_inc(x_289);
x_290 = lean_ctor_get_uint64(x_8, sizeof(void*)*2);
x_291 = lean_ctor_get(x_277, 1);
lean_inc(x_291);
x_292 = lean_ctor_get_uint64(x_277, sizeof(void*)*2);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_293 = x_277;
} else {
 lean_dec_ref(x_277);
 x_293 = lean_box(0);
}
x_294 = lean_ctor_get(x_282, 1);
lean_inc(x_294);
x_295 = lean_ctor_get_uint64(x_282, sizeof(void*)*2);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_296 = x_282;
} else {
 lean_dec_ref(x_282);
 x_296 = lean_box(0);
}
x_297 = l_Lean_instQuoteBool___closed__1;
x_298 = lean_string_dec_eq(x_294, x_297);
lean_dec(x_294);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_293);
lean_dec(x_291);
lean_dec(x_289);
lean_dec(x_272);
lean_dec(x_2);
if (lean_is_scalar(x_296)) {
 x_299 = lean_alloc_ctor(1, 2, 8);
} else {
 x_299 = x_296;
}
lean_ctor_set(x_299, 0, x_288);
lean_ctor_set(x_299, 1, x_273);
lean_ctor_set_uint64(x_299, sizeof(void*)*2, x_271);
x_300 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_268);
lean_ctor_set_uint64(x_300, sizeof(void*)*2, x_269);
lean_ctor_set(x_4, 0, x_300);
if (lean_is_scalar(x_276)) {
 x_301 = lean_alloc_ctor(5, 2, 8);
} else {
 x_301 = x_276;
}
lean_ctor_set(x_301, 0, x_4);
lean_ctor_set(x_301, 1, x_8);
lean_ctor_set_uint64(x_301, sizeof(void*)*2, x_10);
x_302 = lean_apply_1(x_3, x_301);
return x_302;
}
else
{
lean_object* x_303; lean_object* x_304; uint8_t x_305; 
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_303 = x_8;
} else {
 lean_dec_ref(x_8);
 x_303 = lean_box(0);
}
x_304 = l_instReprBool___closed__2;
x_305 = lean_string_dec_eq(x_291, x_304);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_2);
if (lean_is_scalar(x_296)) {
 x_306 = lean_alloc_ctor(1, 2, 8);
} else {
 x_306 = x_296;
}
lean_ctor_set(x_306, 0, x_288);
lean_ctor_set(x_306, 1, x_273);
lean_ctor_set_uint64(x_306, sizeof(void*)*2, x_271);
if (lean_is_scalar(x_303)) {
 x_307 = lean_alloc_ctor(4, 2, 8);
} else {
 x_307 = x_303;
}
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_268);
lean_ctor_set_uint64(x_307, sizeof(void*)*2, x_269);
x_308 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_11);
lean_ctor_set_uint64(x_308, sizeof(void*)*2, x_12);
if (lean_is_scalar(x_293)) {
 x_309 = lean_alloc_ctor(1, 2, 8);
} else {
 x_309 = x_293;
}
lean_ctor_set(x_309, 0, x_288);
lean_ctor_set(x_309, 1, x_297);
lean_ctor_set_uint64(x_309, sizeof(void*)*2, x_295);
if (lean_is_scalar(x_272)) {
 x_310 = lean_alloc_ctor(1, 2, 8);
} else {
 x_310 = x_272;
}
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_291);
lean_ctor_set_uint64(x_310, sizeof(void*)*2, x_292);
lean_ctor_set_tag(x_4, 4);
lean_ctor_set(x_4, 1, x_289);
lean_ctor_set(x_4, 0, x_310);
lean_ctor_set_uint64(x_4, sizeof(void*)*2, x_290);
if (lean_is_scalar(x_276)) {
 x_311 = lean_alloc_ctor(5, 2, 8);
} else {
 x_311 = x_276;
}
lean_ctor_set(x_311, 0, x_308);
lean_ctor_set(x_311, 1, x_4);
lean_ctor_set_uint64(x_311, sizeof(void*)*2, x_10);
x_312 = lean_apply_1(x_3, x_311);
return x_312;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_303);
lean_dec(x_296);
lean_dec(x_293);
lean_dec(x_291);
lean_dec(x_276);
lean_dec(x_272);
lean_free_object(x_4);
lean_dec(x_3);
x_313 = lean_box_uint64(x_269);
x_314 = lean_box_uint64(x_12);
x_315 = lean_box_uint64(x_290);
x_316 = lean_box_uint64(x_10);
x_317 = lean_box_uint64(x_271);
x_318 = lean_box_uint64(x_295);
x_319 = lean_box_uint64(x_292);
x_320 = lean_apply_10(x_2, x_268, x_313, x_11, x_314, x_289, x_315, x_316, x_317, x_318, x_319);
return x_320;
}
}
}
case 1:
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_282);
lean_dec(x_277);
lean_dec(x_272);
lean_dec(x_2);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_321 = x_288;
} else {
 lean_dec_ref(x_288);
 x_321 = lean_box(0);
}
if (lean_is_scalar(x_321)) {
 x_322 = lean_alloc_ctor(1, 2, 8);
} else {
 x_322 = x_321;
}
lean_ctor_set(x_322, 0, x_7);
lean_ctor_set(x_322, 1, x_273);
lean_ctor_set_uint64(x_322, sizeof(void*)*2, x_271);
x_323 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_268);
lean_ctor_set_uint64(x_323, sizeof(void*)*2, x_269);
lean_ctor_set(x_4, 0, x_323);
if (lean_is_scalar(x_276)) {
 x_324 = lean_alloc_ctor(5, 2, 8);
} else {
 x_324 = x_276;
}
lean_ctor_set(x_324, 0, x_4);
lean_ctor_set(x_324, 1, x_8);
lean_ctor_set_uint64(x_324, sizeof(void*)*2, x_10);
x_325 = lean_apply_1(x_3, x_324);
return x_325;
}
default: 
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_282);
lean_dec(x_277);
lean_dec(x_272);
lean_dec(x_2);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_326 = x_288;
} else {
 lean_dec_ref(x_288);
 x_326 = lean_box(0);
}
if (lean_is_scalar(x_326)) {
 x_327 = lean_alloc_ctor(1, 2, 8);
} else {
 x_327 = x_326;
 lean_ctor_set_tag(x_327, 1);
}
lean_ctor_set(x_327, 0, x_7);
lean_ctor_set(x_327, 1, x_273);
lean_ctor_set_uint64(x_327, sizeof(void*)*2, x_271);
x_328 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_268);
lean_ctor_set_uint64(x_328, sizeof(void*)*2, x_269);
lean_ctor_set(x_4, 0, x_328);
if (lean_is_scalar(x_276)) {
 x_329 = lean_alloc_ctor(5, 2, 8);
} else {
 x_329 = x_276;
}
lean_ctor_set(x_329, 0, x_4);
lean_ctor_set(x_329, 1, x_8);
lean_ctor_set_uint64(x_329, sizeof(void*)*2, x_10);
x_330 = lean_apply_1(x_3, x_329);
return x_330;
}
}
}
default: 
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_dec(x_277);
lean_dec(x_272);
lean_dec(x_2);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_331 = x_282;
} else {
 lean_dec_ref(x_282);
 x_331 = lean_box(0);
}
if (lean_is_scalar(x_331)) {
 x_332 = lean_alloc_ctor(1, 2, 8);
} else {
 x_332 = x_331;
 lean_ctor_set_tag(x_332, 1);
}
lean_ctor_set(x_332, 0, x_7);
lean_ctor_set(x_332, 1, x_273);
lean_ctor_set_uint64(x_332, sizeof(void*)*2, x_271);
x_333 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_268);
lean_ctor_set_uint64(x_333, sizeof(void*)*2, x_269);
lean_ctor_set(x_4, 0, x_333);
if (lean_is_scalar(x_276)) {
 x_334 = lean_alloc_ctor(5, 2, 8);
} else {
 x_334 = x_276;
}
lean_ctor_set(x_334, 0, x_4);
lean_ctor_set(x_334, 1, x_8);
lean_ctor_set_uint64(x_334, sizeof(void*)*2, x_10);
x_335 = lean_apply_1(x_3, x_334);
return x_335;
}
}
}
default: 
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_272);
lean_dec(x_2);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_336 = x_277;
} else {
 lean_dec_ref(x_277);
 x_336 = lean_box(0);
}
if (lean_is_scalar(x_336)) {
 x_337 = lean_alloc_ctor(1, 2, 8);
} else {
 x_337 = x_336;
 lean_ctor_set_tag(x_337, 1);
}
lean_ctor_set(x_337, 0, x_7);
lean_ctor_set(x_337, 1, x_273);
lean_ctor_set_uint64(x_337, sizeof(void*)*2, x_271);
x_338 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_268);
lean_ctor_set_uint64(x_338, sizeof(void*)*2, x_269);
lean_ctor_set(x_4, 0, x_338);
if (lean_is_scalar(x_276)) {
 x_339 = lean_alloc_ctor(5, 2, 8);
} else {
 x_339 = x_276;
}
lean_ctor_set(x_339, 0, x_4);
lean_ctor_set(x_339, 1, x_8);
lean_ctor_set_uint64(x_339, sizeof(void*)*2, x_10);
x_340 = lean_apply_1(x_3, x_339);
return x_340;
}
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec(x_2);
if (lean_is_scalar(x_272)) {
 x_341 = lean_alloc_ctor(1, 2, 8);
} else {
 x_341 = x_272;
}
lean_ctor_set(x_341, 0, x_7);
lean_ctor_set(x_341, 1, x_273);
lean_ctor_set_uint64(x_341, sizeof(void*)*2, x_271);
x_342 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_268);
lean_ctor_set_uint64(x_342, sizeof(void*)*2, x_269);
lean_ctor_set(x_4, 0, x_342);
if (lean_is_scalar(x_276)) {
 x_343 = lean_alloc_ctor(5, 2, 8);
} else {
 x_343 = x_276;
}
lean_ctor_set(x_343, 0, x_4);
lean_ctor_set(x_343, 1, x_8);
lean_ctor_set_uint64(x_343, sizeof(void*)*2, x_10);
x_344 = lean_apply_1(x_3, x_343);
return x_344;
}
}
}
}
else
{
uint64_t x_345; lean_object* x_346; uint64_t x_347; lean_object* x_348; uint64_t x_349; lean_object* x_350; lean_object* x_351; uint64_t x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; 
x_345 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_346 = lean_ctor_get(x_4, 1);
x_347 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
lean_inc(x_346);
lean_dec(x_4);
x_348 = lean_ctor_get(x_5, 1);
lean_inc(x_348);
x_349 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_350 = x_5;
} else {
 lean_dec_ref(x_5);
 x_350 = lean_box(0);
}
x_351 = lean_ctor_get(x_6, 1);
lean_inc(x_351);
x_352 = lean_ctor_get_uint64(x_6, sizeof(void*)*2);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_353 = x_6;
} else {
 lean_dec_ref(x_6);
 x_353 = lean_box(0);
}
x_354 = l_Lean_Expr_isSorry_match__1___rarg___closed__1;
x_355 = lean_string_dec_eq(x_351, x_354);
lean_dec(x_351);
if (x_355 == 0)
{
lean_object* x_356; 
lean_dec(x_353);
lean_dec(x_350);
lean_dec(x_348);
lean_dec(x_346);
lean_dec(x_8);
lean_dec(x_2);
x_356 = lean_apply_1(x_3, x_1);
return x_356;
}
else
{
lean_object* x_357; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_357 = x_1;
} else {
 lean_dec_ref(x_1);
 x_357 = lean_box(0);
}
if (lean_obj_tag(x_8) == 4)
{
lean_object* x_358; 
x_358 = lean_ctor_get(x_8, 0);
lean_inc(x_358);
switch (lean_obj_tag(x_358)) {
case 0:
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec(x_2);
if (lean_is_scalar(x_353)) {
 x_359 = lean_alloc_ctor(1, 2, 8);
} else {
 x_359 = x_353;
}
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_359, 1, x_354);
lean_ctor_set_uint64(x_359, sizeof(void*)*2, x_352);
if (lean_is_scalar(x_350)) {
 x_360 = lean_alloc_ctor(4, 2, 8);
} else {
 x_360 = x_350;
}
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_348);
lean_ctor_set_uint64(x_360, sizeof(void*)*2, x_349);
x_361 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_346);
lean_ctor_set_uint64(x_361, sizeof(void*)*2, x_347);
if (lean_is_scalar(x_357)) {
 x_362 = lean_alloc_ctor(5, 2, 8);
} else {
 x_362 = x_357;
}
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_8);
lean_ctor_set_uint64(x_362, sizeof(void*)*2, x_345);
x_363 = lean_apply_1(x_3, x_362);
return x_363;
}
case 1:
{
lean_object* x_364; 
x_364 = lean_ctor_get(x_358, 0);
lean_inc(x_364);
switch (lean_obj_tag(x_364)) {
case 0:
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
lean_dec(x_353);
lean_dec(x_2);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 x_365 = x_358;
} else {
 lean_dec_ref(x_358);
 x_365 = lean_box(0);
}
if (lean_is_scalar(x_365)) {
 x_366 = lean_alloc_ctor(1, 2, 8);
} else {
 x_366 = x_365;
}
lean_ctor_set(x_366, 0, x_364);
lean_ctor_set(x_366, 1, x_354);
lean_ctor_set_uint64(x_366, sizeof(void*)*2, x_352);
if (lean_is_scalar(x_350)) {
 x_367 = lean_alloc_ctor(4, 2, 8);
} else {
 x_367 = x_350;
}
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_348);
lean_ctor_set_uint64(x_367, sizeof(void*)*2, x_349);
x_368 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_346);
lean_ctor_set_uint64(x_368, sizeof(void*)*2, x_347);
if (lean_is_scalar(x_357)) {
 x_369 = lean_alloc_ctor(5, 2, 8);
} else {
 x_369 = x_357;
}
lean_ctor_set(x_369, 0, x_368);
lean_ctor_set(x_369, 1, x_8);
lean_ctor_set_uint64(x_369, sizeof(void*)*2, x_345);
x_370 = lean_apply_1(x_3, x_369);
return x_370;
}
case 1:
{
lean_object* x_371; 
x_371 = lean_ctor_get(x_364, 0);
lean_inc(x_371);
switch (lean_obj_tag(x_371)) {
case 0:
{
lean_object* x_372; uint64_t x_373; lean_object* x_374; uint64_t x_375; lean_object* x_376; lean_object* x_377; uint64_t x_378; lean_object* x_379; lean_object* x_380; uint8_t x_381; 
x_372 = lean_ctor_get(x_8, 1);
lean_inc(x_372);
x_373 = lean_ctor_get_uint64(x_8, sizeof(void*)*2);
x_374 = lean_ctor_get(x_358, 1);
lean_inc(x_374);
x_375 = lean_ctor_get_uint64(x_358, sizeof(void*)*2);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 x_376 = x_358;
} else {
 lean_dec_ref(x_358);
 x_376 = lean_box(0);
}
x_377 = lean_ctor_get(x_364, 1);
lean_inc(x_377);
x_378 = lean_ctor_get_uint64(x_364, sizeof(void*)*2);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_379 = x_364;
} else {
 lean_dec_ref(x_364);
 x_379 = lean_box(0);
}
x_380 = l_Lean_instQuoteBool___closed__1;
x_381 = lean_string_dec_eq(x_377, x_380);
lean_dec(x_377);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
lean_dec(x_376);
lean_dec(x_374);
lean_dec(x_372);
lean_dec(x_353);
lean_dec(x_2);
if (lean_is_scalar(x_379)) {
 x_382 = lean_alloc_ctor(1, 2, 8);
} else {
 x_382 = x_379;
}
lean_ctor_set(x_382, 0, x_371);
lean_ctor_set(x_382, 1, x_354);
lean_ctor_set_uint64(x_382, sizeof(void*)*2, x_352);
if (lean_is_scalar(x_350)) {
 x_383 = lean_alloc_ctor(4, 2, 8);
} else {
 x_383 = x_350;
}
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_348);
lean_ctor_set_uint64(x_383, sizeof(void*)*2, x_349);
x_384 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_346);
lean_ctor_set_uint64(x_384, sizeof(void*)*2, x_347);
if (lean_is_scalar(x_357)) {
 x_385 = lean_alloc_ctor(5, 2, 8);
} else {
 x_385 = x_357;
}
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_8);
lean_ctor_set_uint64(x_385, sizeof(void*)*2, x_345);
x_386 = lean_apply_1(x_3, x_385);
return x_386;
}
else
{
lean_object* x_387; lean_object* x_388; uint8_t x_389; 
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_387 = x_8;
} else {
 lean_dec_ref(x_8);
 x_387 = lean_box(0);
}
x_388 = l_instReprBool___closed__2;
x_389 = lean_string_dec_eq(x_374, x_388);
if (x_389 == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
lean_dec(x_2);
if (lean_is_scalar(x_379)) {
 x_390 = lean_alloc_ctor(1, 2, 8);
} else {
 x_390 = x_379;
}
lean_ctor_set(x_390, 0, x_371);
lean_ctor_set(x_390, 1, x_354);
lean_ctor_set_uint64(x_390, sizeof(void*)*2, x_352);
if (lean_is_scalar(x_387)) {
 x_391 = lean_alloc_ctor(4, 2, 8);
} else {
 x_391 = x_387;
}
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_348);
lean_ctor_set_uint64(x_391, sizeof(void*)*2, x_349);
if (lean_is_scalar(x_350)) {
 x_392 = lean_alloc_ctor(5, 2, 8);
} else {
 x_392 = x_350;
 lean_ctor_set_tag(x_392, 5);
}
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_392, 1, x_346);
lean_ctor_set_uint64(x_392, sizeof(void*)*2, x_347);
if (lean_is_scalar(x_376)) {
 x_393 = lean_alloc_ctor(1, 2, 8);
} else {
 x_393 = x_376;
}
lean_ctor_set(x_393, 0, x_371);
lean_ctor_set(x_393, 1, x_380);
lean_ctor_set_uint64(x_393, sizeof(void*)*2, x_378);
if (lean_is_scalar(x_353)) {
 x_394 = lean_alloc_ctor(1, 2, 8);
} else {
 x_394 = x_353;
}
lean_ctor_set(x_394, 0, x_393);
lean_ctor_set(x_394, 1, x_374);
lean_ctor_set_uint64(x_394, sizeof(void*)*2, x_375);
x_395 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_372);
lean_ctor_set_uint64(x_395, sizeof(void*)*2, x_373);
if (lean_is_scalar(x_357)) {
 x_396 = lean_alloc_ctor(5, 2, 8);
} else {
 x_396 = x_357;
}
lean_ctor_set(x_396, 0, x_392);
lean_ctor_set(x_396, 1, x_395);
lean_ctor_set_uint64(x_396, sizeof(void*)*2, x_345);
x_397 = lean_apply_1(x_3, x_396);
return x_397;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
lean_dec(x_387);
lean_dec(x_379);
lean_dec(x_376);
lean_dec(x_374);
lean_dec(x_357);
lean_dec(x_353);
lean_dec(x_350);
lean_dec(x_3);
x_398 = lean_box_uint64(x_349);
x_399 = lean_box_uint64(x_347);
x_400 = lean_box_uint64(x_373);
x_401 = lean_box_uint64(x_345);
x_402 = lean_box_uint64(x_352);
x_403 = lean_box_uint64(x_378);
x_404 = lean_box_uint64(x_375);
x_405 = lean_apply_10(x_2, x_348, x_398, x_346, x_399, x_372, x_400, x_401, x_402, x_403, x_404);
return x_405;
}
}
}
case 1:
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_dec(x_364);
lean_dec(x_358);
lean_dec(x_353);
lean_dec(x_2);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 x_406 = x_371;
} else {
 lean_dec_ref(x_371);
 x_406 = lean_box(0);
}
if (lean_is_scalar(x_406)) {
 x_407 = lean_alloc_ctor(1, 2, 8);
} else {
 x_407 = x_406;
}
lean_ctor_set(x_407, 0, x_7);
lean_ctor_set(x_407, 1, x_354);
lean_ctor_set_uint64(x_407, sizeof(void*)*2, x_352);
if (lean_is_scalar(x_350)) {
 x_408 = lean_alloc_ctor(4, 2, 8);
} else {
 x_408 = x_350;
}
lean_ctor_set(x_408, 0, x_407);
lean_ctor_set(x_408, 1, x_348);
lean_ctor_set_uint64(x_408, sizeof(void*)*2, x_349);
x_409 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_346);
lean_ctor_set_uint64(x_409, sizeof(void*)*2, x_347);
if (lean_is_scalar(x_357)) {
 x_410 = lean_alloc_ctor(5, 2, 8);
} else {
 x_410 = x_357;
}
lean_ctor_set(x_410, 0, x_409);
lean_ctor_set(x_410, 1, x_8);
lean_ctor_set_uint64(x_410, sizeof(void*)*2, x_345);
x_411 = lean_apply_1(x_3, x_410);
return x_411;
}
default: 
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
lean_dec(x_364);
lean_dec(x_358);
lean_dec(x_353);
lean_dec(x_2);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 x_412 = x_371;
} else {
 lean_dec_ref(x_371);
 x_412 = lean_box(0);
}
if (lean_is_scalar(x_412)) {
 x_413 = lean_alloc_ctor(1, 2, 8);
} else {
 x_413 = x_412;
 lean_ctor_set_tag(x_413, 1);
}
lean_ctor_set(x_413, 0, x_7);
lean_ctor_set(x_413, 1, x_354);
lean_ctor_set_uint64(x_413, sizeof(void*)*2, x_352);
if (lean_is_scalar(x_350)) {
 x_414 = lean_alloc_ctor(4, 2, 8);
} else {
 x_414 = x_350;
}
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_348);
lean_ctor_set_uint64(x_414, sizeof(void*)*2, x_349);
x_415 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_346);
lean_ctor_set_uint64(x_415, sizeof(void*)*2, x_347);
if (lean_is_scalar(x_357)) {
 x_416 = lean_alloc_ctor(5, 2, 8);
} else {
 x_416 = x_357;
}
lean_ctor_set(x_416, 0, x_415);
lean_ctor_set(x_416, 1, x_8);
lean_ctor_set_uint64(x_416, sizeof(void*)*2, x_345);
x_417 = lean_apply_1(x_3, x_416);
return x_417;
}
}
}
default: 
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec(x_358);
lean_dec(x_353);
lean_dec(x_2);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_418 = x_364;
} else {
 lean_dec_ref(x_364);
 x_418 = lean_box(0);
}
if (lean_is_scalar(x_418)) {
 x_419 = lean_alloc_ctor(1, 2, 8);
} else {
 x_419 = x_418;
 lean_ctor_set_tag(x_419, 1);
}
lean_ctor_set(x_419, 0, x_7);
lean_ctor_set(x_419, 1, x_354);
lean_ctor_set_uint64(x_419, sizeof(void*)*2, x_352);
if (lean_is_scalar(x_350)) {
 x_420 = lean_alloc_ctor(4, 2, 8);
} else {
 x_420 = x_350;
}
lean_ctor_set(x_420, 0, x_419);
lean_ctor_set(x_420, 1, x_348);
lean_ctor_set_uint64(x_420, sizeof(void*)*2, x_349);
x_421 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_346);
lean_ctor_set_uint64(x_421, sizeof(void*)*2, x_347);
if (lean_is_scalar(x_357)) {
 x_422 = lean_alloc_ctor(5, 2, 8);
} else {
 x_422 = x_357;
}
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_8);
lean_ctor_set_uint64(x_422, sizeof(void*)*2, x_345);
x_423 = lean_apply_1(x_3, x_422);
return x_423;
}
}
}
default: 
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
lean_dec(x_353);
lean_dec(x_2);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 x_424 = x_358;
} else {
 lean_dec_ref(x_358);
 x_424 = lean_box(0);
}
if (lean_is_scalar(x_424)) {
 x_425 = lean_alloc_ctor(1, 2, 8);
} else {
 x_425 = x_424;
 lean_ctor_set_tag(x_425, 1);
}
lean_ctor_set(x_425, 0, x_7);
lean_ctor_set(x_425, 1, x_354);
lean_ctor_set_uint64(x_425, sizeof(void*)*2, x_352);
if (lean_is_scalar(x_350)) {
 x_426 = lean_alloc_ctor(4, 2, 8);
} else {
 x_426 = x_350;
}
lean_ctor_set(x_426, 0, x_425);
lean_ctor_set(x_426, 1, x_348);
lean_ctor_set_uint64(x_426, sizeof(void*)*2, x_349);
x_427 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_427, 0, x_426);
lean_ctor_set(x_427, 1, x_346);
lean_ctor_set_uint64(x_427, sizeof(void*)*2, x_347);
if (lean_is_scalar(x_357)) {
 x_428 = lean_alloc_ctor(5, 2, 8);
} else {
 x_428 = x_357;
}
lean_ctor_set(x_428, 0, x_427);
lean_ctor_set(x_428, 1, x_8);
lean_ctor_set_uint64(x_428, sizeof(void*)*2, x_345);
x_429 = lean_apply_1(x_3, x_428);
return x_429;
}
}
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
lean_dec(x_2);
if (lean_is_scalar(x_353)) {
 x_430 = lean_alloc_ctor(1, 2, 8);
} else {
 x_430 = x_353;
}
lean_ctor_set(x_430, 0, x_7);
lean_ctor_set(x_430, 1, x_354);
lean_ctor_set_uint64(x_430, sizeof(void*)*2, x_352);
if (lean_is_scalar(x_350)) {
 x_431 = lean_alloc_ctor(4, 2, 8);
} else {
 x_431 = x_350;
}
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_348);
lean_ctor_set_uint64(x_431, sizeof(void*)*2, x_349);
x_432 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_432, 0, x_431);
lean_ctor_set(x_432, 1, x_346);
lean_ctor_set_uint64(x_432, sizeof(void*)*2, x_347);
if (lean_is_scalar(x_357)) {
 x_433 = lean_alloc_ctor(5, 2, 8);
} else {
 x_433 = x_357;
}
lean_ctor_set(x_433, 0, x_432);
lean_ctor_set(x_433, 1, x_8);
lean_ctor_set_uint64(x_433, sizeof(void*)*2, x_345);
x_434 = lean_apply_1(x_3, x_433);
return x_434;
}
}
}
}
else
{
lean_object* x_435; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_435 = lean_apply_1(x_3, x_1);
return x_435;
}
}
else
{
lean_object* x_436; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_436 = lean_apply_1(x_3, x_1);
return x_436;
}
}
else
{
lean_object* x_437; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_437 = lean_apply_1(x_3, x_1);
return x_437;
}
}
else
{
lean_object* x_438; 
lean_dec(x_4);
lean_dec(x_2);
x_438 = lean_apply_1(x_3, x_1);
return x_438;
}
}
else
{
lean_object* x_439; 
lean_dec(x_2);
x_439 = lean_apply_1(x_3, x_1);
return x_439;
}
}
}
lean_object* l_Lean_Expr_isSyntheticSorry_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_isSyntheticSorry_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Expr_isSyntheticSorry(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lean_Expr_isSorry_match__1___rarg___closed__1;
x_9 = lean_string_dec_eq(x_7, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
else
{
if (lean_obj_tag(x_6) == 4)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_instQuoteBool___closed__1;
x_17 = lean_string_dec_eq(x_15, x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_instReprBool___closed__2;
x_20 = lean_string_dec_eq(x_14, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = 0;
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = 0;
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = 0;
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = 0;
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = 0;
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = 0;
return x_29;
}
}
}
lean_object* l_Lean_Expr_isSyntheticSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isSyntheticSorry(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_hasSorry_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_13 = lean_box_uint64(x_12);
x_14 = lean_apply_3(x_2, x_10, x_11, x_13);
return x_14;
}
case 5:
{
lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_18 = lean_box_uint64(x_17);
x_19 = lean_apply_3(x_3, x_15, x_16, x_18);
return x_19;
}
case 6:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
x_23 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_24 = lean_box_uint64(x_23);
x_25 = lean_apply_4(x_6, x_20, x_21, x_22, x_24);
return x_25;
}
case 7:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
x_29 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_30 = lean_box_uint64(x_29);
x_31 = lean_apply_4(x_5, x_26, x_27, x_28, x_30);
return x_31;
}
case 8:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint64_t x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 3);
lean_inc(x_35);
x_36 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_37 = lean_box_uint64(x_36);
x_38 = lean_apply_5(x_4, x_32, x_33, x_34, x_35, x_37);
return x_38;
}
case 10:
{
lean_object* x_39; lean_object* x_40; uint64_t x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
x_41 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_42 = lean_box_uint64(x_41);
x_43 = lean_apply_3(x_7, x_39, x_40, x_42);
return x_43;
}
case 11:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint64_t x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 2);
lean_inc(x_46);
x_47 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_48 = lean_box_uint64(x_47);
x_49 = lean_apply_4(x_8, x_44, x_45, x_46, x_48);
return x_49;
}
default: 
{
lean_object* x_50; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = lean_apply_1(x_9, x_1);
return x_50;
}
}
}
}
lean_object* l_Lean_Expr_hasSorry_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_hasSorry_match__1___rarg), 9, 0);
return x_2;
}
}
#define _init_l_Lean_Expr_hasSorry___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l_Lean_Expr_isSorry_match__1___rarg___closed__1;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_Expr_hasSorry___closed__1_end;\
}\
l_Lean_Expr_hasSorry___closed__1_end: ((void) 0);}
uint8_t l_Lean_Expr_hasSorry(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_Expr_hasSorry___closed__1;
x_4 = lean_name_eq(x_2, x_3);
return x_4;
}
case 5:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Expr_hasSorry(x_5);
if (x_7 == 0)
{
x_1 = x_6;
goto _start;
}
else
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
}
case 6:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = l_Lean_Expr_hasSorry(x_10);
if (x_12 == 0)
{
x_1 = x_11;
goto _start;
}
else
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
}
case 7:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 2);
x_17 = l_Lean_Expr_hasSorry(x_15);
if (x_17 == 0)
{
x_1 = x_16;
goto _start;
}
else
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
}
case 8:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 3);
x_23 = l_Lean_Expr_hasSorry(x_20);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Expr_hasSorry(x_21);
if (x_24 == 0)
{
x_1 = x_22;
goto _start;
}
else
{
uint8_t x_26; 
x_26 = 1;
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = 1;
return x_27;
}
}
case 10:
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_1, 1);
x_1 = x_28;
goto _start;
}
case 11:
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_1, 2);
x_1 = x_30;
goto _start;
}
default: 
{
uint8_t x_32; 
x_32 = 0;
return x_32;
}
}
}
}
lean_object* l_Lean_Expr_hasSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasSorry(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_hasSyntheticSorry_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_12 = lean_box_uint64(x_11);
x_13 = lean_apply_4(x_2, x_1, x_9, x_10, x_12);
return x_13;
}
case 6:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_18 = lean_box_uint64(x_17);
x_19 = lean_apply_4(x_5, x_14, x_15, x_16, x_18);
return x_19;
}
case 7:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
x_23 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_24 = lean_box_uint64(x_23);
x_25 = lean_apply_4(x_4, x_20, x_21, x_22, x_24);
return x_25;
}
case 8:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 3);
lean_inc(x_29);
x_30 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_31 = lean_box_uint64(x_30);
x_32 = lean_apply_5(x_3, x_26, x_27, x_28, x_29, x_31);
return x_32;
}
case 10:
{
lean_object* x_33; lean_object* x_34; uint64_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_36 = lean_box_uint64(x_35);
x_37 = lean_apply_3(x_6, x_33, x_34, x_36);
return x_37;
}
case 11:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint64_t x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 2);
lean_inc(x_40);
x_41 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_42 = lean_box_uint64(x_41);
x_43 = lean_apply_4(x_7, x_38, x_39, x_40, x_42);
return x_43;
}
default: 
{
lean_object* x_44; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_apply_1(x_8, x_1);
return x_44;
}
}
}
}
lean_object* l_Lean_Expr_hasSyntheticSorry_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_hasSyntheticSorry_match__1___rarg), 8, 0);
return x_2;
}
}
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_Expr_isSyntheticSorry(x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_Expr_hasSyntheticSorry(x_2);
if (x_5 == 0)
{
x_1 = x_3;
goto _start;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
case 6:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = l_Lean_Expr_hasSyntheticSorry(x_9);
if (x_11 == 0)
{
x_1 = x_10;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
}
case 7:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
x_16 = l_Lean_Expr_hasSyntheticSorry(x_14);
if (x_16 == 0)
{
x_1 = x_15;
goto _start;
}
else
{
uint8_t x_18; 
x_18 = 1;
return x_18;
}
}
case 8:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_1, 2);
x_21 = lean_ctor_get(x_1, 3);
x_22 = l_Lean_Expr_hasSyntheticSorry(x_19);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = l_Lean_Expr_hasSyntheticSorry(x_20);
if (x_23 == 0)
{
x_1 = x_21;
goto _start;
}
else
{
uint8_t x_25; 
x_25 = 1;
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = 1;
return x_26;
}
}
case 10:
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_1, 1);
x_1 = x_27;
goto _start;
}
case 11:
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_1, 2);
x_1 = x_29;
goto _start;
}
default: 
{
uint8_t x_31; 
x_31 = 0;
return x_31;
}
}
}
}
lean_object* l_Lean_Expr_hasSyntheticSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasSyntheticSorry(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_MessageData_hasSorry_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_2, x_10);
return x_11;
}
case 6:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_apply_2(x_3, x_12, x_13);
return x_14;
}
case 8:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_apply_2(x_4, x_15, x_16);
return x_17;
}
case 9:
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_apply_1(x_5, x_18);
return x_19;
}
case 10:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_apply_2(x_6, x_20, x_21);
return x_22;
}
case 11:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_apply_2(x_7, x_23, x_24);
return x_25;
}
case 12:
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_apply_1(x_8, x_26);
return x_27;
}
default: 
{
lean_object* x_28; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_apply_1(x_9, x_1);
return x_28;
}
}
}
}
lean_object* l_Lean_MessageData_hasSorry_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MessageData_hasSorry_match__1___rarg), 9, 0);
return x_2;
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSorry___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 == x_3;
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_MessageData_hasSorry(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = x_2 + x_7;
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
uint8_t l_Lean_MessageData_hasSorry(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_Expr_hasSorry(x_2);
return x_3;
}
case 6:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
x_1 = x_4;
goto _start;
}
case 8:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 1);
x_1 = x_6;
goto _start;
}
case 9:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 0);
x_1 = x_8;
goto _start;
}
case 10:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = l_Lean_MessageData_hasSorry(x_10);
if (x_12 == 0)
{
x_1 = x_11;
goto _start;
}
else
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
}
case 11:
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_1, 1);
x_1 = x_15;
goto _start;
}
case 12:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_array_get_size(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_18);
x_21 = 0;
return x_21;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_18, x_18);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_18);
x_23 = 0;
return x_23;
}
else
{
size_t x_24; size_t x_25; uint8_t x_26; 
x_24 = 0;
x_25 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_26 = l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSorry___spec__1(x_17, x_24, x_25);
return x_26;
}
}
}
default: 
{
uint8_t x_27; 
x_27 = 0;
return x_27;
}
}
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSorry___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSorry___spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_MessageData_hasSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_hasSorry(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_MessageData_hasSyntheticSorry_visit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_1(x_2, x_11);
return x_12;
}
case 6:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_2(x_3, x_13, x_14);
return x_15;
}
case 7:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_apply_2(x_4, x_16, x_17);
return x_18;
}
case 8:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_apply_2(x_5, x_19, x_20);
return x_21;
}
case 9:
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_apply_1(x_6, x_22);
return x_23;
}
case 10:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_apply_2(x_7, x_24, x_25);
return x_26;
}
case 11:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_apply_2(x_8, x_27, x_28);
return x_29;
}
case 12:
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
lean_dec(x_1);
x_31 = lean_apply_1(x_9, x_30);
return x_31;
}
default: 
{
lean_object* x_32; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_apply_1(x_10, x_1);
return x_32;
}
}
}
}
lean_object* l_Lean_MessageData_hasSyntheticSorry_visit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MessageData_hasSyntheticSorry_visit_match__1___rarg), 10, 0);
return x_2;
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSyntheticSorry_visit___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 == x_3;
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_MessageData_hasSyntheticSorry(x_5);
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = x_2 + x_7;
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
uint8_t l_Lean_MessageData_hasSyntheticSorry_visit(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_Expr_hasSyntheticSorry(x_2);
return x_3;
}
case 6:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
x_1 = x_4;
goto _start;
}
case 7:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 1);
x_1 = x_6;
goto _start;
}
case 8:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 1);
x_1 = x_8;
goto _start;
}
case 9:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 0);
x_1 = x_10;
goto _start;
}
case 10:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = l_Lean_MessageData_hasSyntheticSorry_visit(x_12);
if (x_14 == 0)
{
x_1 = x_13;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
case 11:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_1, 1);
x_1 = x_17;
goto _start;
}
case 12:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_array_get_size(x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_lt(x_21, x_20);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_20);
x_23 = 0;
return x_23;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_20, x_20);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_20);
x_25 = 0;
return x_25;
}
else
{
size_t x_26; size_t x_27; uint8_t x_28; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_28 = l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSyntheticSorry_visit___spec__1(x_19, x_26, x_27);
return x_28;
}
}
}
default: 
{
uint8_t x_29; 
x_29 = 0;
return x_29;
}
}
}
}
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_MessageData_instantiateMVars(x_1);
x_3 = l_Lean_MessageData_hasSyntheticSorry_visit(x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSyntheticSorry_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSyntheticSorry_visit___spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_MessageData_hasSyntheticSorry_visit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_hasSyntheticSorry_visit(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_MessageData_hasSyntheticSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_hasSyntheticSorry(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Exception_hasSyntheticSorry_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Exception_hasSyntheticSorry_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Exception_hasSyntheticSorry_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Exception_hasSyntheticSorry(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_MessageData_hasSyntheticSorry(x_2);
return x_3;
}
else
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = 0;
return x_4;
}
}
}
lean_object* l_Lean_Exception_hasSyntheticSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Exception_hasSyntheticSorry(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Message(lean_object*);
lean_object* initialize_Lean_Exception(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Util_Sorry(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Message(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Exception(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
_init_l_Lean_Expr_isSorry_match__1___rarg___closed__1(l_Lean_Expr_isSorry_match__1___rarg___closed__1);
lean_mark_persistent(l_Lean_Expr_isSorry_match__1___rarg___closed__1);
_init_l_Lean_Expr_hasSorry___closed__1(l_Lean_Expr_hasSorry___closed__1);
lean_mark_persistent(l_Lean_Expr_hasSorry___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
