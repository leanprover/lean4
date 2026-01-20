// Lean compiler output
// Module: Lean.Compiler.IR.AddExtern
// Imports: public import Lean.Compiler.IR.Boxing import Lean.Compiler.IR.RC
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_IR_addExtern___closed__6;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_IR_addDecls(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_addExtern___closed__5;
LEAN_EXPORT lean_object* l_Lean_IR_addExtern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_addExtern___closed__3;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_addExtern___closed__1;
uint8_t l_Lean_isMarkedBorrowed(lean_object*);
LEAN_EXPORT lean_object* lean_add_extern(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
static lean_object* l_Lean_IR_addExtern___closed__2;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_IR_toIRType(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_addExtern___closed__4;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_IR_addExtern_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_addExtern___closed__0;
extern lean_object* l_Lean_IR_tracePrefixOptionName;
lean_object* l_Lean_IR_explicitRC___redArg(lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_addBoxedVersions(lean_object*, lean_object*);
static lean_object* l_Lean_IR_addExtern___closed__7;
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_IR_addExtern_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_setDeclPublic(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_IR_addExtern_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 7)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_14);
lean_dec_ref(x_6);
x_15 = l_Lean_isMarkedBorrowed(x_13);
lean_inc(x_3);
lean_inc_ref(x_2);
x_16 = l_Lean_IR_toIRType(x_13, x_2, x_3);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
lean_inc(x_8);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_15);
x_19 = lean_array_push(x_11, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_8, x_20);
lean_dec(x_8);
lean_ctor_set(x_5, 1, x_14);
lean_ctor_set(x_5, 0, x_19);
lean_ctor_set(x_1, 0, x_21);
goto _start;
}
else
{
uint8_t x_23; 
lean_dec_ref(x_14);
lean_free_object(x_5);
lean_dec(x_11);
lean_free_object(x_1);
lean_dec(x_8);
lean_dec(x_3);
lean_dec_ref(x_2);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
lean_dec(x_5);
x_27 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_28);
lean_dec_ref(x_6);
x_29 = l_Lean_isMarkedBorrowed(x_27);
lean_inc(x_3);
lean_inc_ref(x_2);
x_30 = l_Lean_IR_toIRType(x_27, x_2, x_3);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
lean_inc(x_8);
x_32 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_32, 0, x_8);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_29);
x_33 = lean_array_push(x_26, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_8, x_34);
lean_dec(x_8);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_28);
lean_ctor_set(x_1, 1, x_36);
lean_ctor_set(x_1, 0, x_35);
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec_ref(x_28);
lean_dec(x_26);
lean_free_object(x_1);
lean_dec(x_8);
lean_dec(x_3);
lean_dec_ref(x_2);
x_38 = lean_ctor_get(x_30, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_39 = x_30;
} else {
 lean_dec_ref(x_30);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 1, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_38);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
lean_dec(x_1);
x_42 = lean_ctor_get(x_5, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_43 = x_5;
} else {
 lean_dec_ref(x_5);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_45);
lean_dec_ref(x_6);
x_46 = l_Lean_isMarkedBorrowed(x_44);
lean_inc(x_3);
lean_inc_ref(x_2);
x_47 = l_Lean_IR_toIRType(x_44, x_2, x_3);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
lean_inc(x_41);
x_49 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_46);
x_50 = lean_array_push(x_42, x_49);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_41, x_51);
lean_dec(x_41);
if (lean_is_scalar(x_43)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_43;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_45);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_1 = x_54;
goto _start;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec_ref(x_45);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_3);
lean_dec_ref(x_2);
x_56 = lean_ctor_get(x_47, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_57 = x_47;
} else {
 lean_dec_ref(x_47);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_56);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_59 = !lean_is_exclusive(x_1);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_1, 1);
lean_dec(x_60);
x_61 = !lean_is_exclusive(x_5);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_5, 1);
lean_dec(x_62);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_1);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_5, 0);
lean_inc(x_64);
lean_dec(x_5);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_6);
lean_ctor_set(x_1, 1, x_65);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_1);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_1, 0);
lean_inc(x_67);
lean_dec(x_1);
x_68 = lean_ctor_get(x_5, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_69 = x_5;
} else {
 lean_dec_ref(x_5);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_6);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_IR_addExtern_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_IR_addExtern_spec__0(x_1, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_addExtern___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_addExtern___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_addExtern___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("result", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_addExtern___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_addExtern___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_addExtern___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_addExtern___closed__3;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_addExtern___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_IR_addExtern___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_addExtern___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_addExtern___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_addExtern___closed__6;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_add_extern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_1);
x_6 = l_Lean_Compiler_LCNF_getOtherDeclMonoType(x_1, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_IR_addExtern___closed__0;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
lean_inc(x_4);
lean_inc_ref(x_3);
x_12 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_IR_addExtern_spec__0(x_11, x_3, x_4);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_4);
lean_inc_ref(x_3);
x_17 = l_Lean_IR_toIRType(x_16, x_3, x_4);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_38; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
lean_inc(x_1);
x_19 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_19, 3, x_2);
x_20 = l_Lean_IR_addExtern___closed__1;
x_21 = lean_array_push(x_20, x_19);
x_38 = l_Lean_isPrivateName(x_1);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_st_ref_take(x_4);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 5);
lean_dec(x_42);
x_43 = l_Lean_Compiler_LCNF_setDeclPublic(x_41, x_1);
x_44 = l_Lean_IR_addExtern___closed__7;
lean_ctor_set(x_39, 5, x_44);
lean_ctor_set(x_39, 0, x_43);
x_45 = lean_st_ref_set(x_4, x_39);
x_22 = x_3;
x_23 = x_4;
x_24 = lean_box(0);
goto block_37;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_46 = lean_ctor_get(x_39, 0);
x_47 = lean_ctor_get(x_39, 1);
x_48 = lean_ctor_get(x_39, 2);
x_49 = lean_ctor_get(x_39, 3);
x_50 = lean_ctor_get(x_39, 4);
x_51 = lean_ctor_get(x_39, 6);
x_52 = lean_ctor_get(x_39, 7);
x_53 = lean_ctor_get(x_39, 8);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_39);
x_54 = l_Lean_Compiler_LCNF_setDeclPublic(x_46, x_1);
x_55 = l_Lean_IR_addExtern___closed__7;
x_56 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_47);
lean_ctor_set(x_56, 2, x_48);
lean_ctor_set(x_56, 3, x_49);
lean_ctor_set(x_56, 4, x_50);
lean_ctor_set(x_56, 5, x_55);
lean_ctor_set(x_56, 6, x_51);
lean_ctor_set(x_56, 7, x_52);
lean_ctor_set(x_56, 8, x_53);
x_57 = lean_st_ref_set(x_4, x_56);
x_22 = x_3;
x_23 = x_4;
x_24 = lean_box(0);
goto block_37;
}
}
else
{
lean_dec(x_1);
x_22 = x_3;
x_23 = x_4;
x_24 = lean_box(0);
goto block_37;
}
block_37:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_st_ref_get(x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_26);
lean_dec(x_25);
x_27 = l_Lean_IR_ExplicitBoxing_addBoxedVersions(x_26, x_21);
x_28 = l_Lean_IR_explicitRC___redArg(x_27, x_23);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = l_Lean_IR_addExtern___closed__3;
x_31 = l_Lean_IR_addExtern___closed__4;
lean_inc(x_29);
x_32 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_31, x_30, x_29, x_22, x_23);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_dec_ref(x_32);
x_33 = l_Lean_IR_addDecls(x_29, x_22, x_23);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_29);
return x_33;
}
else
{
lean_dec(x_29);
lean_dec(x_23);
lean_dec_ref(x_22);
return x_32;
}
}
else
{
uint8_t x_34; 
lean_dec(x_23);
lean_dec_ref(x_22);
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
return x_28;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_28, 0);
lean_inc(x_35);
lean_dec(x_28);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_15);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_17);
if (x_58 == 0)
{
return x_17;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_17, 0);
lean_inc(x_59);
lean_dec(x_17);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_12);
if (x_61 == 0)
{
return x_12;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_12, 0);
lean_inc(x_62);
lean_dec(x_12);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_6);
if (x_64 == 0)
{
return x_6;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_6, 0);
lean_inc(x_65);
lean_dec(x_6);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addExtern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_add_extern(x_1, x_2, x_3, x_4);
return x_6;
}
}
lean_object* initialize_Lean_Compiler_IR_Boxing(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_RC(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_AddExtern(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_Boxing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_RC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_addExtern___closed__0 = _init_l_Lean_IR_addExtern___closed__0();
lean_mark_persistent(l_Lean_IR_addExtern___closed__0);
l_Lean_IR_addExtern___closed__1 = _init_l_Lean_IR_addExtern___closed__1();
lean_mark_persistent(l_Lean_IR_addExtern___closed__1);
l_Lean_IR_addExtern___closed__2 = _init_l_Lean_IR_addExtern___closed__2();
lean_mark_persistent(l_Lean_IR_addExtern___closed__2);
l_Lean_IR_addExtern___closed__3 = _init_l_Lean_IR_addExtern___closed__3();
lean_mark_persistent(l_Lean_IR_addExtern___closed__3);
l_Lean_IR_addExtern___closed__4 = _init_l_Lean_IR_addExtern___closed__4();
lean_mark_persistent(l_Lean_IR_addExtern___closed__4);
l_Lean_IR_addExtern___closed__5 = _init_l_Lean_IR_addExtern___closed__5();
lean_mark_persistent(l_Lean_IR_addExtern___closed__5);
l_Lean_IR_addExtern___closed__6 = _init_l_Lean_IR_addExtern___closed__6();
lean_mark_persistent(l_Lean_IR_addExtern___closed__6);
l_Lean_IR_addExtern___closed__7 = _init_l_Lean_IR_addExtern___closed__7();
lean_mark_persistent(l_Lean_IR_addExtern___closed__7);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
