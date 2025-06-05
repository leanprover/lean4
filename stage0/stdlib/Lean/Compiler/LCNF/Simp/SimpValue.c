// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.SimpValue
// Imports: Lean.Compiler.LCNF.Simp.SimpM
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
static lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Arg_toLetValue(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedArg;
lean_object* l_Lean_Compiler_LCNF_LetValue_toExpr(lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___closed__2;
lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
extern lean_object* l_Lean_instInhabitedName;
lean_object* l_Lean_Compiler_LCNF_Simp_findCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_implementedByAttr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_Compiler_LCNF_Simp_findCtor_x3f(x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_10);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_13, 0);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_12, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_ctor_get(x_24, 3);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_nat_add(x_26, x_10);
lean_dec(x_10);
lean_dec(x_26);
x_28 = l_Lean_Compiler_LCNF_instInhabitedArg;
x_29 = lean_array_get(x_28, x_25, x_27);
lean_dec(x_27);
lean_dec(x_25);
x_30 = l_Lean_Compiler_LCNF_Arg_toLetValue(x_29);
lean_dec(x_29);
lean_ctor_set(x_13, 0, x_30);
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
lean_dec(x_12);
x_32 = lean_ctor_get(x_21, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_dec(x_21);
x_34 = lean_ctor_get(x_32, 3);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_nat_add(x_34, x_10);
lean_dec(x_10);
lean_dec(x_34);
x_36 = l_Lean_Compiler_LCNF_instInhabitedArg;
x_37 = lean_array_get(x_36, x_33, x_35);
lean_dec(x_35);
lean_dec(x_33);
x_38 = l_Lean_Compiler_LCNF_Arg_toLetValue(x_37);
lean_dec(x_37);
lean_ctor_set(x_13, 0, x_38);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_13);
lean_ctor_set(x_39, 1, x_31);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_free_object(x_13);
lean_dec(x_21);
lean_dec(x_10);
x_40 = !lean_is_exclusive(x_12);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_12, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set(x_12, 0, x_42);
return x_12;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_12, 1);
lean_inc(x_43);
lean_dec(x_12);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_13, 0);
lean_inc(x_46);
lean_dec(x_13);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_47 = lean_ctor_get(x_12, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_48 = x_12;
} else {
 lean_dec_ref(x_12);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_ctor_get(x_49, 3);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_nat_add(x_51, x_10);
lean_dec(x_10);
lean_dec(x_51);
x_53 = l_Lean_Compiler_LCNF_instInhabitedArg;
x_54 = lean_array_get(x_53, x_50, x_52);
lean_dec(x_52);
lean_dec(x_50);
x_55 = l_Lean_Compiler_LCNF_Arg_toLetValue(x_54);
lean_dec(x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
if (lean_is_scalar(x_48)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_48;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_47);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_46);
lean_dec(x_10);
x_58 = lean_ctor_get(x_12, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_59 = x_12;
} else {
 lean_dec_ref(x_12);
 x_59 = lean_box(0);
}
x_60 = lean_box(0);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
}
}
}
case 4:
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_1);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_1, 1);
lean_dec(x_63);
x_64 = lean_ctor_get(x_1, 0);
lean_dec(x_64);
x_65 = lean_box(0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_65);
return x_1;
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_1);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_9);
return x_67;
}
}
default: 
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_1);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_9);
return x_69;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_simpProj_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = l_Lean_Compiler_LCNF_findLetDecl_x3f(x_10, x_5, x_6, x_7, x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_21, 3);
lean_inc(x_22);
lean_dec(x_21);
switch (lean_obj_tag(x_22)) {
case 1:
{
uint8_t x_23; 
lean_free_object(x_13);
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_12, 0);
lean_dec(x_24);
x_25 = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1;
lean_ctor_set(x_12, 0, x_25);
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_dec(x_12);
x_27 = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
case 3:
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_12);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_12, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_22, 1);
x_34 = lean_ctor_get(x_22, 2);
x_35 = l_Array_isEmpty___rarg(x_11);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Array_append___rarg(x_34, x_11);
lean_ctor_set(x_22, 2, x_36);
lean_ctor_set(x_13, 0, x_22);
return x_12;
}
else
{
lean_object* x_37; 
lean_free_object(x_22);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_free_object(x_13);
x_37 = lean_box(0);
lean_ctor_set(x_12, 0, x_37);
return x_12;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_22, 0);
x_39 = lean_ctor_get(x_22, 1);
x_40 = lean_ctor_get(x_22, 2);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_22);
x_41 = l_Array_isEmpty___rarg(x_11);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = l_Array_append___rarg(x_40, x_11);
x_43 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_39);
lean_ctor_set(x_43, 2, x_42);
lean_ctor_set(x_13, 0, x_43);
return x_12;
}
else
{
lean_object* x_44; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_free_object(x_13);
x_44 = lean_box(0);
lean_ctor_set(x_12, 0, x_44);
return x_12;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_45 = lean_ctor_get(x_12, 1);
lean_inc(x_45);
lean_dec(x_12);
x_46 = lean_ctor_get(x_22, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_22, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_22, 2);
lean_inc(x_48);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 x_49 = x_22;
} else {
 lean_dec_ref(x_22);
 x_49 = lean_box(0);
}
x_50 = l_Array_isEmpty___rarg(x_11);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = l_Array_append___rarg(x_48, x_11);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(3, 3, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_47);
lean_ctor_set(x_52, 2, x_51);
lean_ctor_set(x_13, 0, x_52);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_13);
lean_ctor_set(x_53, 1, x_45);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_free_object(x_13);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_45);
return x_55;
}
}
}
case 4:
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_12);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_12, 0);
lean_dec(x_57);
x_58 = !lean_is_exclusive(x_22);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_22, 0);
x_60 = lean_ctor_get(x_22, 1);
x_61 = l_Array_isEmpty___rarg(x_11);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = l_Array_append___rarg(x_60, x_11);
lean_ctor_set(x_22, 1, x_62);
lean_ctor_set(x_13, 0, x_22);
return x_12;
}
else
{
lean_object* x_63; 
lean_free_object(x_22);
lean_dec(x_60);
lean_dec(x_59);
lean_free_object(x_13);
x_63 = lean_box(0);
lean_ctor_set(x_12, 0, x_63);
return x_12;
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_22, 0);
x_65 = lean_ctor_get(x_22, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_22);
x_66 = l_Array_isEmpty___rarg(x_11);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Array_append___rarg(x_65, x_11);
x_68 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_68, 0, x_64);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_13, 0, x_68);
return x_12;
}
else
{
lean_object* x_69; 
lean_dec(x_65);
lean_dec(x_64);
lean_free_object(x_13);
x_69 = lean_box(0);
lean_ctor_set(x_12, 0, x_69);
return x_12;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_70 = lean_ctor_get(x_12, 1);
lean_inc(x_70);
lean_dec(x_12);
x_71 = lean_ctor_get(x_22, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_22, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_73 = x_22;
} else {
 lean_dec_ref(x_22);
 x_73 = lean_box(0);
}
x_74 = l_Array_isEmpty___rarg(x_11);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = l_Array_append___rarg(x_72, x_11);
if (lean_is_scalar(x_73)) {
 x_76 = lean_alloc_ctor(4, 2, 0);
} else {
 x_76 = x_73;
}
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_13, 0, x_76);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_13);
lean_ctor_set(x_77, 1, x_70);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_free_object(x_13);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_70);
return x_79;
}
}
}
default: 
{
uint8_t x_80; 
lean_dec(x_22);
lean_free_object(x_13);
x_80 = !lean_is_exclusive(x_12);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_12, 0);
lean_dec(x_81);
x_82 = lean_box(0);
lean_ctor_set(x_12, 0, x_82);
return x_12;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_12, 1);
lean_inc(x_83);
lean_dec(x_12);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_13, 0);
lean_inc(x_86);
lean_dec(x_13);
x_87 = lean_ctor_get(x_86, 3);
lean_inc(x_87);
lean_dec(x_86);
switch (lean_obj_tag(x_87)) {
case 1:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_12, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_89 = x_12;
} else {
 lean_dec_ref(x_12);
 x_89 = lean_box(0);
}
x_90 = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1;
if (lean_is_scalar(x_89)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_89;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_88);
return x_91;
}
case 3:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_92 = lean_ctor_get(x_12, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_93 = x_12;
} else {
 lean_dec_ref(x_12);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_87, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_87, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_87, 2);
lean_inc(x_96);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 lean_ctor_release(x_87, 2);
 x_97 = x_87;
} else {
 lean_dec_ref(x_87);
 x_97 = lean_box(0);
}
x_98 = l_Array_isEmpty___rarg(x_11);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = l_Array_append___rarg(x_96, x_11);
if (lean_is_scalar(x_97)) {
 x_100 = lean_alloc_ctor(3, 3, 0);
} else {
 x_100 = x_97;
}
lean_ctor_set(x_100, 0, x_94);
lean_ctor_set(x_100, 1, x_95);
lean_ctor_set(x_100, 2, x_99);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
if (lean_is_scalar(x_93)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_93;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_92);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
x_103 = lean_box(0);
if (lean_is_scalar(x_93)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_93;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_92);
return x_104;
}
}
case 4:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_105 = lean_ctor_get(x_12, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_106 = x_12;
} else {
 lean_dec_ref(x_12);
 x_106 = lean_box(0);
}
x_107 = lean_ctor_get(x_87, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_87, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_109 = x_87;
} else {
 lean_dec_ref(x_87);
 x_109 = lean_box(0);
}
x_110 = l_Array_isEmpty___rarg(x_11);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = l_Array_append___rarg(x_108, x_11);
if (lean_is_scalar(x_109)) {
 x_112 = lean_alloc_ctor(4, 2, 0);
} else {
 x_112 = x_109;
}
lean_ctor_set(x_112, 0, x_107);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
if (lean_is_scalar(x_106)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_106;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_105);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
x_115 = lean_box(0);
if (lean_is_scalar(x_106)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_106;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_105);
return x_116;
}
}
default: 
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_87);
x_117 = lean_ctor_get(x_12, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_118 = x_12;
} else {
 lean_dec_ref(x_12);
 x_118 = lean_box(0);
}
x_119 = lean_box(0);
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_117);
return x_120;
}
}
}
}
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_box(0);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_9);
return x_122;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_st_ref_get(x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 0;
x_17 = l_Lean_Environment_find_x3f(x_15, x_10, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_18 = lean_box(0);
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
if (lean_obj_tag(x_19) == 6)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_19);
lean_free_object(x_11);
x_20 = l_Lean_Compiler_LCNF_LetValue_toExpr(x_1);
x_21 = l_Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f(x_20, x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_21, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___closed__1;
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_22, 0, x_34);
return x_21;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_22, 0);
lean_inc(x_35);
lean_dec(x_22);
x_36 = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___closed__1;
x_37 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_21, 0, x_38);
return x_21;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_21, 1);
lean_inc(x_39);
lean_dec(x_21);
x_40 = lean_ctor_get(x_22, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_41 = x_22;
} else {
 lean_dec_ref(x_22);
 x_41 = lean_box(0);
}
x_42 = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___closed__1;
x_43 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(1, 1, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_39);
return x_45;
}
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_21);
if (x_46 == 0)
{
return x_21;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_21, 0);
x_48 = lean_ctor_get(x_21, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_21);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_50 = lean_box(0);
lean_ctor_set(x_11, 0, x_50);
return x_11;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_11, 0);
x_52 = lean_ctor_get(x_11, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_11);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_dec(x_51);
x_54 = 0;
x_55 = l_Lean_Environment_find_x3f(x_53, x_10, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_52);
return x_57;
}
else
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
lean_dec(x_55);
if (lean_obj_tag(x_58) == 6)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_58);
x_59 = l_Lean_Compiler_LCNF_LetValue_toExpr(x_1);
x_60 = l_Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f(x_59, x_4, x_5, x_6, x_7, x_8, x_52);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_64 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_67 = x_60;
} else {
 lean_dec_ref(x_60);
 x_67 = lean_box(0);
}
x_68 = lean_ctor_get(x_61, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_69 = x_61;
} else {
 lean_dec_ref(x_61);
 x_69 = lean_box(0);
}
x_70 = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___closed__1;
x_71 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(1, 1, 0);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_71);
if (lean_is_scalar(x_67)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_67;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_66);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_60, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_60, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_76 = x_60;
} else {
 lean_dec_ref(x_60);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_58);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_52);
return x_79;
}
}
}
}
case 4:
{
uint8_t x_80; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_80 = !lean_is_exclusive(x_1);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_1, 1);
lean_dec(x_81);
x_82 = lean_ctor_get(x_1, 0);
lean_dec(x_82);
x_83 = lean_box(0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_83);
return x_1;
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_1);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_9);
return x_85;
}
}
default: 
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_9);
return x_87;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_implementedByAttr;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get_uint8(x_10, 2);
if (x_11 == 0)
{
lean_object* x_65; 
x_65 = lean_box(0);
x_12 = x_65;
x_13 = x_9;
goto block_64;
}
else
{
lean_object* x_66; 
x_66 = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___closed__2;
x_12 = x_66;
x_13 = x_9;
goto block_64;
}
block_64:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_dec(x_12);
if (lean_obj_tag(x_1) == 3)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
x_19 = lean_ctor_get(x_1, 2);
x_20 = lean_st_ref_get(x_8, x_13);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_instInhabitedName;
x_25 = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___closed__1;
x_26 = l_Lean_ParametricAttribute_getParam_x3f___rarg(x_24, x_25, x_23, x_17);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_free_object(x_1);
lean_dec(x_19);
lean_dec(x_18);
x_27 = lean_box(0);
lean_ctor_set(x_20, 0, x_27);
return x_20;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_26, 0);
lean_ctor_set(x_1, 0, x_29);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_20, 0, x_26);
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec(x_26);
lean_ctor_set(x_1, 0, x_30);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_20, 0, x_31);
return x_20;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_20);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_instInhabitedName;
x_36 = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___closed__1;
x_37 = l_Lean_ParametricAttribute_getParam_x3f___rarg(x_35, x_36, x_34, x_17);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_free_object(x_1);
lean_dec(x_19);
lean_dec(x_18);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_33);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_37, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_41 = x_37;
} else {
 lean_dec_ref(x_37);
 x_41 = lean_box(0);
}
lean_ctor_set(x_1, 0, x_40);
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 1, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_1);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_33);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_44 = lean_ctor_get(x_1, 0);
x_45 = lean_ctor_get(x_1, 1);
x_46 = lean_ctor_get(x_1, 2);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_1);
x_47 = lean_st_ref_get(x_8, x_13);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
lean_dec(x_48);
x_52 = l_Lean_instInhabitedName;
x_53 = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___closed__1;
x_54 = l_Lean_ParametricAttribute_getParam_x3f___rarg(x_52, x_53, x_51, x_44);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_46);
lean_dec(x_45);
x_55 = lean_box(0);
if (lean_is_scalar(x_50)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_50;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_49);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 x_58 = x_54;
} else {
 lean_dec_ref(x_54);
 x_58 = lean_box(0);
}
x_59 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_45);
lean_ctor_set(x_59, 2, x_46);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(1, 1, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_59);
if (lean_is_scalar(x_50)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_50;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_49);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_1);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_13);
return x_63;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_10 = l_Lean_Compiler_LCNF_Simp_simpProj_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_16 = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_16, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_16, 0, x_24);
return x_16;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_27 = x_17;
} else {
 lean_dec_ref(x_17);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(1, 1, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_16);
if (x_30 == 0)
{
return x_16;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_13);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_13, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_14);
if (x_36 == 0)
{
return x_13;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_14, 0);
lean_inc(x_37);
lean_dec(x_14);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_13, 0, x_38);
return x_13;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_13, 1);
lean_inc(x_39);
lean_dec(x_13);
x_40 = lean_ctor_get(x_14, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_41 = x_14;
} else {
 lean_dec_ref(x_14);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 1, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_10);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_10, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_11);
if (x_46 == 0)
{
return x_10;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_11, 0);
lean_inc(x_47);
lean_dec(x_11);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_10, 0, x_48);
return x_10;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_10, 1);
lean_inc(x_49);
lean_dec(x_10);
x_50 = lean_ctor_get(x_11, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_51 = x_11;
} else {
 lean_dec_ref(x_11);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Simp_SimpValue(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1);
l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___closed__1);
l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___closed__1);
l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
