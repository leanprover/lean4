// Lean compiler output
// Module: Init.Lean.Meta.Tactic.Assumption
// Imports: Init.Lean.Meta.ExprDefEq Init.Lean.Meta.Tactic.Util
#include "runtime/lean.h"
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
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___main___at_Lean_Meta_assumptionAux___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_Meta_assumptionAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_isEqvAux___main___at_Lean_Meta_assumptionAux___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findSomeRevM_x3f___at_Lean_Meta_assumptionAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findSomeRevM_x3f___at_Lean_Meta_assumptionAux___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assumption___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_assumption___closed__1;
lean_object* l_PersistentArray_findSomeRevM_x3f___at_Lean_Meta_assumptionAux___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_assumptionAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assumptionAux___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_PersistentArray_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Format_join___closed__1;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_PersistentArray_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_coeDecidableEq(uint8_t);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Meta_assumption(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_Meta_assumptionAux___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_Meta_assumptionAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assumptionAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assumptionAux___closed__1;
lean_object* l_PersistentArray_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findSomeRevM_x3f___at_Lean_Meta_assumptionAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_Meta_assumptionAux___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalInstance_beq(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_3, x_11);
lean_dec(x_3);
x_13 = lean_array_fget(x_2, x_12);
if (lean_obj_tag(x_13) == 0)
{
x_3 = x_12;
x_4 = lean_box(0);
goto _start;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = l_Lean_LocalDecl_type(x_16);
lean_inc(x_5);
lean_inc(x_1);
x_18 = l_Lean_Meta_isExprDefEq(x_1, x_17, x_5, x_6);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_free_object(x_13);
lean_dec(x_16);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_3 = x_12;
x_4 = lean_box(0);
x_6 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_18, 0);
lean_dec(x_24);
x_25 = l_Lean_LocalDecl_toExpr(x_16);
lean_dec(x_16);
lean_ctor_set(x_13, 0, x_25);
lean_ctor_set(x_18, 0, x_13);
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = l_Lean_LocalDecl_toExpr(x_16);
lean_dec(x_16);
lean_ctor_set(x_13, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_free_object(x_13);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_13, 0);
lean_inc(x_33);
lean_dec(x_13);
x_34 = l_Lean_LocalDecl_type(x_33);
lean_inc(x_5);
lean_inc(x_1);
x_35 = l_Lean_Meta_isExprDefEq(x_1, x_34, x_5, x_6);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_33);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_3 = x_12;
x_4 = lean_box(0);
x_6 = x_38;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_41 = x_35;
} else {
 lean_dec_ref(x_35);
 x_41 = lean_box(0);
}
x_42 = l_Lean_LocalDecl_toExpr(x_33);
lean_dec(x_33);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_33);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_45 = lean_ctor_get(x_35, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_35, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_47 = x_35;
} else {
 lean_dec_ref(x_35);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
}
}
}
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_3, x_11);
lean_dec(x_3);
x_13 = lean_array_fget(x_2, x_12);
lean_inc(x_5);
lean_inc(x_1);
x_14 = l_PersistentArray_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__4(x_1, x_13, x_5, x_6);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_3 = x_12;
x_4 = lean_box(0);
x_6 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_14, 0);
lean_dec(x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_3, x_11);
lean_dec(x_3);
x_13 = lean_array_fget(x_2, x_12);
if (lean_obj_tag(x_13) == 0)
{
x_3 = x_12;
x_4 = lean_box(0);
goto _start;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = l_Lean_LocalDecl_type(x_16);
lean_inc(x_5);
lean_inc(x_1);
x_18 = l_Lean_Meta_isExprDefEq(x_1, x_17, x_5, x_6);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_free_object(x_13);
lean_dec(x_16);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_3 = x_12;
x_4 = lean_box(0);
x_6 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_18, 0);
lean_dec(x_24);
x_25 = l_Lean_LocalDecl_toExpr(x_16);
lean_dec(x_16);
lean_ctor_set(x_13, 0, x_25);
lean_ctor_set(x_18, 0, x_13);
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = l_Lean_LocalDecl_toExpr(x_16);
lean_dec(x_16);
lean_ctor_set(x_13, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_free_object(x_13);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_13, 0);
lean_inc(x_33);
lean_dec(x_13);
x_34 = l_Lean_LocalDecl_type(x_33);
lean_inc(x_5);
lean_inc(x_1);
x_35 = l_Lean_Meta_isExprDefEq(x_1, x_34, x_5, x_6);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_33);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_3 = x_12;
x_4 = lean_box(0);
x_6 = x_38;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_41 = x_35;
} else {
 lean_dec_ref(x_35);
 x_41 = lean_box(0);
}
x_42 = l_Lean_LocalDecl_toExpr(x_33);
lean_dec(x_33);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_33);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_45 = lean_ctor_get(x_35, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_35, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_47 = x_35;
} else {
 lean_dec_ref(x_35);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
}
}
}
lean_object* l_PersistentArray_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_array_get_size(x_5);
x_7 = l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__5(x_1, x_5, x_6, lean_box(0), x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_array_get_size(x_8);
x_10 = l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__6(x_1, x_8, x_9, lean_box(0), x_3, x_4);
return x_10;
}
}
}
lean_object* l_PersistentArray_findSomeRevM_x3f___at_Lean_Meta_assumptionAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_7 = l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__3(x_1, x_5, x_6, lean_box(0), x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_2, 0);
x_11 = l_PersistentArray_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__4(x_1, x_10, x_3, x_9);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_3);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
uint8_t x_16; 
lean_dec(x_3);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_Meta_assumptionAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_PersistentArray_findSomeRevM_x3f___at_Lean_Meta_assumptionAux___spec__2(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_3, x_11);
lean_dec(x_3);
x_13 = lean_array_fget(x_2, x_12);
if (lean_obj_tag(x_13) == 0)
{
x_3 = x_12;
x_4 = lean_box(0);
goto _start;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = l_Lean_LocalDecl_type(x_16);
lean_inc(x_5);
lean_inc(x_1);
x_18 = l_Lean_Meta_isExprDefEq(x_1, x_17, x_5, x_6);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_free_object(x_13);
lean_dec(x_16);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_3 = x_12;
x_4 = lean_box(0);
x_6 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_18, 0);
lean_dec(x_24);
x_25 = l_Lean_LocalDecl_toExpr(x_16);
lean_dec(x_16);
lean_ctor_set(x_13, 0, x_25);
lean_ctor_set(x_18, 0, x_13);
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = l_Lean_LocalDecl_toExpr(x_16);
lean_dec(x_16);
lean_ctor_set(x_13, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_free_object(x_13);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_13, 0);
lean_inc(x_33);
lean_dec(x_13);
x_34 = l_Lean_LocalDecl_type(x_33);
lean_inc(x_5);
lean_inc(x_1);
x_35 = l_Lean_Meta_isExprDefEq(x_1, x_34, x_5, x_6);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_33);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_3 = x_12;
x_4 = lean_box(0);
x_6 = x_38;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_41 = x_35;
} else {
 lean_dec_ref(x_35);
 x_41 = lean_box(0);
}
x_42 = l_Lean_LocalDecl_toExpr(x_33);
lean_dec(x_33);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_33);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_45 = lean_ctor_get(x_35, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_35, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_47 = x_35;
} else {
 lean_dec_ref(x_35);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
}
}
}
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_3, x_11);
lean_dec(x_3);
x_13 = lean_array_fget(x_2, x_12);
lean_inc(x_5);
lean_inc(x_1);
x_14 = l_PersistentArray_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__10(x_1, x_13, x_5, x_6);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_3 = x_12;
x_4 = lean_box(0);
x_6 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_14, 0);
lean_dec(x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_3, x_11);
lean_dec(x_3);
x_13 = lean_array_fget(x_2, x_12);
if (lean_obj_tag(x_13) == 0)
{
x_3 = x_12;
x_4 = lean_box(0);
goto _start;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = l_Lean_LocalDecl_type(x_16);
lean_inc(x_5);
lean_inc(x_1);
x_18 = l_Lean_Meta_isExprDefEq(x_1, x_17, x_5, x_6);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_free_object(x_13);
lean_dec(x_16);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_3 = x_12;
x_4 = lean_box(0);
x_6 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_18, 0);
lean_dec(x_24);
x_25 = l_Lean_LocalDecl_toExpr(x_16);
lean_dec(x_16);
lean_ctor_set(x_13, 0, x_25);
lean_ctor_set(x_18, 0, x_13);
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = l_Lean_LocalDecl_toExpr(x_16);
lean_dec(x_16);
lean_ctor_set(x_13, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_free_object(x_13);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_13, 0);
lean_inc(x_33);
lean_dec(x_13);
x_34 = l_Lean_LocalDecl_type(x_33);
lean_inc(x_5);
lean_inc(x_1);
x_35 = l_Lean_Meta_isExprDefEq(x_1, x_34, x_5, x_6);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_33);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_3 = x_12;
x_4 = lean_box(0);
x_6 = x_38;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_41 = x_35;
} else {
 lean_dec_ref(x_35);
 x_41 = lean_box(0);
}
x_42 = l_Lean_LocalDecl_toExpr(x_33);
lean_dec(x_33);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_33);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_45 = lean_ctor_get(x_35, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_35, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_47 = x_35;
} else {
 lean_dec_ref(x_35);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
}
}
}
lean_object* l_PersistentArray_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_array_get_size(x_5);
x_7 = l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__11(x_1, x_5, x_6, lean_box(0), x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_array_get_size(x_8);
x_10 = l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__12(x_1, x_8, x_9, lean_box(0), x_3, x_4);
return x_10;
}
}
}
lean_object* l_PersistentArray_findSomeRevM_x3f___at_Lean_Meta_assumptionAux___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_7 = l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__9(x_1, x_5, x_6, lean_box(0), x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_2, 0);
x_11 = l_PersistentArray_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__10(x_1, x_10, x_3, x_9);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_3);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
uint8_t x_16; 
lean_dec(x_3);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_Meta_assumptionAux___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_PersistentArray_findSomeRevM_x3f___at_Lean_Meta_assumptionAux___spec__8(x_1, x_5, x_3, x_4);
return x_6;
}
}
uint8_t l_Array_isEqvAux___main___at_Lean_Meta_assumptionAux___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = l_Lean_LocalInstance_beq(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_15;
goto _start;
}
}
}
}
lean_object* _init_l_Lean_Meta_assumptionAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("assumption");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_assumptionAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_assumptionAux___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_assumptionAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l_Lean_Meta_getMVarDecl(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_7 = x_4;
} else {
 lean_dec_ref(x_4);
 x_7 = lean_box(0);
}
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 4);
lean_inc(x_13);
x_14 = lean_array_get_size(x_9);
x_15 = lean_array_get_size(x_13);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_8);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_13);
lean_ctor_set(x_17, 3, x_10);
lean_ctor_set(x_17, 4, x_11);
if (x_16 == 0)
{
uint8_t x_273; 
lean_dec(x_13);
lean_dec(x_5);
x_273 = 0;
x_18 = x_273;
goto block_272;
}
else
{
lean_object* x_274; uint8_t x_275; 
x_274 = lean_unsigned_to_nat(0u);
x_275 = l_Array_isEqvAux___main___at_Lean_Meta_assumptionAux___spec__13(x_2, x_5, lean_box(0), x_9, x_13, x_274);
lean_dec(x_13);
lean_dec(x_5);
x_18 = x_275;
goto block_272;
}
block_272:
{
uint8_t x_19; 
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_6);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_6, 2);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_51; lean_object* x_52; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_23 = lean_ctor_get(x_21, 2);
x_75 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_21, 2, x_75);
x_76 = l_Lean_Meta_assumptionAux___closed__2;
lean_inc(x_1);
x_77 = l_Lean_Meta_checkNotAssigned(x_1, x_76, x_17, x_6);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
lean_inc(x_1);
x_79 = l_Lean_Meta_getMVarType(x_1, x_17, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
lean_inc(x_17);
x_82 = l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_Meta_assumptionAux___spec__1(x_80, x_12, x_17, x_81);
lean_dec(x_12);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; uint8_t x_85; 
lean_dec(x_17);
lean_dec(x_1);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = 0;
x_24 = x_85;
x_25 = x_84;
goto block_50;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_dec(x_82);
x_87 = lean_ctor_get(x_83, 0);
lean_inc(x_87);
lean_dec(x_83);
x_88 = l_Lean_Meta_assignExprMVar(x_1, x_87, x_17, x_86);
lean_dec(x_17);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = 1;
x_24 = x_90;
x_25 = x_89;
goto block_50;
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_7);
x_91 = lean_ctor_get(x_88, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_88, 1);
lean_inc(x_92);
lean_dec(x_88);
x_51 = x_91;
x_52 = x_92;
goto block_74;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_1);
x_93 = lean_ctor_get(x_82, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_82, 1);
lean_inc(x_94);
lean_dec(x_82);
x_51 = x_93;
x_52 = x_94;
goto block_74;
}
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_1);
x_95 = lean_ctor_get(x_79, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_79, 1);
lean_inc(x_96);
lean_dec(x_79);
x_51 = x_95;
x_52 = x_96;
goto block_74;
}
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_1);
x_97 = lean_ctor_get(x_77, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_77, 1);
lean_inc(x_98);
lean_dec(x_77);
x_51 = x_97;
x_52 = x_98;
goto block_74;
}
block_50:
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 2);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 2);
lean_dec(x_29);
lean_ctor_set(x_27, 2, x_23);
x_30 = lean_box(x_24);
if (lean_is_scalar(x_7)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_7;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_27);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_23);
lean_ctor_set(x_25, 2, x_34);
x_35 = lean_box(x_24);
if (lean_is_scalar(x_7)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_7;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_25);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_37 = lean_ctor_get(x_25, 2);
x_38 = lean_ctor_get(x_25, 0);
x_39 = lean_ctor_get(x_25, 1);
x_40 = lean_ctor_get(x_25, 3);
x_41 = lean_ctor_get(x_25, 4);
x_42 = lean_ctor_get(x_25, 5);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_37);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_25);
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 3, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_23);
x_47 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_39);
lean_ctor_set(x_47, 2, x_46);
lean_ctor_set(x_47, 3, x_40);
lean_ctor_set(x_47, 4, x_41);
lean_ctor_set(x_47, 5, x_42);
x_48 = lean_box(x_24);
if (lean_is_scalar(x_7)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_7;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
block_74:
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_52, 2);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 2);
lean_dec(x_56);
lean_ctor_set(x_54, 2, x_23);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_52);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_54, 0);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_54);
x_60 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_60, 2, x_23);
lean_ctor_set(x_52, 2, x_60);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_51);
lean_ctor_set(x_61, 1, x_52);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_62 = lean_ctor_get(x_52, 2);
x_63 = lean_ctor_get(x_52, 0);
x_64 = lean_ctor_get(x_52, 1);
x_65 = lean_ctor_get(x_52, 3);
x_66 = lean_ctor_get(x_52, 4);
x_67 = lean_ctor_get(x_52, 5);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_62);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_52);
x_68 = lean_ctor_get(x_62, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 lean_ctor_release(x_62, 2);
 x_70 = x_62;
} else {
 lean_dec_ref(x_62);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 3, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
lean_ctor_set(x_71, 2, x_23);
x_72 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_72, 0, x_63);
lean_ctor_set(x_72, 1, x_64);
lean_ctor_set(x_72, 2, x_71);
lean_ctor_set(x_72, 3, x_65);
lean_ctor_set(x_72, 4, x_66);
lean_ctor_set(x_72, 5, x_67);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_51);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_119; lean_object* x_120; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_99 = lean_ctor_get(x_21, 0);
x_100 = lean_ctor_get(x_21, 1);
x_101 = lean_ctor_get(x_21, 2);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_21);
x_135 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_136 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_136, 0, x_99);
lean_ctor_set(x_136, 1, x_100);
lean_ctor_set(x_136, 2, x_135);
lean_ctor_set(x_6, 2, x_136);
x_137 = l_Lean_Meta_assumptionAux___closed__2;
lean_inc(x_1);
x_138 = l_Lean_Meta_checkNotAssigned(x_1, x_137, x_17, x_6);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
lean_inc(x_1);
x_140 = l_Lean_Meta_getMVarType(x_1, x_17, x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
lean_inc(x_17);
x_143 = l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_Meta_assumptionAux___spec__1(x_141, x_12, x_17, x_142);
lean_dec(x_12);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; uint8_t x_146; 
lean_dec(x_17);
lean_dec(x_1);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = 0;
x_102 = x_146;
x_103 = x_145;
goto block_118;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_143, 1);
lean_inc(x_147);
lean_dec(x_143);
x_148 = lean_ctor_get(x_144, 0);
lean_inc(x_148);
lean_dec(x_144);
x_149 = l_Lean_Meta_assignExprMVar(x_1, x_148, x_17, x_147);
lean_dec(x_17);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; uint8_t x_151; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
x_151 = 1;
x_102 = x_151;
x_103 = x_150;
goto block_118;
}
else
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_7);
x_152 = lean_ctor_get(x_149, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_149, 1);
lean_inc(x_153);
lean_dec(x_149);
x_119 = x_152;
x_120 = x_153;
goto block_134;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_1);
x_154 = lean_ctor_get(x_143, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_143, 1);
lean_inc(x_155);
lean_dec(x_143);
x_119 = x_154;
x_120 = x_155;
goto block_134;
}
}
else
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_1);
x_156 = lean_ctor_get(x_140, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_140, 1);
lean_inc(x_157);
lean_dec(x_140);
x_119 = x_156;
x_120 = x_157;
goto block_134;
}
}
else
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_1);
x_158 = lean_ctor_get(x_138, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_138, 1);
lean_inc(x_159);
lean_dec(x_138);
x_119 = x_158;
x_120 = x_159;
goto block_134;
}
block_118:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_104 = lean_ctor_get(x_103, 2);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_103, 3);
lean_inc(x_107);
x_108 = lean_ctor_get(x_103, 4);
lean_inc(x_108);
x_109 = lean_ctor_get(x_103, 5);
lean_inc(x_109);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 lean_ctor_release(x_103, 2);
 lean_ctor_release(x_103, 3);
 lean_ctor_release(x_103, 4);
 lean_ctor_release(x_103, 5);
 x_110 = x_103;
} else {
 lean_dec_ref(x_103);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get(x_104, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_104, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 lean_ctor_release(x_104, 2);
 x_113 = x_104;
} else {
 lean_dec_ref(x_104);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(0, 3, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
lean_ctor_set(x_114, 2, x_101);
if (lean_is_scalar(x_110)) {
 x_115 = lean_alloc_ctor(0, 6, 0);
} else {
 x_115 = x_110;
}
lean_ctor_set(x_115, 0, x_105);
lean_ctor_set(x_115, 1, x_106);
lean_ctor_set(x_115, 2, x_114);
lean_ctor_set(x_115, 3, x_107);
lean_ctor_set(x_115, 4, x_108);
lean_ctor_set(x_115, 5, x_109);
x_116 = lean_box(x_102);
if (lean_is_scalar(x_7)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_7;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
block_134:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_121 = lean_ctor_get(x_120, 2);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_120, 3);
lean_inc(x_124);
x_125 = lean_ctor_get(x_120, 4);
lean_inc(x_125);
x_126 = lean_ctor_get(x_120, 5);
lean_inc(x_126);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 lean_ctor_release(x_120, 2);
 lean_ctor_release(x_120, 3);
 lean_ctor_release(x_120, 4);
 lean_ctor_release(x_120, 5);
 x_127 = x_120;
} else {
 lean_dec_ref(x_120);
 x_127 = lean_box(0);
}
x_128 = lean_ctor_get(x_121, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_121, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 lean_ctor_release(x_121, 2);
 x_130 = x_121;
} else {
 lean_dec_ref(x_121);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(0, 3, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
lean_ctor_set(x_131, 2, x_101);
if (lean_is_scalar(x_127)) {
 x_132 = lean_alloc_ctor(0, 6, 0);
} else {
 x_132 = x_127;
}
lean_ctor_set(x_132, 0, x_122);
lean_ctor_set(x_132, 1, x_123);
lean_ctor_set(x_132, 2, x_131);
lean_ctor_set(x_132, 3, x_124);
lean_ctor_set(x_132, 4, x_125);
lean_ctor_set(x_132, 5, x_126);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_119);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_187; lean_object* x_188; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_160 = lean_ctor_get(x_6, 2);
x_161 = lean_ctor_get(x_6, 0);
x_162 = lean_ctor_get(x_6, 1);
x_163 = lean_ctor_get(x_6, 3);
x_164 = lean_ctor_get(x_6, 4);
x_165 = lean_ctor_get(x_6, 5);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_160);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_6);
x_166 = lean_ctor_get(x_160, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_160, 1);
lean_inc(x_167);
x_168 = lean_ctor_get(x_160, 2);
lean_inc(x_168);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 lean_ctor_release(x_160, 2);
 x_169 = x_160;
} else {
 lean_dec_ref(x_160);
 x_169 = lean_box(0);
}
x_203 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_169)) {
 x_204 = lean_alloc_ctor(0, 3, 0);
} else {
 x_204 = x_169;
}
lean_ctor_set(x_204, 0, x_166);
lean_ctor_set(x_204, 1, x_167);
lean_ctor_set(x_204, 2, x_203);
x_205 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_205, 0, x_161);
lean_ctor_set(x_205, 1, x_162);
lean_ctor_set(x_205, 2, x_204);
lean_ctor_set(x_205, 3, x_163);
lean_ctor_set(x_205, 4, x_164);
lean_ctor_set(x_205, 5, x_165);
x_206 = l_Lean_Meta_assumptionAux___closed__2;
lean_inc(x_1);
x_207 = l_Lean_Meta_checkNotAssigned(x_1, x_206, x_17, x_205);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
lean_dec(x_207);
lean_inc(x_1);
x_209 = l_Lean_Meta_getMVarType(x_1, x_17, x_208);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
lean_inc(x_17);
x_212 = l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_Meta_assumptionAux___spec__1(x_210, x_12, x_17, x_211);
lean_dec(x_12);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; uint8_t x_215; 
lean_dec(x_17);
lean_dec(x_1);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = 0;
x_170 = x_215;
x_171 = x_214;
goto block_186;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_212, 1);
lean_inc(x_216);
lean_dec(x_212);
x_217 = lean_ctor_get(x_213, 0);
lean_inc(x_217);
lean_dec(x_213);
x_218 = l_Lean_Meta_assignExprMVar(x_1, x_217, x_17, x_216);
lean_dec(x_17);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; uint8_t x_220; 
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
lean_dec(x_218);
x_220 = 1;
x_170 = x_220;
x_171 = x_219;
goto block_186;
}
else
{
lean_object* x_221; lean_object* x_222; 
lean_dec(x_7);
x_221 = lean_ctor_get(x_218, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_218, 1);
lean_inc(x_222);
lean_dec(x_218);
x_187 = x_221;
x_188 = x_222;
goto block_202;
}
}
}
else
{
lean_object* x_223; lean_object* x_224; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_1);
x_223 = lean_ctor_get(x_212, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_212, 1);
lean_inc(x_224);
lean_dec(x_212);
x_187 = x_223;
x_188 = x_224;
goto block_202;
}
}
else
{
lean_object* x_225; lean_object* x_226; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_1);
x_225 = lean_ctor_get(x_209, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_209, 1);
lean_inc(x_226);
lean_dec(x_209);
x_187 = x_225;
x_188 = x_226;
goto block_202;
}
}
else
{
lean_object* x_227; lean_object* x_228; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_1);
x_227 = lean_ctor_get(x_207, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_207, 1);
lean_inc(x_228);
lean_dec(x_207);
x_187 = x_227;
x_188 = x_228;
goto block_202;
}
block_186:
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_172 = lean_ctor_get(x_171, 2);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
x_175 = lean_ctor_get(x_171, 3);
lean_inc(x_175);
x_176 = lean_ctor_get(x_171, 4);
lean_inc(x_176);
x_177 = lean_ctor_get(x_171, 5);
lean_inc(x_177);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 lean_ctor_release(x_171, 2);
 lean_ctor_release(x_171, 3);
 lean_ctor_release(x_171, 4);
 lean_ctor_release(x_171, 5);
 x_178 = x_171;
} else {
 lean_dec_ref(x_171);
 x_178 = lean_box(0);
}
x_179 = lean_ctor_get(x_172, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_172, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 lean_ctor_release(x_172, 2);
 x_181 = x_172;
} else {
 lean_dec_ref(x_172);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(0, 3, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
lean_ctor_set(x_182, 2, x_168);
if (lean_is_scalar(x_178)) {
 x_183 = lean_alloc_ctor(0, 6, 0);
} else {
 x_183 = x_178;
}
lean_ctor_set(x_183, 0, x_173);
lean_ctor_set(x_183, 1, x_174);
lean_ctor_set(x_183, 2, x_182);
lean_ctor_set(x_183, 3, x_175);
lean_ctor_set(x_183, 4, x_176);
lean_ctor_set(x_183, 5, x_177);
x_184 = lean_box(x_170);
if (lean_is_scalar(x_7)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_7;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
block_202:
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_189 = lean_ctor_get(x_188, 2);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_188, 1);
lean_inc(x_191);
x_192 = lean_ctor_get(x_188, 3);
lean_inc(x_192);
x_193 = lean_ctor_get(x_188, 4);
lean_inc(x_193);
x_194 = lean_ctor_get(x_188, 5);
lean_inc(x_194);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 lean_ctor_release(x_188, 4);
 lean_ctor_release(x_188, 5);
 x_195 = x_188;
} else {
 lean_dec_ref(x_188);
 x_195 = lean_box(0);
}
x_196 = lean_ctor_get(x_189, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_189, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 lean_ctor_release(x_189, 2);
 x_198 = x_189;
} else {
 lean_dec_ref(x_189);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(0, 3, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_197);
lean_ctor_set(x_199, 2, x_168);
if (lean_is_scalar(x_195)) {
 x_200 = lean_alloc_ctor(0, 6, 0);
} else {
 x_200 = x_195;
}
lean_ctor_set(x_200, 0, x_190);
lean_ctor_set(x_200, 1, x_191);
lean_ctor_set(x_200, 2, x_199);
lean_ctor_set(x_200, 3, x_192);
lean_ctor_set(x_200, 4, x_193);
lean_ctor_set(x_200, 5, x_194);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_187);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
else
{
lean_object* x_229; lean_object* x_230; 
lean_dec(x_7);
x_229 = l_Lean_Meta_assumptionAux___closed__2;
lean_inc(x_1);
x_230 = l_Lean_Meta_checkNotAssigned(x_1, x_229, x_17, x_6);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
lean_dec(x_230);
lean_inc(x_1);
x_232 = l_Lean_Meta_getMVarType(x_1, x_17, x_231);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
lean_inc(x_17);
x_235 = l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_Meta_assumptionAux___spec__7(x_233, x_12, x_17, x_234);
lean_dec(x_12);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
if (lean_obj_tag(x_236) == 0)
{
uint8_t x_237; 
lean_dec(x_17);
lean_dec(x_1);
x_237 = !lean_is_exclusive(x_235);
if (x_237 == 0)
{
lean_object* x_238; uint8_t x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_235, 0);
lean_dec(x_238);
x_239 = 0;
x_240 = lean_box(x_239);
lean_ctor_set(x_235, 0, x_240);
return x_235;
}
else
{
lean_object* x_241; uint8_t x_242; lean_object* x_243; lean_object* x_244; 
x_241 = lean_ctor_get(x_235, 1);
lean_inc(x_241);
lean_dec(x_235);
x_242 = 0;
x_243 = lean_box(x_242);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_241);
return x_244;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_235, 1);
lean_inc(x_245);
lean_dec(x_235);
x_246 = lean_ctor_get(x_236, 0);
lean_inc(x_246);
lean_dec(x_236);
x_247 = l_Lean_Meta_assignExprMVar(x_1, x_246, x_17, x_245);
lean_dec(x_17);
if (lean_obj_tag(x_247) == 0)
{
uint8_t x_248; 
x_248 = !lean_is_exclusive(x_247);
if (x_248 == 0)
{
lean_object* x_249; uint8_t x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_247, 0);
lean_dec(x_249);
x_250 = 1;
x_251 = lean_box(x_250);
lean_ctor_set(x_247, 0, x_251);
return x_247;
}
else
{
lean_object* x_252; uint8_t x_253; lean_object* x_254; lean_object* x_255; 
x_252 = lean_ctor_get(x_247, 1);
lean_inc(x_252);
lean_dec(x_247);
x_253 = 1;
x_254 = lean_box(x_253);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_252);
return x_255;
}
}
else
{
uint8_t x_256; 
x_256 = !lean_is_exclusive(x_247);
if (x_256 == 0)
{
return x_247;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_247, 0);
x_258 = lean_ctor_get(x_247, 1);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_247);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
return x_259;
}
}
}
}
else
{
uint8_t x_260; 
lean_dec(x_17);
lean_dec(x_1);
x_260 = !lean_is_exclusive(x_235);
if (x_260 == 0)
{
return x_235;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_235, 0);
x_262 = lean_ctor_get(x_235, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_235);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
return x_263;
}
}
}
else
{
uint8_t x_264; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_1);
x_264 = !lean_is_exclusive(x_232);
if (x_264 == 0)
{
return x_232;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_232, 0);
x_266 = lean_ctor_get(x_232, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_232);
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_265);
lean_ctor_set(x_267, 1, x_266);
return x_267;
}
}
}
else
{
uint8_t x_268; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_1);
x_268 = !lean_is_exclusive(x_230);
if (x_268 == 0)
{
return x_230;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_230, 0);
x_270 = lean_ctor_get(x_230, 1);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_230);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
return x_271;
}
}
}
}
}
else
{
uint8_t x_276; 
lean_dec(x_1);
x_276 = !lean_is_exclusive(x_4);
if (x_276 == 0)
{
return x_4;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_4, 0);
x_278 = lean_ctor_get(x_4, 1);
lean_inc(x_278);
lean_inc(x_277);
lean_dec(x_4);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
return x_279;
}
}
}
}
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_PersistentArray_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_PersistentArray_findSomeRevM_x3f___at_Lean_Meta_assumptionAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_findSomeRevM_x3f___at_Lean_Meta_assumptionAux___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_Meta_assumptionAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_Meta_assumptionAux___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__9(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__11(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__12(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_PersistentArray_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_findSomeRevMAux___main___at_Lean_Meta_assumptionAux___spec__10(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_PersistentArray_findSomeRevM_x3f___at_Lean_Meta_assumptionAux___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_findSomeRevM_x3f___at_Lean_Meta_assumptionAux___spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_Meta_assumptionAux___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_Meta_assumptionAux___spec__7(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_isEqvAux___main___at_Lean_Meta_assumptionAux___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___main___at_Lean_Meta_assumptionAux___spec__13(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_assumptionAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_assumptionAux(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_assumption___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_join___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_assumption(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l_Lean_Meta_assumptionAux(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = l_Lean_Meta_assumptionAux___closed__2;
x_9 = l_Lean_Meta_assumption___closed__1;
x_10 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_1, x_9, x_2, x_7);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_4, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec(x_4);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_4);
if (x_17 == 0)
{
return x_4;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_4);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_Meta_assumption___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_assumption(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init_Lean_Meta_ExprDefEq(lean_object*);
lean_object* initialize_Init_Lean_Meta_Tactic_Util(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_Tactic_Assumption(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Meta_ExprDefEq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Tactic_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_assumptionAux___closed__1 = _init_l_Lean_Meta_assumptionAux___closed__1();
lean_mark_persistent(l_Lean_Meta_assumptionAux___closed__1);
l_Lean_Meta_assumptionAux___closed__2 = _init_l_Lean_Meta_assumptionAux___closed__2();
lean_mark_persistent(l_Lean_Meta_assumptionAux___closed__2);
l_Lean_Meta_assumption___closed__1 = _init_l_Lean_Meta_assumption___closed__1();
lean_mark_persistent(l_Lean_Meta_assumption___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
