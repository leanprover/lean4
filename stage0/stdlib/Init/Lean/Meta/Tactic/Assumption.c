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
lean_object* l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findRevM___at_Lean_Meta_assumptionAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assumption___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_assumption___closed__1;
lean_object* l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___main___at_Lean_Meta_assumptionAux___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findDeclRevM___at_Lean_Meta_assumptionAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assumptionAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findDeclRevM___at_Lean_Meta_assumptionAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assumption___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findRevM___at_Lean_Meta_assumptionAux___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Meta_assumption(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assumptionAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assumptionAux___closed__1;
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findDeclRevM___at_Lean_Meta_assumptionAux___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_isEqvAux___main___at_Lean_Meta_assumptionAux___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findRevM___at_Lean_Meta_assumptionAux___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findDeclRevM___at_Lean_Meta_assumptionAux___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findRevM___at_Lean_Meta_assumptionAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalInstance_beq(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_object* l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_14 = l_PersistentArray_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__4(x_1, x_13, x_5, x_6);
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
lean_object* l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_PersistentArray_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_array_get_size(x_5);
x_7 = l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__5(x_1, x_5, x_6, lean_box(0), x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_array_get_size(x_8);
x_10 = l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__6(x_1, x_8, x_9, lean_box(0), x_3, x_4);
return x_10;
}
}
}
lean_object* l_PersistentArray_findRevM___at_Lean_Meta_assumptionAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_7 = l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__3(x_1, x_5, x_6, lean_box(0), x_3, x_4);
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
x_11 = l_PersistentArray_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__4(x_1, x_10, x_3, x_9);
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
lean_object* l_Lean_LocalContext_findDeclRevM___at_Lean_Meta_assumptionAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_PersistentArray_findRevM___at_Lean_Meta_assumptionAux___spec__2(x_1, x_5, x_3, x_4);
return x_6;
}
}
uint8_t l_Array_isEqvAux___main___at_Lean_Meta_assumptionAux___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_14 = l_PersistentArray_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__11(x_1, x_13, x_5, x_6);
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
lean_object* l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_PersistentArray_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_array_get_size(x_5);
x_7 = l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__12(x_1, x_5, x_6, lean_box(0), x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_array_get_size(x_8);
x_10 = l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__13(x_1, x_8, x_9, lean_box(0), x_3, x_4);
return x_10;
}
}
}
lean_object* l_PersistentArray_findRevM___at_Lean_Meta_assumptionAux___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_7 = l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__10(x_1, x_5, x_6, lean_box(0), x_3, x_4);
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
x_11 = l_PersistentArray_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__11(x_1, x_10, x_3, x_9);
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
lean_object* l_Lean_LocalContext_findDeclRevM___at_Lean_Meta_assumptionAux___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_PersistentArray_findRevM___at_Lean_Meta_assumptionAux___spec__9(x_1, x_5, x_3, x_4);
return x_6;
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
lean_object* l_Lean_Meta_assumptionAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l_Lean_Meta_getMVarDecl(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
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
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 4);
lean_inc(x_11);
x_12 = lean_array_get_size(x_9);
x_13 = lean_array_get_size(x_11);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_11);
if (x_14 == 0)
{
lean_object* x_227; 
lean_dec(x_11);
lean_dec(x_5);
x_227 = lean_box(0);
x_16 = x_227;
goto block_226;
}
else
{
lean_object* x_228; uint8_t x_229; 
x_228 = lean_unsigned_to_nat(0u);
x_229 = l_Array_isEqvAux___main___at_Lean_Meta_assumptionAux___spec__7(x_2, x_5, lean_box(0), x_9, x_11, x_228);
lean_dec(x_11);
lean_dec(x_5);
if (x_229 == 0)
{
lean_object* x_230; 
x_230 = lean_box(0);
x_16 = x_230;
goto block_226;
}
else
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_7);
x_231 = l_Lean_Meta_assumptionAux___closed__1;
lean_inc(x_1);
x_232 = l_Lean_Meta_checkNotAssigned(x_1, x_231, x_15, x_6);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_232, 1);
lean_inc(x_233);
lean_dec(x_232);
lean_inc(x_1);
x_234 = l_Lean_Meta_getMVarType(x_1, x_15, x_233);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
lean_inc(x_15);
x_237 = l_Lean_LocalContext_findDeclRevM___at_Lean_Meta_assumptionAux___spec__8(x_235, x_10, x_15, x_236);
lean_dec(x_10);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
if (lean_obj_tag(x_238) == 0)
{
uint8_t x_239; 
lean_dec(x_15);
lean_dec(x_1);
x_239 = !lean_is_exclusive(x_237);
if (x_239 == 0)
{
lean_object* x_240; uint8_t x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_237, 0);
lean_dec(x_240);
x_241 = 0;
x_242 = lean_box(x_241);
lean_ctor_set(x_237, 0, x_242);
return x_237;
}
else
{
lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; 
x_243 = lean_ctor_get(x_237, 1);
lean_inc(x_243);
lean_dec(x_237);
x_244 = 0;
x_245 = lean_box(x_244);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_243);
return x_246;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_237, 1);
lean_inc(x_247);
lean_dec(x_237);
x_248 = lean_ctor_get(x_238, 0);
lean_inc(x_248);
lean_dec(x_238);
x_249 = l_Lean_Meta_assignExprMVar(x_1, x_248, x_15, x_247);
lean_dec(x_15);
if (lean_obj_tag(x_249) == 0)
{
uint8_t x_250; 
x_250 = !lean_is_exclusive(x_249);
if (x_250 == 0)
{
lean_object* x_251; uint8_t x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_249, 0);
lean_dec(x_251);
x_252 = 1;
x_253 = lean_box(x_252);
lean_ctor_set(x_249, 0, x_253);
return x_249;
}
else
{
lean_object* x_254; uint8_t x_255; lean_object* x_256; lean_object* x_257; 
x_254 = lean_ctor_get(x_249, 1);
lean_inc(x_254);
lean_dec(x_249);
x_255 = 1;
x_256 = lean_box(x_255);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_254);
return x_257;
}
}
else
{
uint8_t x_258; 
x_258 = !lean_is_exclusive(x_249);
if (x_258 == 0)
{
return x_249;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_249, 0);
x_260 = lean_ctor_get(x_249, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_249);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
return x_261;
}
}
}
}
else
{
uint8_t x_262; 
lean_dec(x_15);
lean_dec(x_1);
x_262 = !lean_is_exclusive(x_237);
if (x_262 == 0)
{
return x_237;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_237, 0);
x_264 = lean_ctor_get(x_237, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_237);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
}
}
else
{
uint8_t x_266; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_1);
x_266 = !lean_is_exclusive(x_234);
if (x_266 == 0)
{
return x_234;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_234, 0);
x_268 = lean_ctor_get(x_234, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_234);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
}
else
{
uint8_t x_270; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_1);
x_270 = !lean_is_exclusive(x_232);
if (x_270 == 0)
{
return x_232;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_232, 0);
x_272 = lean_ctor_get(x_232, 1);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_232);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
return x_273;
}
}
}
}
block_226:
{
uint8_t x_17; 
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_6, 2);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_48; lean_object* x_49; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_20 = lean_ctor_get(x_18, 2);
x_72 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_18, 2, x_72);
x_73 = l_Lean_Meta_assumptionAux___closed__1;
lean_inc(x_1);
x_74 = l_Lean_Meta_checkNotAssigned(x_1, x_73, x_15, x_6);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
lean_inc(x_1);
x_76 = l_Lean_Meta_getMVarType(x_1, x_15, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_15);
x_79 = l_Lean_LocalContext_findDeclRevM___at_Lean_Meta_assumptionAux___spec__1(x_77, x_10, x_15, x_78);
lean_dec(x_10);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; uint8_t x_82; 
lean_dec(x_15);
lean_dec(x_1);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = 0;
x_21 = x_82;
x_22 = x_81;
goto block_47;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_dec(x_79);
x_84 = lean_ctor_get(x_80, 0);
lean_inc(x_84);
lean_dec(x_80);
x_85 = l_Lean_Meta_assignExprMVar(x_1, x_84, x_15, x_83);
lean_dec(x_15);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = 1;
x_21 = x_87;
x_22 = x_86;
goto block_47;
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_7);
x_88 = lean_ctor_get(x_85, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_85, 1);
lean_inc(x_89);
lean_dec(x_85);
x_48 = x_88;
x_49 = x_89;
goto block_71;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_1);
x_90 = lean_ctor_get(x_79, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_79, 1);
lean_inc(x_91);
lean_dec(x_79);
x_48 = x_90;
x_49 = x_91;
goto block_71;
}
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_1);
x_92 = lean_ctor_get(x_76, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_76, 1);
lean_inc(x_93);
lean_dec(x_76);
x_48 = x_92;
x_49 = x_93;
goto block_71;
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_1);
x_94 = lean_ctor_get(x_74, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_74, 1);
lean_inc(x_95);
lean_dec(x_74);
x_48 = x_94;
x_49 = x_95;
goto block_71;
}
block_47:
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_22, 2);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 2);
lean_dec(x_26);
lean_ctor_set(x_24, 2, x_20);
x_27 = lean_box(x_21);
if (lean_is_scalar(x_7)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_7;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_22);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_20);
lean_ctor_set(x_22, 2, x_31);
x_32 = lean_box(x_21);
if (lean_is_scalar(x_7)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_7;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_22);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_34 = lean_ctor_get(x_22, 2);
x_35 = lean_ctor_get(x_22, 0);
x_36 = lean_ctor_get(x_22, 1);
x_37 = lean_ctor_get(x_22, 3);
x_38 = lean_ctor_get(x_22, 4);
x_39 = lean_ctor_get(x_22, 5);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_34);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_22);
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 x_42 = x_34;
} else {
 lean_dec_ref(x_34);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 3, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_43, 2, x_20);
x_44 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_44, 0, x_35);
lean_ctor_set(x_44, 1, x_36);
lean_ctor_set(x_44, 2, x_43);
lean_ctor_set(x_44, 3, x_37);
lean_ctor_set(x_44, 4, x_38);
lean_ctor_set(x_44, 5, x_39);
x_45 = lean_box(x_21);
if (lean_is_scalar(x_7)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_7;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
block_71:
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_49, 2);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 2);
lean_dec(x_53);
lean_ctor_set(x_51, 2, x_20);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_49);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_51, 0);
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_51);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_20);
lean_ctor_set(x_49, 2, x_57);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_49);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_59 = lean_ctor_get(x_49, 2);
x_60 = lean_ctor_get(x_49, 0);
x_61 = lean_ctor_get(x_49, 1);
x_62 = lean_ctor_get(x_49, 3);
x_63 = lean_ctor_get(x_49, 4);
x_64 = lean_ctor_get(x_49, 5);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_59);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_49);
x_65 = lean_ctor_get(x_59, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 x_67 = x_59;
} else {
 lean_dec_ref(x_59);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 3, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
lean_ctor_set(x_68, 2, x_20);
x_69 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_69, 0, x_60);
lean_ctor_set(x_69, 1, x_61);
lean_ctor_set(x_69, 2, x_68);
lean_ctor_set(x_69, 3, x_62);
lean_ctor_set(x_69, 4, x_63);
lean_ctor_set(x_69, 5, x_64);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_48);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_116; lean_object* x_117; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_96 = lean_ctor_get(x_18, 0);
x_97 = lean_ctor_get(x_18, 1);
x_98 = lean_ctor_get(x_18, 2);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_18);
x_132 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_133 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_133, 0, x_96);
lean_ctor_set(x_133, 1, x_97);
lean_ctor_set(x_133, 2, x_132);
lean_ctor_set(x_6, 2, x_133);
x_134 = l_Lean_Meta_assumptionAux___closed__1;
lean_inc(x_1);
x_135 = l_Lean_Meta_checkNotAssigned(x_1, x_134, x_15, x_6);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
lean_inc(x_1);
x_137 = l_Lean_Meta_getMVarType(x_1, x_15, x_136);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
lean_inc(x_15);
x_140 = l_Lean_LocalContext_findDeclRevM___at_Lean_Meta_assumptionAux___spec__1(x_138, x_10, x_15, x_139);
lean_dec(x_10);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; uint8_t x_143; 
lean_dec(x_15);
lean_dec(x_1);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = 0;
x_99 = x_143;
x_100 = x_142;
goto block_115;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_140, 1);
lean_inc(x_144);
lean_dec(x_140);
x_145 = lean_ctor_get(x_141, 0);
lean_inc(x_145);
lean_dec(x_141);
x_146 = l_Lean_Meta_assignExprMVar(x_1, x_145, x_15, x_144);
lean_dec(x_15);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; uint8_t x_148; 
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
lean_dec(x_146);
x_148 = 1;
x_99 = x_148;
x_100 = x_147;
goto block_115;
}
else
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_7);
x_149 = lean_ctor_get(x_146, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_146, 1);
lean_inc(x_150);
lean_dec(x_146);
x_116 = x_149;
x_117 = x_150;
goto block_131;
}
}
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_1);
x_151 = lean_ctor_get(x_140, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_140, 1);
lean_inc(x_152);
lean_dec(x_140);
x_116 = x_151;
x_117 = x_152;
goto block_131;
}
}
else
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_1);
x_153 = lean_ctor_get(x_137, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_137, 1);
lean_inc(x_154);
lean_dec(x_137);
x_116 = x_153;
x_117 = x_154;
goto block_131;
}
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_1);
x_155 = lean_ctor_get(x_135, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_135, 1);
lean_inc(x_156);
lean_dec(x_135);
x_116 = x_155;
x_117 = x_156;
goto block_131;
}
block_115:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_101 = lean_ctor_get(x_100, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_100, 3);
lean_inc(x_104);
x_105 = lean_ctor_get(x_100, 4);
lean_inc(x_105);
x_106 = lean_ctor_get(x_100, 5);
lean_inc(x_106);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 lean_ctor_release(x_100, 2);
 lean_ctor_release(x_100, 3);
 lean_ctor_release(x_100, 4);
 lean_ctor_release(x_100, 5);
 x_107 = x_100;
} else {
 lean_dec_ref(x_100);
 x_107 = lean_box(0);
}
x_108 = lean_ctor_get(x_101, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_101, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 lean_ctor_release(x_101, 2);
 x_110 = x_101;
} else {
 lean_dec_ref(x_101);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(0, 3, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
lean_ctor_set(x_111, 2, x_98);
if (lean_is_scalar(x_107)) {
 x_112 = lean_alloc_ctor(0, 6, 0);
} else {
 x_112 = x_107;
}
lean_ctor_set(x_112, 0, x_102);
lean_ctor_set(x_112, 1, x_103);
lean_ctor_set(x_112, 2, x_111);
lean_ctor_set(x_112, 3, x_104);
lean_ctor_set(x_112, 4, x_105);
lean_ctor_set(x_112, 5, x_106);
x_113 = lean_box(x_99);
if (lean_is_scalar(x_7)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_7;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
block_131:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_118 = lean_ctor_get(x_117, 2);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_117, 3);
lean_inc(x_121);
x_122 = lean_ctor_get(x_117, 4);
lean_inc(x_122);
x_123 = lean_ctor_get(x_117, 5);
lean_inc(x_123);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 lean_ctor_release(x_117, 4);
 lean_ctor_release(x_117, 5);
 x_124 = x_117;
} else {
 lean_dec_ref(x_117);
 x_124 = lean_box(0);
}
x_125 = lean_ctor_get(x_118, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_118, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 x_127 = x_118;
} else {
 lean_dec_ref(x_118);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(0, 3, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
lean_ctor_set(x_128, 2, x_98);
if (lean_is_scalar(x_124)) {
 x_129 = lean_alloc_ctor(0, 6, 0);
} else {
 x_129 = x_124;
}
lean_ctor_set(x_129, 0, x_119);
lean_ctor_set(x_129, 1, x_120);
lean_ctor_set(x_129, 2, x_128);
lean_ctor_set(x_129, 3, x_121);
lean_ctor_set(x_129, 4, x_122);
lean_ctor_set(x_129, 5, x_123);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_116);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_184; lean_object* x_185; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_157 = lean_ctor_get(x_6, 2);
x_158 = lean_ctor_get(x_6, 0);
x_159 = lean_ctor_get(x_6, 1);
x_160 = lean_ctor_get(x_6, 3);
x_161 = lean_ctor_get(x_6, 4);
x_162 = lean_ctor_get(x_6, 5);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_157);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_6);
x_163 = lean_ctor_get(x_157, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_157, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_157, 2);
lean_inc(x_165);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 lean_ctor_release(x_157, 2);
 x_166 = x_157;
} else {
 lean_dec_ref(x_157);
 x_166 = lean_box(0);
}
x_200 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_166)) {
 x_201 = lean_alloc_ctor(0, 3, 0);
} else {
 x_201 = x_166;
}
lean_ctor_set(x_201, 0, x_163);
lean_ctor_set(x_201, 1, x_164);
lean_ctor_set(x_201, 2, x_200);
x_202 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_202, 0, x_158);
lean_ctor_set(x_202, 1, x_159);
lean_ctor_set(x_202, 2, x_201);
lean_ctor_set(x_202, 3, x_160);
lean_ctor_set(x_202, 4, x_161);
lean_ctor_set(x_202, 5, x_162);
x_203 = l_Lean_Meta_assumptionAux___closed__1;
lean_inc(x_1);
x_204 = l_Lean_Meta_checkNotAssigned(x_1, x_203, x_15, x_202);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
lean_dec(x_204);
lean_inc(x_1);
x_206 = l_Lean_Meta_getMVarType(x_1, x_15, x_205);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
lean_inc(x_15);
x_209 = l_Lean_LocalContext_findDeclRevM___at_Lean_Meta_assumptionAux___spec__1(x_207, x_10, x_15, x_208);
lean_dec(x_10);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; uint8_t x_212; 
lean_dec(x_15);
lean_dec(x_1);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = 0;
x_167 = x_212;
x_168 = x_211;
goto block_183;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_209, 1);
lean_inc(x_213);
lean_dec(x_209);
x_214 = lean_ctor_get(x_210, 0);
lean_inc(x_214);
lean_dec(x_210);
x_215 = l_Lean_Meta_assignExprMVar(x_1, x_214, x_15, x_213);
lean_dec(x_15);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; uint8_t x_217; 
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
x_217 = 1;
x_167 = x_217;
x_168 = x_216;
goto block_183;
}
else
{
lean_object* x_218; lean_object* x_219; 
lean_dec(x_7);
x_218 = lean_ctor_get(x_215, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_215, 1);
lean_inc(x_219);
lean_dec(x_215);
x_184 = x_218;
x_185 = x_219;
goto block_199;
}
}
}
else
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_1);
x_220 = lean_ctor_get(x_209, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_209, 1);
lean_inc(x_221);
lean_dec(x_209);
x_184 = x_220;
x_185 = x_221;
goto block_199;
}
}
else
{
lean_object* x_222; lean_object* x_223; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_1);
x_222 = lean_ctor_get(x_206, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_206, 1);
lean_inc(x_223);
lean_dec(x_206);
x_184 = x_222;
x_185 = x_223;
goto block_199;
}
}
else
{
lean_object* x_224; lean_object* x_225; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_1);
x_224 = lean_ctor_get(x_204, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_204, 1);
lean_inc(x_225);
lean_dec(x_204);
x_184 = x_224;
x_185 = x_225;
goto block_199;
}
block_183:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_169 = lean_ctor_get(x_168, 2);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_168, 1);
lean_inc(x_171);
x_172 = lean_ctor_get(x_168, 3);
lean_inc(x_172);
x_173 = lean_ctor_get(x_168, 4);
lean_inc(x_173);
x_174 = lean_ctor_get(x_168, 5);
lean_inc(x_174);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 lean_ctor_release(x_168, 2);
 lean_ctor_release(x_168, 3);
 lean_ctor_release(x_168, 4);
 lean_ctor_release(x_168, 5);
 x_175 = x_168;
} else {
 lean_dec_ref(x_168);
 x_175 = lean_box(0);
}
x_176 = lean_ctor_get(x_169, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_169, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 lean_ctor_release(x_169, 2);
 x_178 = x_169;
} else {
 lean_dec_ref(x_169);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(0, 3, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_177);
lean_ctor_set(x_179, 2, x_165);
if (lean_is_scalar(x_175)) {
 x_180 = lean_alloc_ctor(0, 6, 0);
} else {
 x_180 = x_175;
}
lean_ctor_set(x_180, 0, x_170);
lean_ctor_set(x_180, 1, x_171);
lean_ctor_set(x_180, 2, x_179);
lean_ctor_set(x_180, 3, x_172);
lean_ctor_set(x_180, 4, x_173);
lean_ctor_set(x_180, 5, x_174);
x_181 = lean_box(x_167);
if (lean_is_scalar(x_7)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_7;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
block_199:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_186 = lean_ctor_get(x_185, 2);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_185, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_185, 3);
lean_inc(x_189);
x_190 = lean_ctor_get(x_185, 4);
lean_inc(x_190);
x_191 = lean_ctor_get(x_185, 5);
lean_inc(x_191);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 lean_ctor_release(x_185, 2);
 lean_ctor_release(x_185, 3);
 lean_ctor_release(x_185, 4);
 lean_ctor_release(x_185, 5);
 x_192 = x_185;
} else {
 lean_dec_ref(x_185);
 x_192 = lean_box(0);
}
x_193 = lean_ctor_get(x_186, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_186, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 lean_ctor_release(x_186, 2);
 x_195 = x_186;
} else {
 lean_dec_ref(x_186);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(0, 3, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set(x_196, 1, x_194);
lean_ctor_set(x_196, 2, x_165);
if (lean_is_scalar(x_192)) {
 x_197 = lean_alloc_ctor(0, 6, 0);
} else {
 x_197 = x_192;
}
lean_ctor_set(x_197, 0, x_187);
lean_ctor_set(x_197, 1, x_188);
lean_ctor_set(x_197, 2, x_196);
lean_ctor_set(x_197, 3, x_189);
lean_ctor_set(x_197, 4, x_190);
lean_ctor_set(x_197, 5, x_191);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_184);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
}
else
{
uint8_t x_274; 
lean_dec(x_1);
x_274 = !lean_is_exclusive(x_4);
if (x_274 == 0)
{
return x_4;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_4, 0);
x_276 = lean_ctor_get(x_4, 1);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_4);
x_277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set(x_277, 1, x_276);
return x_277;
}
}
}
}
lean_object* l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_PersistentArray_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_PersistentArray_findRevM___at_Lean_Meta_assumptionAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_findRevM___at_Lean_Meta_assumptionAux___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_LocalContext_findDeclRevM___at_Lean_Meta_assumptionAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_LocalContext_findDeclRevM___at_Lean_Meta_assumptionAux___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_isEqvAux___main___at_Lean_Meta_assumptionAux___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___main___at_Lean_Meta_assumptionAux___spec__7(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__10(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__12(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__13(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_PersistentArray_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_findRevMAux___main___at_Lean_Meta_assumptionAux___spec__11(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_PersistentArray_findRevM___at_Lean_Meta_assumptionAux___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_findRevM___at_Lean_Meta_assumptionAux___spec__9(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_LocalContext_findDeclRevM___at_Lean_Meta_assumptionAux___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_LocalContext_findDeclRevM___at_Lean_Meta_assumptionAux___spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
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
lean_object* x_1; 
x_1 = lean_mk_string("`assumption` failed");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_assumption___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_assumption___closed__1;
x_2 = lean_alloc_ctor(19, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_assumption(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
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
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = l_Lean_Meta_assumption___closed__2;
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = l_Lean_Meta_assumption___closed__2;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_4, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_4, 0, x_15);
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_4);
if (x_19 == 0)
{
return x_4;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_4, 0);
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_4);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
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
l_Lean_Meta_assumption___closed__1 = _init_l_Lean_Meta_assumption___closed__1();
lean_mark_persistent(l_Lean_Meta_assumption___closed__1);
l_Lean_Meta_assumption___closed__2 = _init_l_Lean_Meta_assumption___closed__2();
lean_mark_persistent(l_Lean_Meta_assumption___closed__2);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
