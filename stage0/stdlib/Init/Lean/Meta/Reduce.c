// Lean compiler output
// Module: Init.Lean.Meta.Reduce
// Imports: Init.Lean.Meta.Basic Init.Lean.Meta.FunInfo
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
lean_object* l___private_Init_Lean_Meta_Basic_7__lambdaTelescopeAux___main___at_Lean_Meta_reduceAux___main___spec__3(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduceAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClassExpensive___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__4(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_reduceAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClassQuick___main(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at_Lean_Meta_reduceAux___main___spec__5(uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduceAux___main___spec__2(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_reduceAux___main___spec__1(uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceAux(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__7___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at_Lean_Meta_reduceAux___main___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshId___rarg(lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__6(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__8(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceAux___main(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__7___lambda__1(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_7__lambdaTelescopeAux___main___at_Lean_Meta_reduceAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__7(uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Bool_DecidableEq(uint8_t, uint8_t);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_reduceAux___main___spec__1(uint8_t x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_7, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_7, x_13);
lean_dec(x_7);
x_15 = lean_nat_sub(x_6, x_14);
x_16 = lean_nat_sub(x_15, x_13);
lean_dec(x_15);
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_array_get_size(x_17);
x_19 = lean_nat_dec_lt(x_16, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_array_get_size(x_8);
x_21 = lean_nat_dec_lt(x_16, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_dec(x_16);
x_7 = x_14;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_array_fget(x_8, x_16);
x_24 = l_Lean_Expr_Inhabited___closed__1;
x_25 = lean_array_fset(x_8, x_16, x_24);
lean_inc(x_9);
x_26 = l_Lean_Meta_reduceAux___main(x_1, x_2, x_3, x_23, x_9, x_10);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_array_fset(x_25, x_16, x_27);
lean_dec(x_16);
x_7 = x_14;
x_8 = x_29;
x_10 = x_28;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_25);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_9);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_array_fget(x_17, x_16);
if (x_1 == 0)
{
lean_dec(x_35);
x_36 = x_4;
goto block_55;
}
else
{
uint8_t x_56; 
x_56 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = lean_ctor_get_uint8(x_35, sizeof(void*)*1 + 1);
lean_dec(x_35);
x_36 = x_57;
goto block_55;
}
else
{
lean_dec(x_35);
x_36 = x_1;
goto block_55;
}
}
block_55:
{
uint8_t x_37; uint8_t x_38; 
x_37 = 1;
x_38 = l_Bool_DecidableEq(x_36, x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_array_get_size(x_8);
x_40 = lean_nat_dec_lt(x_16, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_dec(x_16);
x_7 = x_14;
goto _start;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_array_fget(x_8, x_16);
x_43 = l_Lean_Expr_Inhabited___closed__1;
x_44 = lean_array_fset(x_8, x_16, x_43);
lean_inc(x_9);
x_45 = l_Lean_Meta_reduceAux___main(x_1, x_2, x_3, x_42, x_9, x_10);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_array_fset(x_44, x_16, x_46);
lean_dec(x_16);
x_7 = x_14;
x_8 = x_48;
x_10 = x_47;
goto _start;
}
else
{
uint8_t x_50; 
lean_dec(x_44);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_9);
x_50 = !lean_is_exclusive(x_45);
if (x_50 == 0)
{
return x_45;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_45, 0);
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_45);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
lean_dec(x_16);
x_7 = x_14;
goto _start;
}
}
}
}
else
{
lean_object* x_58; 
lean_dec(x_9);
lean_dec(x_7);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_8);
lean_ctor_set(x_58, 1, x_10);
return x_58;
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__4(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_6);
x_11 = lean_nat_dec_lt(x_7, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_7);
lean_inc(x_8);
x_12 = l_Lean_Meta_reduceAux___main(x_1, x_2, x_3, x_5, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_mkLambda(x_4, x_13, x_8, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_fget(x_6, x_7);
lean_inc(x_8);
x_21 = l_Lean_Meta_getFVarLocalDecl(x_20, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_LocalDecl_type(x_22);
lean_dec(x_22);
lean_inc(x_8);
lean_inc(x_24);
x_25 = l_Lean_Meta_isClassQuick___main(x_24, x_8, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_24);
lean_dec(x_20);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_7, x_28);
lean_dec(x_7);
x_7 = x_29;
x_9 = x_27;
goto _start;
}
case 1:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_24);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_7, x_33);
lean_dec(x_7);
x_35 = !lean_is_exclusive(x_8);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_8, 2);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_20);
x_38 = lean_array_push(x_36, x_37);
lean_ctor_set(x_8, 2, x_38);
x_7 = x_34;
x_9 = x_31;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_8, 0);
x_41 = lean_ctor_get(x_8, 1);
x_42 = lean_ctor_get(x_8, 2);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_8);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_32);
lean_ctor_set(x_43, 1, x_20);
x_44 = lean_array_push(x_42, x_43);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_41);
lean_ctor_set(x_45, 2, x_44);
x_7 = x_34;
x_8 = x_45;
x_9 = x_31;
goto _start;
}
}
default: 
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_25, 1);
lean_inc(x_47);
lean_dec(x_25);
lean_inc(x_8);
x_48 = l_Lean_Meta_isClassExpensive___main(x_24, x_8, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_20);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_7, x_51);
lean_dec(x_7);
x_7 = x_52;
x_9 = x_50;
goto _start;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_dec(x_48);
x_55 = lean_ctor_get(x_49, 0);
lean_inc(x_55);
lean_dec(x_49);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_7, x_56);
lean_dec(x_7);
x_58 = !lean_is_exclusive(x_8);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_8, 2);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_20);
x_61 = lean_array_push(x_59, x_60);
lean_ctor_set(x_8, 2, x_61);
x_7 = x_57;
x_9 = x_54;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_8, 0);
x_64 = lean_ctor_get(x_8, 1);
x_65 = lean_ctor_get(x_8, 2);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_8);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_20);
x_67 = lean_array_push(x_65, x_66);
x_68 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_64);
lean_ctor_set(x_68, 2, x_67);
x_7 = x_57;
x_8 = x_68;
x_9 = x_54;
goto _start;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_70 = !lean_is_exclusive(x_48);
if (x_70 == 0)
{
return x_48;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_48, 0);
x_72 = lean_ctor_get(x_48, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_48);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_74 = !lean_is_exclusive(x_25);
if (x_74 == 0)
{
return x_25;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_25, 0);
x_76 = lean_ctor_get(x_25, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_25);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_78 = !lean_is_exclusive(x_21);
if (x_78 == 0)
{
return x_21;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_21, 0);
x_80 = lean_ctor_get(x_21, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_21);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_Basic_7__lambdaTelescopeAux___main___at_Lean_Meta_reduceAux___main___spec__3(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
switch (lean_obj_tag(x_7)) {
case 6:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_21 = lean_ctor_get(x_7, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_7, 2);
lean_inc(x_23);
x_24 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
lean_dec(x_7);
x_25 = lean_array_get_size(x_5);
lean_inc(x_5);
x_26 = lean_expr_instantiate_rev_range(x_22, x_6, x_25, x_5);
lean_dec(x_25);
lean_dec(x_22);
x_27 = l_Lean_Meta_mkFreshId___rarg(x_9);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = (uint8_t)((x_24 << 24) >> 61);
lean_inc(x_28);
x_31 = lean_local_ctx_mk_local_decl(x_4, x_28, x_21, x_26, x_30);
x_32 = l_Lean_mkFVar(x_28);
x_33 = lean_array_push(x_5, x_32);
x_4 = x_31;
x_5 = x_33;
x_7 = x_23;
x_9 = x_29;
goto _start;
}
case 8:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_35 = lean_ctor_get(x_7, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_7, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_7, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_7, 3);
lean_inc(x_38);
lean_dec(x_7);
x_39 = lean_array_get_size(x_5);
lean_inc(x_5);
x_40 = lean_expr_instantiate_rev_range(x_36, x_6, x_39, x_5);
lean_dec(x_36);
lean_inc(x_5);
x_41 = lean_expr_instantiate_rev_range(x_37, x_6, x_39, x_5);
lean_dec(x_39);
lean_dec(x_37);
x_42 = l_Lean_Meta_mkFreshId___rarg(x_9);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_43);
x_45 = lean_local_ctx_mk_let_decl(x_4, x_43, x_35, x_40, x_41);
x_46 = l_Lean_mkFVar(x_43);
x_47 = lean_array_push(x_5, x_46);
x_4 = x_45;
x_5 = x_47;
x_7 = x_38;
x_9 = x_44;
goto _start;
}
default: 
{
lean_object* x_49; 
x_49 = lean_box(0);
x_10 = x_49;
goto block_20;
}
}
block_20:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_10);
x_11 = lean_array_get_size(x_5);
lean_inc(x_5);
x_12 = lean_expr_instantiate_rev_range(x_7, x_6, x_11, x_5);
lean_dec(x_11);
lean_dec(x_7);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_8, 1);
lean_dec(x_14);
lean_ctor_set(x_8, 1, x_4);
lean_inc(x_5);
x_15 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__4(x_1, x_2, x_3, x_5, x_12, x_5, x_6, x_8, x_9);
lean_dec(x_5);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 2);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_4);
lean_ctor_set(x_18, 2, x_17);
lean_inc(x_5);
x_19 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__4(x_1, x_2, x_3, x_5, x_12, x_5, x_6, x_18, x_9);
lean_dec(x_5);
return x_19;
}
}
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduceAux___main___spec__2(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = l_Array_empty___closed__1;
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Init_Lean_Meta_Basic_7__lambdaTelescopeAux___main___at_Lean_Meta_reduceAux___main___spec__3(x_1, x_2, x_3, x_8, x_9, x_10, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 2);
lean_dec(x_15);
lean_ctor_set(x_13, 2, x_7);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_ctor_get(x_13, 3);
x_19 = lean_ctor_get(x_13, 4);
x_20 = lean_ctor_get(x_13, 5);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_13);
x_21 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_7);
lean_ctor_set(x_21, 3, x_18);
lean_ctor_set(x_21, 4, x_19);
lean_ctor_set(x_21, 5, x_20);
lean_ctor_set(x_11, 1, x_21);
return x_11;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_11, 1);
x_23 = lean_ctor_get(x_11, 0);
lean_inc(x_22);
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_22, 4);
lean_inc(x_27);
x_28 = lean_ctor_get(x_22, 5);
lean_inc(x_28);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 lean_ctor_release(x_22, 3);
 lean_ctor_release(x_22, 4);
 lean_ctor_release(x_22, 5);
 x_29 = x_22;
} else {
 lean_dec_ref(x_22);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 6, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set(x_30, 2, x_7);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set(x_30, 4, x_27);
lean_ctor_set(x_30, 5, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_23);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_11);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_11, 1);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 2);
lean_dec(x_35);
lean_ctor_set(x_33, 2, x_7);
return x_11;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_33, 0);
x_37 = lean_ctor_get(x_33, 1);
x_38 = lean_ctor_get(x_33, 3);
x_39 = lean_ctor_get(x_33, 4);
x_40 = lean_ctor_get(x_33, 5);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_33);
x_41 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set(x_41, 2, x_7);
lean_ctor_set(x_41, 3, x_38);
lean_ctor_set(x_41, 4, x_39);
lean_ctor_set(x_41, 5, x_40);
lean_ctor_set(x_11, 1, x_41);
return x_11;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get(x_11, 1);
x_43 = lean_ctor_get(x_11, 0);
lean_inc(x_42);
lean_inc(x_43);
lean_dec(x_11);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_42, 3);
lean_inc(x_46);
x_47 = lean_ctor_get(x_42, 4);
lean_inc(x_47);
x_48 = lean_ctor_get(x_42, 5);
lean_inc(x_48);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 lean_ctor_release(x_42, 4);
 lean_ctor_release(x_42, 5);
 x_49 = x_42;
} else {
 lean_dec_ref(x_42);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 6, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_45);
lean_ctor_set(x_50, 2, x_7);
lean_ctor_set(x_50, 3, x_46);
lean_ctor_set(x_50, 4, x_47);
lean_ctor_set(x_50, 5, x_48);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__6(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_6);
x_11 = lean_nat_dec_lt(x_7, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_7);
lean_inc(x_8);
x_12 = l_Lean_Meta_reduceAux___main(x_1, x_2, x_3, x_5, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_mkForall(x_4, x_13, x_8, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_fget(x_6, x_7);
lean_inc(x_8);
x_21 = l_Lean_Meta_getFVarLocalDecl(x_20, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_LocalDecl_type(x_22);
lean_dec(x_22);
lean_inc(x_8);
lean_inc(x_24);
x_25 = l_Lean_Meta_isClassQuick___main(x_24, x_8, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_24);
lean_dec(x_20);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_7, x_28);
lean_dec(x_7);
x_7 = x_29;
x_9 = x_27;
goto _start;
}
case 1:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_24);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_7, x_33);
lean_dec(x_7);
x_35 = !lean_is_exclusive(x_8);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_8, 2);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_20);
x_38 = lean_array_push(x_36, x_37);
lean_ctor_set(x_8, 2, x_38);
x_7 = x_34;
x_9 = x_31;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_8, 0);
x_41 = lean_ctor_get(x_8, 1);
x_42 = lean_ctor_get(x_8, 2);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_8);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_32);
lean_ctor_set(x_43, 1, x_20);
x_44 = lean_array_push(x_42, x_43);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_41);
lean_ctor_set(x_45, 2, x_44);
x_7 = x_34;
x_8 = x_45;
x_9 = x_31;
goto _start;
}
}
default: 
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_25, 1);
lean_inc(x_47);
lean_dec(x_25);
lean_inc(x_8);
x_48 = l_Lean_Meta_isClassExpensive___main(x_24, x_8, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_20);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_7, x_51);
lean_dec(x_7);
x_7 = x_52;
x_9 = x_50;
goto _start;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_dec(x_48);
x_55 = lean_ctor_get(x_49, 0);
lean_inc(x_55);
lean_dec(x_49);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_7, x_56);
lean_dec(x_7);
x_58 = !lean_is_exclusive(x_8);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_8, 2);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_20);
x_61 = lean_array_push(x_59, x_60);
lean_ctor_set(x_8, 2, x_61);
x_7 = x_57;
x_9 = x_54;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_8, 0);
x_64 = lean_ctor_get(x_8, 1);
x_65 = lean_ctor_get(x_8, 2);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_8);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_20);
x_67 = lean_array_push(x_65, x_66);
x_68 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_64);
lean_ctor_set(x_68, 2, x_67);
x_7 = x_57;
x_8 = x_68;
x_9 = x_54;
goto _start;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_70 = !lean_is_exclusive(x_48);
if (x_70 == 0)
{
return x_48;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_48, 0);
x_72 = lean_ctor_get(x_48, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_48);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_74 = !lean_is_exclusive(x_25);
if (x_74 == 0)
{
return x_25;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_25, 0);
x_76 = lean_ctor_get(x_25, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_25);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_78 = !lean_is_exclusive(x_21);
if (x_78 == 0)
{
return x_21;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_21, 0);
x_80 = lean_ctor_get(x_21, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_21);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__7___lambda__1(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; 
x_13 = l_Lean_Expr_isForall(x_10);
x_14 = 1;
x_15 = l_Bool_DecidableEq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_inc(x_11);
x_16 = l_Lean_Meta_reduceAux___main(x_1, x_2, x_3, x_4, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_mkForall(x_5, x_17, x_11, x_18);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_11);
lean_dec(x_5);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; 
lean_dec(x_4);
x_24 = l___private_Init_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at_Lean_Meta_reduceAux___main___spec__5(x_1, x_2, x_3, x_6, x_7, x_8, x_5, x_9, x_10, x_11, x_12);
return x_24;
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__7(uint8_t x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_inc(x_11);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_whnf), 3, 1);
lean_closure_set(x_16, 0, x_11);
x_17 = lean_box(x_1);
x_18 = lean_box(x_2);
x_19 = lean_box(x_3);
x_20 = lean_box(x_4);
lean_inc(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_7);
lean_inc(x_11);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__7___lambda__1___boxed), 12, 9);
lean_closure_set(x_21, 0, x_17);
lean_closure_set(x_21, 1, x_18);
lean_closure_set(x_21, 2, x_19);
lean_closure_set(x_21, 3, x_11);
lean_closure_set(x_21, 4, x_7);
lean_closure_set(x_21, 5, x_20);
lean_closure_set(x_21, 6, x_5);
lean_closure_set(x_21, 7, x_6);
lean_closure_set(x_21, 8, x_10);
x_22 = lean_array_get_size(x_12);
x_23 = lean_nat_dec_lt(x_13, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_24 = l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(x_16, x_21, x_14, x_15);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_16);
x_25 = lean_array_fget(x_12, x_13);
lean_inc(x_14);
x_26 = l_Lean_Meta_getFVarLocalDecl(x_25, x_14, x_15);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_LocalDecl_type(x_27);
lean_dec(x_27);
lean_inc(x_14);
lean_inc(x_29);
x_30 = l_Lean_Meta_isClassQuick___main(x_29, x_14, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
switch (lean_obj_tag(x_31)) {
case 0:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_29);
lean_dec(x_25);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_13, x_33);
lean_dec(x_13);
x_13 = x_34;
x_15 = x_32;
goto _start;
}
case 1:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_29);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_13, x_38);
lean_dec(x_13);
x_40 = !lean_is_exclusive(x_14);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_14, 2);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_25);
x_43 = lean_array_push(x_41, x_42);
lean_ctor_set(x_14, 2, x_43);
x_13 = x_39;
x_15 = x_36;
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_14, 0);
x_46 = lean_ctor_get(x_14, 1);
x_47 = lean_ctor_get(x_14, 2);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_14);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_37);
lean_ctor_set(x_48, 1, x_25);
x_49 = lean_array_push(x_47, x_48);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_46);
lean_ctor_set(x_50, 2, x_49);
x_13 = x_39;
x_14 = x_50;
x_15 = x_36;
goto _start;
}
}
default: 
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_30, 1);
lean_inc(x_52);
lean_dec(x_30);
lean_inc(x_14);
x_53 = l_Lean_Meta_isClassExpensive___main(x_29, x_14, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_25);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_13, x_56);
lean_dec(x_13);
x_13 = x_57;
x_15 = x_55;
goto _start;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
lean_dec(x_53);
x_60 = lean_ctor_get(x_54, 0);
lean_inc(x_60);
lean_dec(x_54);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_13, x_61);
lean_dec(x_13);
x_63 = !lean_is_exclusive(x_14);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_14, 2);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_25);
x_66 = lean_array_push(x_64, x_65);
lean_ctor_set(x_14, 2, x_66);
x_13 = x_62;
x_15 = x_59;
goto _start;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_14, 0);
x_69 = lean_ctor_get(x_14, 1);
x_70 = lean_ctor_get(x_14, 2);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_14);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_60);
lean_ctor_set(x_71, 1, x_25);
x_72 = lean_array_push(x_70, x_71);
x_73 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_73, 0, x_68);
lean_ctor_set(x_73, 1, x_69);
lean_ctor_set(x_73, 2, x_72);
x_13 = x_62;
x_14 = x_73;
x_15 = x_59;
goto _start;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_75 = !lean_is_exclusive(x_53);
if (x_75 == 0)
{
return x_53;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_53, 0);
x_77 = lean_ctor_get(x_53, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_79 = !lean_is_exclusive(x_30);
if (x_79 == 0)
{
return x_30;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_30, 0);
x_81 = lean_ctor_get(x_30, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_30);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_83 = !lean_is_exclusive(x_26);
if (x_83 == 0)
{
return x_26;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_26, 0);
x_85 = lean_ctor_get(x_26, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_26);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__8(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_6);
x_11 = lean_nat_dec_lt(x_7, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_7);
lean_inc(x_8);
x_12 = l_Lean_Meta_reduceAux___main(x_1, x_2, x_3, x_5, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_mkForall(x_4, x_13, x_8, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_fget(x_6, x_7);
lean_inc(x_8);
x_21 = l_Lean_Meta_getFVarLocalDecl(x_20, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_LocalDecl_type(x_22);
lean_dec(x_22);
lean_inc(x_8);
lean_inc(x_24);
x_25 = l_Lean_Meta_isClassQuick___main(x_24, x_8, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_24);
lean_dec(x_20);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_7, x_28);
lean_dec(x_7);
x_7 = x_29;
x_9 = x_27;
goto _start;
}
case 1:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_24);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_7, x_33);
lean_dec(x_7);
x_35 = !lean_is_exclusive(x_8);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_8, 2);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_20);
x_38 = lean_array_push(x_36, x_37);
lean_ctor_set(x_8, 2, x_38);
x_7 = x_34;
x_9 = x_31;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_8, 0);
x_41 = lean_ctor_get(x_8, 1);
x_42 = lean_ctor_get(x_8, 2);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_8);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_32);
lean_ctor_set(x_43, 1, x_20);
x_44 = lean_array_push(x_42, x_43);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_41);
lean_ctor_set(x_45, 2, x_44);
x_7 = x_34;
x_8 = x_45;
x_9 = x_31;
goto _start;
}
}
default: 
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_25, 1);
lean_inc(x_47);
lean_dec(x_25);
lean_inc(x_8);
x_48 = l_Lean_Meta_isClassExpensive___main(x_24, x_8, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_20);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_7, x_51);
lean_dec(x_7);
x_7 = x_52;
x_9 = x_50;
goto _start;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_dec(x_48);
x_55 = lean_ctor_get(x_49, 0);
lean_inc(x_55);
lean_dec(x_49);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_7, x_56);
lean_dec(x_7);
x_58 = !lean_is_exclusive(x_8);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_8, 2);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_20);
x_61 = lean_array_push(x_59, x_60);
lean_ctor_set(x_8, 2, x_61);
x_7 = x_57;
x_9 = x_54;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_8, 0);
x_64 = lean_ctor_get(x_8, 1);
x_65 = lean_ctor_get(x_8, 2);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_8);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_20);
x_67 = lean_array_push(x_65, x_66);
x_68 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_64);
lean_ctor_set(x_68, 2, x_67);
x_7 = x_57;
x_8 = x_68;
x_9 = x_54;
goto _start;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_70 = !lean_is_exclusive(x_48);
if (x_70 == 0)
{
return x_48;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_48, 0);
x_72 = lean_ctor_get(x_48, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_48);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_74 = !lean_is_exclusive(x_25);
if (x_74 == 0)
{
return x_25;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_25, 0);
x_76 = lean_ctor_get(x_25, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_25);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_78 = !lean_is_exclusive(x_21);
if (x_78 == 0)
{
return x_21;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_21, 0);
x_80 = lean_ctor_get(x_21, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_21);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at_Lean_Meta_reduceAux___main___spec__5(uint8_t x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
if (lean_obj_tag(x_9) == 7)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get(x_9, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_9, 2);
lean_inc(x_29);
x_30 = lean_ctor_get_uint64(x_9, sizeof(void*)*3);
lean_dec(x_9);
x_31 = lean_array_get_size(x_7);
lean_inc(x_7);
x_32 = lean_expr_instantiate_rev_range(x_28, x_8, x_31, x_7);
lean_dec(x_31);
lean_dec(x_28);
x_33 = l_Lean_Meta_mkFreshId___rarg(x_11);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = (uint8_t)((x_30 << 24) >> 61);
lean_inc(x_34);
x_37 = lean_local_ctx_mk_local_decl(x_6, x_34, x_27, x_32, x_36);
x_38 = l_Lean_mkFVar(x_34);
x_39 = lean_array_push(x_7, x_38);
if (lean_obj_tag(x_5) == 0)
{
x_6 = x_37;
x_7 = x_39;
x_9 = x_29;
x_11 = x_35;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_5, 0);
lean_inc(x_41);
x_42 = lean_array_get_size(x_39);
x_43 = lean_nat_dec_lt(x_42, x_41);
lean_dec(x_41);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
lean_dec(x_5);
lean_inc(x_39);
x_44 = lean_expr_instantiate_rev_range(x_29, x_8, x_42, x_39);
lean_dec(x_42);
lean_dec(x_29);
x_45 = !lean_is_exclusive(x_10);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_10, 1);
lean_dec(x_46);
lean_ctor_set(x_10, 1, x_37);
lean_inc(x_39);
x_47 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__8(x_1, x_2, x_3, x_39, x_44, x_39, x_8, x_10, x_35);
lean_dec(x_39);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_10, 0);
x_49 = lean_ctor_get(x_10, 2);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_10);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_37);
lean_ctor_set(x_50, 2, x_49);
lean_inc(x_39);
x_51 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__8(x_1, x_2, x_3, x_39, x_44, x_39, x_8, x_50, x_35);
lean_dec(x_39);
return x_51;
}
}
else
{
lean_dec(x_42);
x_6 = x_37;
x_7 = x_39;
x_9 = x_29;
x_11 = x_35;
goto _start;
}
}
}
else
{
lean_object* x_53; 
x_53 = lean_box(0);
x_12 = x_53;
goto block_26;
}
block_26:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; 
lean_dec(x_12);
x_13 = lean_array_get_size(x_7);
lean_inc(x_7);
x_14 = lean_expr_instantiate_rev_range(x_9, x_8, x_13, x_7);
x_15 = 1;
x_16 = l_Bool_DecidableEq(x_4, x_15);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_10, 1);
lean_dec(x_18);
lean_inc(x_6);
lean_ctor_set(x_10, 1, x_6);
if (x_16 == 0)
{
lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_inc(x_7);
x_19 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__6(x_1, x_2, x_3, x_7, x_14, x_7, x_8, x_10, x_11);
lean_dec(x_7);
return x_19;
}
else
{
lean_object* x_20; 
lean_inc(x_8);
lean_inc(x_7);
x_20 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13, x_14, x_7, x_8, x_10, x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 2);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
lean_inc(x_6);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_22);
if (x_16 == 0)
{
lean_object* x_24; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_inc(x_7);
x_24 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__6(x_1, x_2, x_3, x_7, x_14, x_7, x_8, x_23, x_11);
lean_dec(x_7);
return x_24;
}
else
{
lean_object* x_25; 
lean_inc(x_8);
lean_inc(x_7);
x_25 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13, x_14, x_7, x_8, x_23, x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_25;
}
}
}
}
}
lean_object* l_Lean_Meta_reduceAux___main(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
if (x_2 == 0)
{
if (x_3 == 0)
{
x_7 = x_3;
x_8 = x_6;
goto block_99;
}
else
{
lean_object* x_100; 
lean_inc(x_5);
lean_inc(x_4);
x_100 = l_Lean_Meta_isProof(x_4, x_5, x_6);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_unbox(x_101);
lean_dec(x_101);
x_7 = x_103;
x_8 = x_102;
goto block_99;
}
else
{
uint8_t x_104; 
lean_dec(x_5);
lean_dec(x_4);
x_104 = !lean_is_exclusive(x_100);
if (x_104 == 0)
{
return x_100;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_100, 0);
x_106 = lean_ctor_get(x_100, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_100);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
else
{
lean_object* x_108; 
lean_inc(x_5);
lean_inc(x_4);
x_108 = l_Lean_Meta_isType(x_4, x_5, x_6);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_unbox(x_109);
lean_dec(x_109);
if (x_110 == 0)
{
if (x_3 == 0)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_dec(x_108);
x_7 = x_3;
x_8 = x_111;
goto block_99;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_108, 1);
lean_inc(x_112);
lean_dec(x_108);
lean_inc(x_5);
lean_inc(x_4);
x_113 = l_Lean_Meta_isProof(x_4, x_5, x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_unbox(x_114);
lean_dec(x_114);
x_7 = x_116;
x_8 = x_115;
goto block_99;
}
else
{
uint8_t x_117; 
lean_dec(x_5);
lean_dec(x_4);
x_117 = !lean_is_exclusive(x_113);
if (x_117 == 0)
{
return x_113;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_113, 0);
x_119 = lean_ctor_get(x_113, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_113);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_5);
x_121 = !lean_is_exclusive(x_108);
if (x_121 == 0)
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_108, 0);
lean_dec(x_122);
lean_ctor_set(x_108, 0, x_4);
return x_108;
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_108, 1);
lean_inc(x_123);
lean_dec(x_108);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_4);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_5);
lean_dec(x_4);
x_125 = !lean_is_exclusive(x_108);
if (x_125 == 0)
{
return x_108;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_108, 0);
x_127 = lean_ctor_get(x_108, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_108);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
block_99:
{
if (x_7 == 0)
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = l_Lean_Meta_whnf(x_4, x_5, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
switch (lean_obj_tag(x_10)) {
case 5:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Expr_getAppFn___main(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Expr_getAppNumArgsAux___main(x_10, x_13);
lean_inc(x_5);
lean_inc(x_14);
lean_inc(x_12);
x_15 = l_Lean_Meta_getFunInfoNArgs(x_12, x_14, x_5, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_14);
x_19 = lean_mk_array(x_14, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_14, x_20);
lean_dec(x_14);
x_22 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_10, x_19, x_21);
x_23 = lean_array_get_size(x_22);
lean_inc(x_23);
x_24 = l_Nat_foldMAux___main___at_Lean_Meta_reduceAux___main___spec__1(x_1, x_2, x_3, x_7, x_16, x_23, x_23, x_22, x_5, x_17);
lean_dec(x_23);
lean_dec(x_16);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_26, x_26, x_13, x_12);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
x_30 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_28, x_28, x_13, x_12);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_12);
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
return x_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_5);
x_36 = !lean_is_exclusive(x_15);
if (x_36 == 0)
{
return x_15;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_15, 0);
x_38 = lean_ctor_get(x_15, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_15);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
case 6:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_9, 1);
lean_inc(x_40);
lean_dec(x_9);
x_41 = l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduceAux___main___spec__2(x_1, x_2, x_3, x_10, x_5, x_40);
return x_41;
}
case 7:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_9, 1);
lean_inc(x_42);
lean_dec(x_9);
x_43 = lean_ctor_get(x_42, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_5, 1);
lean_inc(x_44);
x_45 = lean_box(0);
x_46 = 0;
x_47 = l_Array_empty___closed__1;
x_48 = lean_unsigned_to_nat(0u);
x_49 = l___private_Init_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at_Lean_Meta_reduceAux___main___spec__5(x_1, x_2, x_3, x_46, x_45, x_44, x_47, x_48, x_10, x_5, x_42);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_49, 1);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 2);
lean_dec(x_53);
lean_ctor_set(x_51, 2, x_43);
return x_49;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_51, 0);
x_55 = lean_ctor_get(x_51, 1);
x_56 = lean_ctor_get(x_51, 3);
x_57 = lean_ctor_get(x_51, 4);
x_58 = lean_ctor_get(x_51, 5);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_51);
x_59 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_55);
lean_ctor_set(x_59, 2, x_43);
lean_ctor_set(x_59, 3, x_56);
lean_ctor_set(x_59, 4, x_57);
lean_ctor_set(x_59, 5, x_58);
lean_ctor_set(x_49, 1, x_59);
return x_49;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_60 = lean_ctor_get(x_49, 1);
x_61 = lean_ctor_get(x_49, 0);
lean_inc(x_60);
lean_inc(x_61);
lean_dec(x_49);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_60, 3);
lean_inc(x_64);
x_65 = lean_ctor_get(x_60, 4);
lean_inc(x_65);
x_66 = lean_ctor_get(x_60, 5);
lean_inc(x_66);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 lean_ctor_release(x_60, 2);
 lean_ctor_release(x_60, 3);
 lean_ctor_release(x_60, 4);
 lean_ctor_release(x_60, 5);
 x_67 = x_60;
} else {
 lean_dec_ref(x_60);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 6, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_63);
lean_ctor_set(x_68, 2, x_43);
lean_ctor_set(x_68, 3, x_64);
lean_ctor_set(x_68, 4, x_65);
lean_ctor_set(x_68, 5, x_66);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_49);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_49, 1);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_71, 2);
lean_dec(x_73);
lean_ctor_set(x_71, 2, x_43);
return x_49;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_71, 0);
x_75 = lean_ctor_get(x_71, 1);
x_76 = lean_ctor_get(x_71, 3);
x_77 = lean_ctor_get(x_71, 4);
x_78 = lean_ctor_get(x_71, 5);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_71);
x_79 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_79, 0, x_74);
lean_ctor_set(x_79, 1, x_75);
lean_ctor_set(x_79, 2, x_43);
lean_ctor_set(x_79, 3, x_76);
lean_ctor_set(x_79, 4, x_77);
lean_ctor_set(x_79, 5, x_78);
lean_ctor_set(x_49, 1, x_79);
return x_49;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_80 = lean_ctor_get(x_49, 1);
x_81 = lean_ctor_get(x_49, 0);
lean_inc(x_80);
lean_inc(x_81);
lean_dec(x_49);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_80, 3);
lean_inc(x_84);
x_85 = lean_ctor_get(x_80, 4);
lean_inc(x_85);
x_86 = lean_ctor_get(x_80, 5);
lean_inc(x_86);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 lean_ctor_release(x_80, 2);
 lean_ctor_release(x_80, 3);
 lean_ctor_release(x_80, 4);
 lean_ctor_release(x_80, 5);
 x_87 = x_80;
} else {
 lean_dec_ref(x_80);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(0, 6, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_82);
lean_ctor_set(x_88, 1, x_83);
lean_ctor_set(x_88, 2, x_43);
lean_ctor_set(x_88, 3, x_84);
lean_ctor_set(x_88, 4, x_85);
lean_ctor_set(x_88, 5, x_86);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_81);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
default: 
{
uint8_t x_90; 
lean_dec(x_5);
x_90 = !lean_is_exclusive(x_9);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_9, 0);
lean_dec(x_91);
return x_9;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_9, 1);
lean_inc(x_92);
lean_dec(x_9);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_10);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_5);
x_94 = !lean_is_exclusive(x_9);
if (x_94 == 0)
{
return x_9;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_9, 0);
x_96 = lean_ctor_get(x_9, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_9);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; 
lean_dec(x_5);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_4);
lean_ctor_set(x_98, 1, x_8);
return x_98;
}
}
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_reduceAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Nat_foldMAux___main___at_Lean_Meta_reduceAux___main___spec__1(x_11, x_12, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__4(x_10, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_13;
}
}
lean_object* l___private_Init_Lean_Meta_Basic_7__lambdaTelescopeAux___main___at_Lean_Meta_reduceAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l___private_Init_Lean_Meta_Basic_7__lambdaTelescopeAux___main___at_Lean_Meta_reduceAux___main___spec__3(x_10, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduceAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduceAux___main___spec__2(x_7, x_8, x_9, x_4, x_5, x_6);
return x_10;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__6(x_10, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_13;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__7___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = lean_unbox(x_6);
lean_dec(x_6);
x_17 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__7___lambda__1(x_13, x_14, x_15, x_4, x_5, x_16, x_7, x_8, x_9, x_10, x_11, x_12);
return x_17;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_unbox(x_1);
lean_dec(x_1);
x_17 = lean_unbox(x_2);
lean_dec(x_2);
x_18 = lean_unbox(x_3);
lean_dec(x_3);
x_19 = lean_unbox(x_4);
lean_dec(x_4);
x_20 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__7(x_16, x_17, x_18, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
return x_20;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_reduceAux___main___spec__8(x_10, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_13;
}
}
lean_object* l___private_Init_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at_Lean_Meta_reduceAux___main___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l___private_Init_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at_Lean_Meta_reduceAux___main___spec__5(x_12, x_13, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
}
lean_object* l_Lean_Meta_reduceAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_reduceAux___main(x_7, x_8, x_9, x_4, x_5, x_6);
return x_10;
}
}
lean_object* l_Lean_Meta_reduceAux(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_reduceAux___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_reduceAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_reduceAux(x_7, x_8, x_9, x_4, x_5, x_6);
return x_10;
}
}
lean_object* l_Lean_Meta_reduce(lean_object* x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_reduceAux___main(x_2, x_3, x_4, x_1, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_reduce___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lean_Meta_reduce(x_1, x_7, x_8, x_9, x_5, x_6);
return x_10;
}
}
lean_object* initialize_Init_Lean_Meta_Basic(lean_object*);
lean_object* initialize_Init_Lean_Meta_FunInfo(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_Reduce(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Meta_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_FunInfo(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
