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
lean_object* l_Lean_Meta_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_reduceAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_forallTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Meta_reduceAux___main___lambda__1(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_reduceAux___main___spec__1(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceAux___main___lambda__2(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceAux(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceAux___main___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceAux___main___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceAux___main(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_reduceAux___main___spec__1(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_6, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_6, x_12);
lean_dec(x_6);
x_14 = lean_nat_sub(x_5, x_13);
x_15 = lean_nat_sub(x_14, x_12);
lean_dec(x_14);
x_33 = lean_ctor_get(x_4, 0);
x_34 = lean_array_get_size(x_33);
x_35 = lean_nat_dec_lt(x_15, x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_array_get_size(x_7);
x_37 = lean_nat_dec_lt(x_15, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_dec(x_15);
x_6 = x_13;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_array_fget(x_7, x_15);
x_40 = l_Lean_Expr_Inhabited___closed__1;
x_41 = lean_array_fset(x_7, x_15, x_40);
lean_inc(x_8);
x_42 = l_Lean_Meta_reduceAux___main(x_1, x_2, x_3, x_39, x_8, x_9);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_array_fset(x_41, x_15, x_43);
lean_dec(x_15);
x_6 = x_13;
x_7 = x_45;
x_9 = x_44;
goto _start;
}
else
{
uint8_t x_47; 
lean_dec(x_41);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
x_47 = !lean_is_exclusive(x_42);
if (x_47 == 0)
{
return x_42;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_42, 0);
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_42);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
else
{
if (x_1 == 0)
{
lean_object* x_51; 
x_51 = lean_box(0);
x_16 = x_51;
goto block_32;
}
else
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_array_fget(x_33, x_15);
x_53 = lean_ctor_get_uint8(x_52, sizeof(void*)*1);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = lean_ctor_get_uint8(x_52, sizeof(void*)*1 + 1);
lean_dec(x_52);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_box(0);
x_16 = x_55;
goto block_32;
}
else
{
lean_dec(x_15);
x_6 = x_13;
goto _start;
}
}
else
{
lean_dec(x_52);
lean_dec(x_15);
x_6 = x_13;
goto _start;
}
}
}
block_32:
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_16);
x_17 = lean_array_get_size(x_7);
x_18 = lean_nat_dec_lt(x_15, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_dec(x_15);
x_6 = x_13;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_array_fget(x_7, x_15);
x_21 = l_Lean_Expr_Inhabited___closed__1;
x_22 = lean_array_fset(x_7, x_15, x_21);
lean_inc(x_8);
x_23 = l_Lean_Meta_reduceAux___main(x_1, x_2, x_3, x_20, x_8, x_9);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_array_fset(x_22, x_15, x_24);
lean_dec(x_15);
x_6 = x_13;
x_7 = x_26;
x_9 = x_25;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
else
{
lean_object* x_58; 
lean_dec(x_8);
lean_dec(x_6);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_7);
lean_ctor_set(x_58, 1, x_9);
return x_58;
}
}
}
lean_object* l_Lean_Meta_reduceAux___main___lambda__1(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
x_8 = l_Lean_Meta_reduceAux___main(x_1, x_2, x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_mkLambda(x_4, x_9, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_4);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l_Lean_Meta_reduceAux___main___lambda__2(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
x_8 = l_Lean_Meta_reduceAux___main(x_1, x_2, x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_mkForall(x_4, x_9, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_4);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
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
goto block_61;
}
else
{
lean_object* x_62; 
lean_inc(x_5);
lean_inc(x_4);
x_62 = l_Lean_Meta_isProof(x_4, x_5, x_6);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_unbox(x_63);
lean_dec(x_63);
x_7 = x_65;
x_8 = x_64;
goto block_61;
}
else
{
uint8_t x_66; 
lean_dec(x_5);
lean_dec(x_4);
x_66 = !lean_is_exclusive(x_62);
if (x_66 == 0)
{
return x_62;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_62, 0);
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_62);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
else
{
lean_object* x_70; 
lean_inc(x_5);
lean_inc(x_4);
x_70 = l_Lean_Meta_isType(x_4, x_5, x_6);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
if (x_3 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_7 = x_3;
x_8 = x_73;
goto block_61;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_70, 1);
lean_inc(x_74);
lean_dec(x_70);
lean_inc(x_5);
lean_inc(x_4);
x_75 = l_Lean_Meta_isProof(x_4, x_5, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_unbox(x_76);
lean_dec(x_76);
x_7 = x_78;
x_8 = x_77;
goto block_61;
}
else
{
uint8_t x_79; 
lean_dec(x_5);
lean_dec(x_4);
x_79 = !lean_is_exclusive(x_75);
if (x_79 == 0)
{
return x_75;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_75, 0);
x_81 = lean_ctor_get(x_75, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_75);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_5);
x_83 = !lean_is_exclusive(x_70);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_70, 0);
lean_dec(x_84);
lean_ctor_set(x_70, 0, x_4);
return x_70;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_70, 1);
lean_inc(x_85);
lean_dec(x_70);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_4);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_5);
lean_dec(x_4);
x_87 = !lean_is_exclusive(x_70);
if (x_87 == 0)
{
return x_70;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_70, 0);
x_89 = lean_ctor_get(x_70, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_70);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
block_61:
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
x_24 = l_Nat_foldMAux___main___at_Lean_Meta_reduceAux___main___spec__1(x_1, x_2, x_3, x_16, x_23, x_23, x_22, x_5, x_17);
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
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_9, 1);
lean_inc(x_40);
lean_dec(x_9);
x_41 = lean_box(x_1);
x_42 = lean_box(x_2);
x_43 = lean_box(x_3);
x_44 = lean_alloc_closure((void*)(l_Lean_Meta_reduceAux___main___lambda__1___boxed), 7, 3);
lean_closure_set(x_44, 0, x_41);
lean_closure_set(x_44, 1, x_42);
lean_closure_set(x_44, 2, x_43);
x_45 = l_Lean_Meta_lambdaTelescope___rarg(x_10, x_44, x_5, x_40);
return x_45;
}
case 7:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_9, 1);
lean_inc(x_46);
lean_dec(x_9);
x_47 = lean_box(x_1);
x_48 = lean_box(x_2);
x_49 = lean_box(x_3);
x_50 = lean_alloc_closure((void*)(l_Lean_Meta_reduceAux___main___lambda__2___boxed), 7, 3);
lean_closure_set(x_50, 0, x_47);
lean_closure_set(x_50, 1, x_48);
lean_closure_set(x_50, 2, x_49);
x_51 = l_Lean_Meta_forallTelescope___rarg(x_10, x_50, x_5, x_46);
return x_51;
}
default: 
{
uint8_t x_52; 
lean_dec(x_5);
x_52 = !lean_is_exclusive(x_9);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_9, 0);
lean_dec(x_53);
return x_9;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_9, 1);
lean_inc(x_54);
lean_dec(x_9);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_10);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_5);
x_56 = !lean_is_exclusive(x_9);
if (x_56 == 0)
{
return x_9;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_9, 0);
x_58 = lean_ctor_get(x_9, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_9);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; 
lean_dec(x_5);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_4);
lean_ctor_set(x_60, 1, x_8);
return x_60;
}
}
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_reduceAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Nat_foldMAux___main___at_Lean_Meta_reduceAux___main___spec__1(x_10, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
lean_object* l_Lean_Meta_reduceAux___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_reduceAux___main___lambda__1(x_8, x_9, x_10, x_4, x_5, x_6, x_7);
return x_11;
}
}
lean_object* l_Lean_Meta_reduceAux___main___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_reduceAux___main___lambda__2(x_8, x_9, x_10, x_4, x_5, x_6, x_7);
return x_11;
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
