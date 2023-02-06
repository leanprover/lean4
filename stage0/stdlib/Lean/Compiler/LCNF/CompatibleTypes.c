// Lean compiler output
// Module: Lean.Compiler.LCNF.CompatibleTypes
// Imports: Init Lean.Compiler.LCNF.InferType
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
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Compiler_LCNF_InferType_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshFVarId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isEquiv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_compatibleTypesQuick(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEqv___at_Lean_Compiler_LCNF_eqvTypes___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compatibleTypesQuick___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_compatibleTypesQuick(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_55; 
x_55 = l_Lean_Expr_isErased(x_1);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = l_Lean_Expr_isErased(x_2);
x_3 = x_56;
goto block_54;
}
else
{
uint8_t x_57; 
x_57 = 1;
x_3 = x_57;
goto block_54;
}
block_54:
{
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_48; 
lean_inc(x_1);
x_4 = l_Lean_Expr_headBeta(x_1);
lean_inc(x_2);
x_5 = l_Lean_Expr_headBeta(x_2);
x_48 = lean_expr_eqv(x_1, x_4);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = 1;
x_6 = x_49;
goto block_47;
}
else
{
uint8_t x_50; 
x_50 = lean_expr_eqv(x_2, x_5);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = 1;
x_6 = x_51;
goto block_47;
}
else
{
uint8_t x_52; 
x_52 = 0;
x_6 = x_52;
goto block_47;
}
}
block_47:
{
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
lean_dec(x_4);
x_7 = lean_expr_eqv(x_1, x_2);
if (x_7 == 0)
{
switch (lean_obj_tag(x_1)) {
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lean_Level_isEquiv(x_8, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = 0;
return x_11;
}
}
case 4:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_name_eq(x_12, x_14);
lean_dec(x_14);
lean_dec(x_12);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_15);
lean_dec(x_13);
x_17 = 0;
return x_17;
}
else
{
uint8_t x_18; 
x_18 = l_List_isEqv___at_Lean_Compiler_LCNF_eqvTypes___spec__1(x_13, x_15);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = 0;
return x_19;
}
}
case 5:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_24 = l_Lean_Compiler_LCNF_compatibleTypesQuick(x_20, x_22);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_23);
lean_dec(x_21);
x_25 = 0;
return x_25;
}
else
{
x_1 = x_21;
x_2 = x_23;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = 0;
return x_27;
}
}
case 6:
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 2);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 2);
lean_inc(x_31);
lean_dec(x_2);
x_32 = l_Lean_Compiler_LCNF_compatibleTypesQuick(x_28, x_30);
if (x_32 == 0)
{
uint8_t x_33; 
lean_dec(x_31);
lean_dec(x_29);
x_33 = 0;
return x_33;
}
else
{
x_1 = x_29;
x_2 = x_31;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_dec(x_2);
lean_dec(x_1);
x_35 = 0;
return x_35;
}
}
case 7:
{
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 2);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_ctor_get(x_2, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 2);
lean_inc(x_39);
lean_dec(x_2);
x_40 = l_Lean_Compiler_LCNF_compatibleTypesQuick(x_36, x_38);
if (x_40 == 0)
{
uint8_t x_41; 
lean_dec(x_39);
lean_dec(x_37);
x_41 = 0;
return x_41;
}
else
{
x_1 = x_37;
x_2 = x_39;
goto _start;
}
}
else
{
uint8_t x_43; 
lean_dec(x_2);
lean_dec(x_1);
x_43 = 0;
return x_43;
}
}
default: 
{
uint8_t x_44; 
lean_dec(x_2);
lean_dec(x_1);
x_44 = 0;
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_2);
lean_dec(x_1);
x_45 = 1;
return x_45;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_4;
x_2 = x_5;
goto _start;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_2);
lean_dec(x_1);
x_53 = 1;
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compatibleTypesQuick___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_compatibleTypesQuick(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_Compiler_LCNF_InferType_inferType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Expr_headBeta(x_10);
if (lean_obj_tag(x_11) == 7)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 8);
lean_dec(x_11);
x_15 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__1;
x_16 = l_Lean_Expr_app___override(x_1, x_15);
x_17 = l_Lean_Expr_lam___override(x_12, x_13, x_16, x_14);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_8, 0, x_18);
return x_8;
}
else
{
lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_1);
x_19 = lean_box(0);
lean_ctor_set(x_8, 0, x_19);
return x_8;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = l_Lean_Expr_headBeta(x_20);
if (lean_obj_tag(x_22) == 7)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_22, sizeof(void*)*3 + 8);
lean_dec(x_22);
x_26 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__1;
x_27 = l_Lean_Expr_app___override(x_1, x_26);
x_28 = l_Lean_Expr_lam___override(x_23, x_24, x_27, x_25);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_21);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_22);
lean_dec(x_1);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_21);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_8);
if (x_33 == 0)
{
return x_8;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_8, 0);
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_8);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
x_13 = l_Lean_mkFreshFVarId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__1(x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_14);
x_16 = l_Lean_Expr_fvar___override(x_14);
x_17 = 0;
x_18 = l_Lean_LocalContext_mkLocalDecl(x_7, x_14, x_1, x_2, x_3, x_17);
x_19 = lean_expr_instantiate1(x_4, x_16);
lean_dec(x_4);
x_20 = lean_expr_instantiate1(x_5, x_16);
lean_dec(x_16);
lean_dec(x_5);
x_21 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(x_19, x_20, x_18, x_8, x_9, x_10, x_11, x_15);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_343; 
x_343 = l_Lean_Expr_isErased(x_1);
if (x_343 == 0)
{
uint8_t x_344; 
x_344 = l_Lean_Expr_isErased(x_2);
x_9 = x_344;
goto block_342;
}
else
{
uint8_t x_345; 
x_345 = 1;
x_9 = x_345;
goto block_342;
}
block_342:
{
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_334; 
lean_inc(x_1);
x_10 = l_Lean_Expr_headBeta(x_1);
lean_inc(x_2);
x_11 = l_Lean_Expr_headBeta(x_2);
x_334 = lean_expr_eqv(x_1, x_10);
if (x_334 == 0)
{
uint8_t x_335; 
x_335 = 1;
x_12 = x_335;
goto block_333;
}
else
{
uint8_t x_336; 
x_336 = lean_expr_eqv(x_2, x_11);
if (x_336 == 0)
{
uint8_t x_337; 
x_337 = 1;
x_12 = x_337;
goto block_333;
}
else
{
uint8_t x_338; 
x_338 = 0;
x_12 = x_338;
goto block_333;
}
}
block_333:
{
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_11);
lean_dec(x_10);
x_13 = lean_expr_eqv(x_1, x_2);
if (x_13 == 0)
{
switch (lean_obj_tag(x_1)) {
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l_Lean_Level_isEquiv(x_14, x_15);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = l_Lean_Expr_isLambda(x_1);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_Lean_Expr_isLambda(x_2);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_8);
return x_23;
}
else
{
lean_object* x_24; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_24 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = 0;
x_29 = lean_box(x_28);
lean_ctor_set(x_24, 0, x_29);
return x_24;
}
else
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = 0;
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_dec(x_24);
x_35 = lean_ctor_get(x_25, 0);
lean_inc(x_35);
lean_dec(x_25);
x_1 = x_35;
x_8 = x_34;
goto _start;
}
}
else
{
uint8_t x_37; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_24);
if (x_37 == 0)
{
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_24);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
else
{
lean_object* x_41; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_41 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_41, 0);
lean_dec(x_44);
x_45 = 0;
x_46 = lean_box(x_45);
lean_ctor_set(x_41, 0, x_46);
return x_41;
}
else
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
lean_dec(x_41);
x_48 = 0;
x_49 = lean_box(x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_41, 1);
lean_inc(x_51);
lean_dec(x_41);
x_52 = lean_ctor_get(x_42, 0);
lean_inc(x_52);
lean_dec(x_42);
x_2 = x_52;
x_8 = x_51;
goto _start;
}
}
else
{
uint8_t x_54; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_41);
if (x_54 == 0)
{
return x_41;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_41, 0);
x_56 = lean_ctor_get(x_41, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_41);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
}
case 4:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_58 = lean_ctor_get(x_1, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_1, 1);
lean_inc(x_59);
lean_dec(x_1);
x_60 = lean_ctor_get(x_2, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_2, 1);
lean_inc(x_61);
lean_dec(x_2);
x_62 = lean_name_eq(x_58, x_60);
lean_dec(x_60);
lean_dec(x_58);
if (x_62 == 0)
{
uint8_t x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_61);
lean_dec(x_59);
x_63 = 0;
x_64 = lean_box(x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_8);
return x_65;
}
else
{
uint8_t x_66; lean_object* x_67; lean_object* x_68; 
x_66 = l_List_isEqv___at_Lean_Compiler_LCNF_eqvTypes___spec__1(x_59, x_61);
x_67 = lean_box(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_8);
return x_68;
}
}
else
{
uint8_t x_69; 
x_69 = l_Lean_Expr_isLambda(x_1);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = l_Lean_Expr_isLambda(x_2);
if (x_70 == 0)
{
uint8_t x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = 0;
x_72 = lean_box(x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_8);
return x_73;
}
else
{
lean_object* x_74; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_74 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_76 = !lean_is_exclusive(x_74);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_74, 0);
lean_dec(x_77);
x_78 = 0;
x_79 = lean_box(x_78);
lean_ctor_set(x_74, 0, x_79);
return x_74;
}
else
{
lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_74, 1);
lean_inc(x_80);
lean_dec(x_74);
x_81 = 0;
x_82 = lean_box(x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_80);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_74, 1);
lean_inc(x_84);
lean_dec(x_74);
x_85 = lean_ctor_get(x_75, 0);
lean_inc(x_85);
lean_dec(x_75);
x_1 = x_85;
x_8 = x_84;
goto _start;
}
}
else
{
uint8_t x_87; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_74);
if (x_87 == 0)
{
return x_74;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_74, 0);
x_89 = lean_ctor_get(x_74, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_74);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
else
{
lean_object* x_91; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_91 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_93; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_91);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_91, 0);
lean_dec(x_94);
x_95 = 0;
x_96 = lean_box(x_95);
lean_ctor_set(x_91, 0, x_96);
return x_91;
}
else
{
lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_91, 1);
lean_inc(x_97);
lean_dec(x_91);
x_98 = 0;
x_99 = lean_box(x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_97);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_91, 1);
lean_inc(x_101);
lean_dec(x_91);
x_102 = lean_ctor_get(x_92, 0);
lean_inc(x_102);
lean_dec(x_92);
x_2 = x_102;
x_8 = x_101;
goto _start;
}
}
else
{
uint8_t x_104; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_91);
if (x_104 == 0)
{
return x_91;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_91, 0);
x_106 = lean_ctor_get(x_91, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_91);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
}
case 5:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_ctor_get(x_1, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_1, 1);
lean_inc(x_109);
lean_dec(x_1);
x_110 = lean_ctor_get(x_2, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_2, 1);
lean_inc(x_111);
lean_dec(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_112 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(x_108, x_110, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; uint8_t x_114; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_unbox(x_113);
if (x_114 == 0)
{
uint8_t x_115; 
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_115 = !lean_is_exclusive(x_112);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_112, 0);
lean_dec(x_116);
return x_112;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_112, 1);
lean_inc(x_117);
lean_dec(x_112);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_113);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
else
{
lean_object* x_119; 
lean_dec(x_113);
x_119 = lean_ctor_get(x_112, 1);
lean_inc(x_119);
lean_dec(x_112);
x_1 = x_109;
x_2 = x_111;
x_8 = x_119;
goto _start;
}
}
else
{
uint8_t x_121; 
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_121 = !lean_is_exclusive(x_112);
if (x_121 == 0)
{
return x_112;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_112, 0);
x_123 = lean_ctor_get(x_112, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_112);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
uint8_t x_125; 
x_125 = l_Lean_Expr_isLambda(x_1);
if (x_125 == 0)
{
uint8_t x_126; 
x_126 = l_Lean_Expr_isLambda(x_2);
if (x_126 == 0)
{
uint8_t x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_127 = 0;
x_128 = lean_box(x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_8);
return x_129;
}
else
{
lean_object* x_130; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_130 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
if (lean_obj_tag(x_131) == 0)
{
uint8_t x_132; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_132 = !lean_is_exclusive(x_130);
if (x_132 == 0)
{
lean_object* x_133; uint8_t x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_130, 0);
lean_dec(x_133);
x_134 = 0;
x_135 = lean_box(x_134);
lean_ctor_set(x_130, 0, x_135);
return x_130;
}
else
{
lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_130, 1);
lean_inc(x_136);
lean_dec(x_130);
x_137 = 0;
x_138 = lean_box(x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_136);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_130, 1);
lean_inc(x_140);
lean_dec(x_130);
x_141 = lean_ctor_get(x_131, 0);
lean_inc(x_141);
lean_dec(x_131);
x_1 = x_141;
x_8 = x_140;
goto _start;
}
}
else
{
uint8_t x_143; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_143 = !lean_is_exclusive(x_130);
if (x_143 == 0)
{
return x_130;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_130, 0);
x_145 = lean_ctor_get(x_130, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_130);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
}
else
{
lean_object* x_147; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_147 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
if (lean_obj_tag(x_148) == 0)
{
uint8_t x_149; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_149 = !lean_is_exclusive(x_147);
if (x_149 == 0)
{
lean_object* x_150; uint8_t x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_147, 0);
lean_dec(x_150);
x_151 = 0;
x_152 = lean_box(x_151);
lean_ctor_set(x_147, 0, x_152);
return x_147;
}
else
{
lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; 
x_153 = lean_ctor_get(x_147, 1);
lean_inc(x_153);
lean_dec(x_147);
x_154 = 0;
x_155 = lean_box(x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_153);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_147, 1);
lean_inc(x_157);
lean_dec(x_147);
x_158 = lean_ctor_get(x_148, 0);
lean_inc(x_158);
lean_dec(x_148);
x_2 = x_158;
x_8 = x_157;
goto _start;
}
}
else
{
uint8_t x_160; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_160 = !lean_is_exclusive(x_147);
if (x_160 == 0)
{
return x_147;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_147, 0);
x_162 = lean_ctor_get(x_147, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_147);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
}
}
case 6:
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_164 = lean_ctor_get(x_1, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_1, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_1, 2);
lean_inc(x_166);
x_167 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_168 = lean_ctor_get(x_2, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_2, 2);
lean_inc(x_169);
lean_dec(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_165);
x_170 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(x_165, x_168, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; uint8_t x_172; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_unbox(x_171);
lean_dec(x_171);
if (x_172 == 0)
{
uint8_t x_173; 
lean_dec(x_169);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_173 = !lean_is_exclusive(x_170);
if (x_173 == 0)
{
lean_object* x_174; uint8_t x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_170, 0);
lean_dec(x_174);
x_175 = 0;
x_176 = lean_box(x_175);
lean_ctor_set(x_170, 0, x_176);
return x_170;
}
else
{
lean_object* x_177; uint8_t x_178; lean_object* x_179; lean_object* x_180; 
x_177 = lean_ctor_get(x_170, 1);
lean_inc(x_177);
lean_dec(x_170);
x_178 = 0;
x_179 = lean_box(x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_177);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_170, 1);
lean_inc(x_181);
lean_dec(x_170);
x_182 = lean_box(0);
x_183 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull___lambda__1(x_164, x_165, x_167, x_166, x_169, x_182, x_3, x_4, x_5, x_6, x_7, x_181);
return x_183;
}
}
else
{
uint8_t x_184; 
lean_dec(x_169);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_184 = !lean_is_exclusive(x_170);
if (x_184 == 0)
{
return x_170;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_170, 0);
x_186 = lean_ctor_get(x_170, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_170);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
else
{
uint8_t x_188; 
x_188 = l_Lean_Expr_isLambda(x_1);
if (x_188 == 0)
{
uint8_t x_189; 
x_189 = l_Lean_Expr_isLambda(x_2);
if (x_189 == 0)
{
uint8_t x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_190 = 0;
x_191 = lean_box(x_190);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_8);
return x_192;
}
else
{
lean_object* x_193; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_193 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
uint8_t x_195; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_195 = !lean_is_exclusive(x_193);
if (x_195 == 0)
{
lean_object* x_196; uint8_t x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_193, 0);
lean_dec(x_196);
x_197 = 0;
x_198 = lean_box(x_197);
lean_ctor_set(x_193, 0, x_198);
return x_193;
}
else
{
lean_object* x_199; uint8_t x_200; lean_object* x_201; lean_object* x_202; 
x_199 = lean_ctor_get(x_193, 1);
lean_inc(x_199);
lean_dec(x_193);
x_200 = 0;
x_201 = lean_box(x_200);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_199);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_193, 1);
lean_inc(x_203);
lean_dec(x_193);
x_204 = lean_ctor_get(x_194, 0);
lean_inc(x_204);
lean_dec(x_194);
x_1 = x_204;
x_8 = x_203;
goto _start;
}
}
else
{
uint8_t x_206; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_206 = !lean_is_exclusive(x_193);
if (x_206 == 0)
{
return x_193;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_193, 0);
x_208 = lean_ctor_get(x_193, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_193);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
}
else
{
lean_object* x_210; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_210 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
if (lean_obj_tag(x_211) == 0)
{
uint8_t x_212; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_212 = !lean_is_exclusive(x_210);
if (x_212 == 0)
{
lean_object* x_213; uint8_t x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_210, 0);
lean_dec(x_213);
x_214 = 0;
x_215 = lean_box(x_214);
lean_ctor_set(x_210, 0, x_215);
return x_210;
}
else
{
lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; 
x_216 = lean_ctor_get(x_210, 1);
lean_inc(x_216);
lean_dec(x_210);
x_217 = 0;
x_218 = lean_box(x_217);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_216);
return x_219;
}
}
else
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_210, 1);
lean_inc(x_220);
lean_dec(x_210);
x_221 = lean_ctor_get(x_211, 0);
lean_inc(x_221);
lean_dec(x_211);
x_2 = x_221;
x_8 = x_220;
goto _start;
}
}
else
{
uint8_t x_223; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_223 = !lean_is_exclusive(x_210);
if (x_223 == 0)
{
return x_210;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_210, 0);
x_225 = lean_ctor_get(x_210, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_210);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
return x_226;
}
}
}
}
}
case 7:
{
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_227 = lean_ctor_get(x_1, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_1, 1);
lean_inc(x_228);
x_229 = lean_ctor_get(x_1, 2);
lean_inc(x_229);
x_230 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_231 = lean_ctor_get(x_2, 1);
lean_inc(x_231);
x_232 = lean_ctor_get(x_2, 2);
lean_inc(x_232);
lean_dec(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_228);
x_233 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(x_228, x_231, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; uint8_t x_235; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_unbox(x_234);
lean_dec(x_234);
if (x_235 == 0)
{
uint8_t x_236; 
lean_dec(x_232);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_236 = !lean_is_exclusive(x_233);
if (x_236 == 0)
{
lean_object* x_237; uint8_t x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_233, 0);
lean_dec(x_237);
x_238 = 0;
x_239 = lean_box(x_238);
lean_ctor_set(x_233, 0, x_239);
return x_233;
}
else
{
lean_object* x_240; uint8_t x_241; lean_object* x_242; lean_object* x_243; 
x_240 = lean_ctor_get(x_233, 1);
lean_inc(x_240);
lean_dec(x_233);
x_241 = 0;
x_242 = lean_box(x_241);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_240);
return x_243;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_233, 1);
lean_inc(x_244);
lean_dec(x_233);
x_245 = lean_box(0);
x_246 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull___lambda__1(x_227, x_228, x_230, x_229, x_232, x_245, x_3, x_4, x_5, x_6, x_7, x_244);
return x_246;
}
}
else
{
uint8_t x_247; 
lean_dec(x_232);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_247 = !lean_is_exclusive(x_233);
if (x_247 == 0)
{
return x_233;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_233, 0);
x_249 = lean_ctor_get(x_233, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_233);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
else
{
uint8_t x_251; 
x_251 = l_Lean_Expr_isLambda(x_1);
if (x_251 == 0)
{
uint8_t x_252; 
x_252 = l_Lean_Expr_isLambda(x_2);
if (x_252 == 0)
{
uint8_t x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_253 = 0;
x_254 = lean_box(x_253);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_8);
return x_255;
}
else
{
lean_object* x_256; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_256 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
if (lean_obj_tag(x_257) == 0)
{
uint8_t x_258; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_258 = !lean_is_exclusive(x_256);
if (x_258 == 0)
{
lean_object* x_259; uint8_t x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_256, 0);
lean_dec(x_259);
x_260 = 0;
x_261 = lean_box(x_260);
lean_ctor_set(x_256, 0, x_261);
return x_256;
}
else
{
lean_object* x_262; uint8_t x_263; lean_object* x_264; lean_object* x_265; 
x_262 = lean_ctor_get(x_256, 1);
lean_inc(x_262);
lean_dec(x_256);
x_263 = 0;
x_264 = lean_box(x_263);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_262);
return x_265;
}
}
else
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_256, 1);
lean_inc(x_266);
lean_dec(x_256);
x_267 = lean_ctor_get(x_257, 0);
lean_inc(x_267);
lean_dec(x_257);
x_1 = x_267;
x_8 = x_266;
goto _start;
}
}
else
{
uint8_t x_269; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_269 = !lean_is_exclusive(x_256);
if (x_269 == 0)
{
return x_256;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_256, 0);
x_271 = lean_ctor_get(x_256, 1);
lean_inc(x_271);
lean_inc(x_270);
lean_dec(x_256);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
return x_272;
}
}
}
}
else
{
lean_object* x_273; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_273 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
if (lean_obj_tag(x_274) == 0)
{
uint8_t x_275; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_275 = !lean_is_exclusive(x_273);
if (x_275 == 0)
{
lean_object* x_276; uint8_t x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_273, 0);
lean_dec(x_276);
x_277 = 0;
x_278 = lean_box(x_277);
lean_ctor_set(x_273, 0, x_278);
return x_273;
}
else
{
lean_object* x_279; uint8_t x_280; lean_object* x_281; lean_object* x_282; 
x_279 = lean_ctor_get(x_273, 1);
lean_inc(x_279);
lean_dec(x_273);
x_280 = 0;
x_281 = lean_box(x_280);
x_282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_279);
return x_282;
}
}
else
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_ctor_get(x_273, 1);
lean_inc(x_283);
lean_dec(x_273);
x_284 = lean_ctor_get(x_274, 0);
lean_inc(x_284);
lean_dec(x_274);
x_2 = x_284;
x_8 = x_283;
goto _start;
}
}
else
{
uint8_t x_286; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_286 = !lean_is_exclusive(x_273);
if (x_286 == 0)
{
return x_273;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_287 = lean_ctor_get(x_273, 0);
x_288 = lean_ctor_get(x_273, 1);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_273);
x_289 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_289, 0, x_287);
lean_ctor_set(x_289, 1, x_288);
return x_289;
}
}
}
}
}
default: 
{
uint8_t x_290; 
x_290 = l_Lean_Expr_isLambda(x_1);
if (x_290 == 0)
{
uint8_t x_291; 
x_291 = l_Lean_Expr_isLambda(x_2);
if (x_291 == 0)
{
uint8_t x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_292 = 0;
x_293 = lean_box(x_292);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_8);
return x_294;
}
else
{
lean_object* x_295; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_295 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
if (lean_obj_tag(x_296) == 0)
{
uint8_t x_297; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_297 = !lean_is_exclusive(x_295);
if (x_297 == 0)
{
lean_object* x_298; uint8_t x_299; lean_object* x_300; 
x_298 = lean_ctor_get(x_295, 0);
lean_dec(x_298);
x_299 = 0;
x_300 = lean_box(x_299);
lean_ctor_set(x_295, 0, x_300);
return x_295;
}
else
{
lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; 
x_301 = lean_ctor_get(x_295, 1);
lean_inc(x_301);
lean_dec(x_295);
x_302 = 0;
x_303 = lean_box(x_302);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_301);
return x_304;
}
}
else
{
lean_object* x_305; lean_object* x_306; 
x_305 = lean_ctor_get(x_295, 1);
lean_inc(x_305);
lean_dec(x_295);
x_306 = lean_ctor_get(x_296, 0);
lean_inc(x_306);
lean_dec(x_296);
x_1 = x_306;
x_8 = x_305;
goto _start;
}
}
else
{
uint8_t x_308; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_308 = !lean_is_exclusive(x_295);
if (x_308 == 0)
{
return x_295;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_295, 0);
x_310 = lean_ctor_get(x_295, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_295);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
return x_311;
}
}
}
}
else
{
lean_object* x_312; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_312 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; 
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
if (lean_obj_tag(x_313) == 0)
{
uint8_t x_314; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_314 = !lean_is_exclusive(x_312);
if (x_314 == 0)
{
lean_object* x_315; uint8_t x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_312, 0);
lean_dec(x_315);
x_316 = 0;
x_317 = lean_box(x_316);
lean_ctor_set(x_312, 0, x_317);
return x_312;
}
else
{
lean_object* x_318; uint8_t x_319; lean_object* x_320; lean_object* x_321; 
x_318 = lean_ctor_get(x_312, 1);
lean_inc(x_318);
lean_dec(x_312);
x_319 = 0;
x_320 = lean_box(x_319);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_318);
return x_321;
}
}
else
{
lean_object* x_322; lean_object* x_323; 
x_322 = lean_ctor_get(x_312, 1);
lean_inc(x_322);
lean_dec(x_312);
x_323 = lean_ctor_get(x_313, 0);
lean_inc(x_323);
lean_dec(x_313);
x_2 = x_323;
x_8 = x_322;
goto _start;
}
}
else
{
uint8_t x_325; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_325 = !lean_is_exclusive(x_312);
if (x_325 == 0)
{
return x_312;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_312, 0);
x_327 = lean_ctor_get(x_312, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_312);
x_328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
return x_328;
}
}
}
}
}
}
else
{
uint8_t x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_329 = 1;
x_330 = lean_box(x_329);
x_331 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_8);
return x_331;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_10;
x_2 = x_11;
goto _start;
}
}
}
else
{
uint8_t x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_339 = 1;
x_340 = lean_box(x_339);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_8);
return x_341;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull___lambda__1(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_Compiler_LCNF_compatibleTypesQuick(x_1, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_CompatibleTypes(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__1 = _init_l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
