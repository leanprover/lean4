// Lean compiler output
// Module: Lean.Compiler.LCNF.CompatibleTypes
// Imports: Lean.Compiler.LCNF.InferType
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
uint8_t x_3; 
x_3 = l_Lean_Expr_isErased(x_1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = l_Lean_Expr_isErased(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_1);
x_5 = l_Lean_Expr_headBeta(x_1);
lean_inc(x_2);
x_6 = l_Lean_Expr_headBeta(x_2);
x_7 = lean_expr_eqv(x_1, x_5);
if (x_7 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_5;
x_2 = x_6;
goto _start;
}
else
{
uint8_t x_9; 
x_9 = lean_expr_eqv(x_2, x_6);
if (x_9 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_5;
x_2 = x_6;
goto _start;
}
else
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_expr_eqv(x_1, x_2);
if (x_11 == 0)
{
switch (lean_obj_tag(x_1)) {
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_Level_isEquiv(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_2);
lean_dec(x_1);
x_15 = 0;
return x_15;
}
}
case 4:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_name_eq(x_16, x_18);
lean_dec(x_18);
lean_dec(x_16);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_19);
lean_dec(x_17);
x_21 = 0;
return x_21;
}
else
{
uint8_t x_22; 
x_22 = l_List_isEqv___at_Lean_Compiler_LCNF_eqvTypes___spec__1(x_17, x_19);
lean_dec(x_19);
lean_dec(x_17);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_2);
lean_dec(x_1);
x_23 = 0;
return x_23;
}
}
case 5:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_dec(x_2);
x_28 = l_Lean_Compiler_LCNF_compatibleTypesQuick(x_24, x_26);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec(x_27);
lean_dec(x_25);
x_29 = 0;
return x_29;
}
else
{
x_1 = x_25;
x_2 = x_27;
goto _start;
}
}
else
{
uint8_t x_31; 
lean_dec(x_2);
lean_dec(x_1);
x_31 = 0;
return x_31;
}
}
case 6:
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 2);
lean_inc(x_35);
lean_dec(x_2);
x_36 = l_Lean_Compiler_LCNF_compatibleTypesQuick(x_32, x_34);
if (x_36 == 0)
{
uint8_t x_37; 
lean_dec(x_35);
lean_dec(x_33);
x_37 = 0;
return x_37;
}
else
{
x_1 = x_33;
x_2 = x_35;
goto _start;
}
}
else
{
uint8_t x_39; 
lean_dec(x_2);
lean_dec(x_1);
x_39 = 0;
return x_39;
}
}
case 7:
{
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 2);
lean_inc(x_41);
lean_dec(x_1);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 2);
lean_inc(x_43);
lean_dec(x_2);
x_44 = l_Lean_Compiler_LCNF_compatibleTypesQuick(x_40, x_42);
if (x_44 == 0)
{
uint8_t x_45; 
lean_dec(x_43);
lean_dec(x_41);
x_45 = 0;
return x_45;
}
else
{
x_1 = x_41;
x_2 = x_43;
goto _start;
}
}
else
{
uint8_t x_47; 
lean_dec(x_2);
lean_dec(x_1);
x_47 = 0;
return x_47;
}
}
default: 
{
uint8_t x_48; 
lean_dec(x_2);
lean_dec(x_1);
x_48 = 0;
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_2);
lean_dec(x_1);
x_49 = 1;
return x_49;
}
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_2);
lean_dec(x_1);
x_50 = 1;
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_2);
lean_dec(x_1);
x_51 = 1;
return x_51;
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
x_20 = lean_expr_instantiate1(x_5, x_16);
lean_dec(x_16);
x_21 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(x_19, x_20, x_18, x_8, x_9, x_10, x_11, x_15);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Expr_isErased(x_1);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_Expr_isErased(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_1);
x_11 = l_Lean_Expr_headBeta(x_1);
lean_inc(x_2);
x_12 = l_Lean_Expr_headBeta(x_2);
x_13 = lean_expr_eqv(x_1, x_11);
if (x_13 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_12;
goto _start;
}
else
{
uint8_t x_15; 
x_15 = lean_expr_eqv(x_2, x_12);
if (x_15 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_12;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_expr_eqv(x_1, x_2);
if (x_17 == 0)
{
switch (lean_obj_tag(x_1)) {
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_20 = l_Lean_Level_isEquiv(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_8);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = l_Lean_Expr_isLambda(x_1);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Expr_isLambda(x_2);
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = 0;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_8);
return x_27;
}
else
{
lean_object* x_28; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_28 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
x_32 = 0;
x_33 = lean_box(x_32);
lean_ctor_set(x_28, 0, x_33);
return x_28;
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = 0;
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
lean_dec(x_28);
x_39 = lean_ctor_get(x_29, 0);
lean_inc(x_39);
lean_dec(x_29);
x_1 = x_39;
x_8 = x_38;
goto _start;
}
}
else
{
uint8_t x_41; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_28);
if (x_41 == 0)
{
return x_28;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_28, 0);
x_43 = lean_ctor_get(x_28, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_28);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
lean_object* x_45; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_45 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_45);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_45, 0);
lean_dec(x_48);
x_49 = 0;
x_50 = lean_box(x_49);
lean_ctor_set(x_45, 0, x_50);
return x_45;
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
lean_dec(x_45);
x_52 = 0;
x_53 = lean_box(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_45, 1);
lean_inc(x_55);
lean_dec(x_45);
x_56 = lean_ctor_get(x_46, 0);
lean_inc(x_56);
lean_dec(x_46);
x_2 = x_56;
x_8 = x_55;
goto _start;
}
}
else
{
uint8_t x_58; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_45);
if (x_58 == 0)
{
return x_45;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_45, 0);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_45);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
}
case 4:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_62 = lean_ctor_get(x_1, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_1, 1);
lean_inc(x_63);
lean_dec(x_1);
x_64 = lean_ctor_get(x_2, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_2, 1);
lean_inc(x_65);
lean_dec(x_2);
x_66 = lean_name_eq(x_62, x_64);
lean_dec(x_64);
lean_dec(x_62);
if (x_66 == 0)
{
uint8_t x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_65);
lean_dec(x_63);
x_67 = 0;
x_68 = lean_box(x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_8);
return x_69;
}
else
{
uint8_t x_70; lean_object* x_71; lean_object* x_72; 
x_70 = l_List_isEqv___at_Lean_Compiler_LCNF_eqvTypes___spec__1(x_63, x_65);
lean_dec(x_65);
lean_dec(x_63);
x_71 = lean_box(x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_8);
return x_72;
}
}
else
{
uint8_t x_73; 
x_73 = l_Lean_Expr_isLambda(x_1);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = l_Lean_Expr_isLambda(x_2);
if (x_74 == 0)
{
uint8_t x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = 0;
x_76 = lean_box(x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_8);
return x_77;
}
else
{
lean_object* x_78; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_78 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_80; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_80 = !lean_is_exclusive(x_78);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_78, 0);
lean_dec(x_81);
x_82 = 0;
x_83 = lean_box(x_82);
lean_ctor_set(x_78, 0, x_83);
return x_78;
}
else
{
lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_78, 1);
lean_inc(x_84);
lean_dec(x_78);
x_85 = 0;
x_86 = lean_box(x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_78, 1);
lean_inc(x_88);
lean_dec(x_78);
x_89 = lean_ctor_get(x_79, 0);
lean_inc(x_89);
lean_dec(x_79);
x_1 = x_89;
x_8 = x_88;
goto _start;
}
}
else
{
uint8_t x_91; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_78);
if (x_91 == 0)
{
return x_78;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_78, 0);
x_93 = lean_ctor_get(x_78, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_78);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
else
{
lean_object* x_95; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_95 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_97; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_95);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_95, 0);
lean_dec(x_98);
x_99 = 0;
x_100 = lean_box(x_99);
lean_ctor_set(x_95, 0, x_100);
return x_95;
}
else
{
lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_95, 1);
lean_inc(x_101);
lean_dec(x_95);
x_102 = 0;
x_103 = lean_box(x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_95, 1);
lean_inc(x_105);
lean_dec(x_95);
x_106 = lean_ctor_get(x_96, 0);
lean_inc(x_106);
lean_dec(x_96);
x_2 = x_106;
x_8 = x_105;
goto _start;
}
}
else
{
uint8_t x_108; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_95);
if (x_108 == 0)
{
return x_95;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_95, 0);
x_110 = lean_ctor_get(x_95, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_95);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
}
case 5:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_ctor_get(x_1, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_1, 1);
lean_inc(x_113);
lean_dec(x_1);
x_114 = lean_ctor_get(x_2, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_2, 1);
lean_inc(x_115);
lean_dec(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_116 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(x_112, x_114, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_unbox(x_117);
if (x_118 == 0)
{
uint8_t x_119; 
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_119 = !lean_is_exclusive(x_116);
if (x_119 == 0)
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_116, 0);
lean_dec(x_120);
return x_116;
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_116, 1);
lean_inc(x_121);
lean_dec(x_116);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_117);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
else
{
lean_object* x_123; 
lean_dec(x_117);
x_123 = lean_ctor_get(x_116, 1);
lean_inc(x_123);
lean_dec(x_116);
x_1 = x_113;
x_2 = x_115;
x_8 = x_123;
goto _start;
}
}
else
{
uint8_t x_125; 
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_125 = !lean_is_exclusive(x_116);
if (x_125 == 0)
{
return x_116;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_116, 0);
x_127 = lean_ctor_get(x_116, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_116);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
uint8_t x_129; 
x_129 = l_Lean_Expr_isLambda(x_1);
if (x_129 == 0)
{
uint8_t x_130; 
x_130 = l_Lean_Expr_isLambda(x_2);
if (x_130 == 0)
{
uint8_t x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_131 = 0;
x_132 = lean_box(x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_8);
return x_133;
}
else
{
lean_object* x_134; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_134 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
uint8_t x_136; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_136 = !lean_is_exclusive(x_134);
if (x_136 == 0)
{
lean_object* x_137; uint8_t x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_134, 0);
lean_dec(x_137);
x_138 = 0;
x_139 = lean_box(x_138);
lean_ctor_set(x_134, 0, x_139);
return x_134;
}
else
{
lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_134, 1);
lean_inc(x_140);
lean_dec(x_134);
x_141 = 0;
x_142 = lean_box(x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_140);
return x_143;
}
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_134, 1);
lean_inc(x_144);
lean_dec(x_134);
x_145 = lean_ctor_get(x_135, 0);
lean_inc(x_145);
lean_dec(x_135);
x_1 = x_145;
x_8 = x_144;
goto _start;
}
}
else
{
uint8_t x_147; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_147 = !lean_is_exclusive(x_134);
if (x_147 == 0)
{
return x_134;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_134, 0);
x_149 = lean_ctor_get(x_134, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_134);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
}
else
{
lean_object* x_151; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_151 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
if (lean_obj_tag(x_152) == 0)
{
uint8_t x_153; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_153 = !lean_is_exclusive(x_151);
if (x_153 == 0)
{
lean_object* x_154; uint8_t x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_151, 0);
lean_dec(x_154);
x_155 = 0;
x_156 = lean_box(x_155);
lean_ctor_set(x_151, 0, x_156);
return x_151;
}
else
{
lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_ctor_get(x_151, 1);
lean_inc(x_157);
lean_dec(x_151);
x_158 = 0;
x_159 = lean_box(x_158);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_157);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_151, 1);
lean_inc(x_161);
lean_dec(x_151);
x_162 = lean_ctor_get(x_152, 0);
lean_inc(x_162);
lean_dec(x_152);
x_2 = x_162;
x_8 = x_161;
goto _start;
}
}
else
{
uint8_t x_164; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_164 = !lean_is_exclusive(x_151);
if (x_164 == 0)
{
return x_151;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_151, 0);
x_166 = lean_ctor_get(x_151, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_151);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
}
}
case 6:
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_168 = lean_ctor_get(x_1, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_1, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_1, 2);
lean_inc(x_170);
x_171 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_172 = lean_ctor_get(x_2, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_2, 2);
lean_inc(x_173);
lean_dec(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_169);
x_174 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(x_169, x_172, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; uint8_t x_176; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_unbox(x_175);
lean_dec(x_175);
if (x_176 == 0)
{
uint8_t x_177; 
lean_dec(x_173);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_177 = !lean_is_exclusive(x_174);
if (x_177 == 0)
{
lean_object* x_178; uint8_t x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_174, 0);
lean_dec(x_178);
x_179 = 0;
x_180 = lean_box(x_179);
lean_ctor_set(x_174, 0, x_180);
return x_174;
}
else
{
lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; 
x_181 = lean_ctor_get(x_174, 1);
lean_inc(x_181);
lean_dec(x_174);
x_182 = 0;
x_183 = lean_box(x_182);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_181);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_174, 1);
lean_inc(x_185);
lean_dec(x_174);
x_186 = lean_box(0);
x_187 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull___lambda__1(x_168, x_169, x_171, x_170, x_173, x_186, x_3, x_4, x_5, x_6, x_7, x_185);
lean_dec(x_173);
lean_dec(x_170);
return x_187;
}
}
else
{
uint8_t x_188; 
lean_dec(x_173);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_188 = !lean_is_exclusive(x_174);
if (x_188 == 0)
{
return x_174;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_174, 0);
x_190 = lean_ctor_get(x_174, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_174);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
else
{
uint8_t x_192; 
x_192 = l_Lean_Expr_isLambda(x_1);
if (x_192 == 0)
{
uint8_t x_193; 
x_193 = l_Lean_Expr_isLambda(x_2);
if (x_193 == 0)
{
uint8_t x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_194 = 0;
x_195 = lean_box(x_194);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_8);
return x_196;
}
else
{
lean_object* x_197; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_197 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
if (lean_obj_tag(x_198) == 0)
{
uint8_t x_199; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_199 = !lean_is_exclusive(x_197);
if (x_199 == 0)
{
lean_object* x_200; uint8_t x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_197, 0);
lean_dec(x_200);
x_201 = 0;
x_202 = lean_box(x_201);
lean_ctor_set(x_197, 0, x_202);
return x_197;
}
else
{
lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; 
x_203 = lean_ctor_get(x_197, 1);
lean_inc(x_203);
lean_dec(x_197);
x_204 = 0;
x_205 = lean_box(x_204);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_203);
return x_206;
}
}
else
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_197, 1);
lean_inc(x_207);
lean_dec(x_197);
x_208 = lean_ctor_get(x_198, 0);
lean_inc(x_208);
lean_dec(x_198);
x_1 = x_208;
x_8 = x_207;
goto _start;
}
}
else
{
uint8_t x_210; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_210 = !lean_is_exclusive(x_197);
if (x_210 == 0)
{
return x_197;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_197, 0);
x_212 = lean_ctor_get(x_197, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_197);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
}
else
{
lean_object* x_214; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_214 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
if (lean_obj_tag(x_215) == 0)
{
uint8_t x_216; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_216 = !lean_is_exclusive(x_214);
if (x_216 == 0)
{
lean_object* x_217; uint8_t x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_214, 0);
lean_dec(x_217);
x_218 = 0;
x_219 = lean_box(x_218);
lean_ctor_set(x_214, 0, x_219);
return x_214;
}
else
{
lean_object* x_220; uint8_t x_221; lean_object* x_222; lean_object* x_223; 
x_220 = lean_ctor_get(x_214, 1);
lean_inc(x_220);
lean_dec(x_214);
x_221 = 0;
x_222 = lean_box(x_221);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_220);
return x_223;
}
}
else
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_ctor_get(x_214, 1);
lean_inc(x_224);
lean_dec(x_214);
x_225 = lean_ctor_get(x_215, 0);
lean_inc(x_225);
lean_dec(x_215);
x_2 = x_225;
x_8 = x_224;
goto _start;
}
}
else
{
uint8_t x_227; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_227 = !lean_is_exclusive(x_214);
if (x_227 == 0)
{
return x_214;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_214, 0);
x_229 = lean_ctor_get(x_214, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_214);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
}
}
}
}
case 7:
{
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_231 = lean_ctor_get(x_1, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_1, 1);
lean_inc(x_232);
x_233 = lean_ctor_get(x_1, 2);
lean_inc(x_233);
x_234 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_235 = lean_ctor_get(x_2, 1);
lean_inc(x_235);
x_236 = lean_ctor_get(x_2, 2);
lean_inc(x_236);
lean_dec(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_232);
x_237 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(x_232, x_235, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; uint8_t x_239; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_unbox(x_238);
lean_dec(x_238);
if (x_239 == 0)
{
uint8_t x_240; 
lean_dec(x_236);
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_240 = !lean_is_exclusive(x_237);
if (x_240 == 0)
{
lean_object* x_241; uint8_t x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_237, 0);
lean_dec(x_241);
x_242 = 0;
x_243 = lean_box(x_242);
lean_ctor_set(x_237, 0, x_243);
return x_237;
}
else
{
lean_object* x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; 
x_244 = lean_ctor_get(x_237, 1);
lean_inc(x_244);
lean_dec(x_237);
x_245 = 0;
x_246 = lean_box(x_245);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_244);
return x_247;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_237, 1);
lean_inc(x_248);
lean_dec(x_237);
x_249 = lean_box(0);
x_250 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull___lambda__1(x_231, x_232, x_234, x_233, x_236, x_249, x_3, x_4, x_5, x_6, x_7, x_248);
lean_dec(x_236);
lean_dec(x_233);
return x_250;
}
}
else
{
uint8_t x_251; 
lean_dec(x_236);
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_251 = !lean_is_exclusive(x_237);
if (x_251 == 0)
{
return x_237;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_237, 0);
x_253 = lean_ctor_get(x_237, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_237);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
return x_254;
}
}
}
else
{
uint8_t x_255; 
x_255 = l_Lean_Expr_isLambda(x_1);
if (x_255 == 0)
{
uint8_t x_256; 
x_256 = l_Lean_Expr_isLambda(x_2);
if (x_256 == 0)
{
uint8_t x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_257 = 0;
x_258 = lean_box(x_257);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_8);
return x_259;
}
else
{
lean_object* x_260; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_260 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; 
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
if (lean_obj_tag(x_261) == 0)
{
uint8_t x_262; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_262 = !lean_is_exclusive(x_260);
if (x_262 == 0)
{
lean_object* x_263; uint8_t x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_260, 0);
lean_dec(x_263);
x_264 = 0;
x_265 = lean_box(x_264);
lean_ctor_set(x_260, 0, x_265);
return x_260;
}
else
{
lean_object* x_266; uint8_t x_267; lean_object* x_268; lean_object* x_269; 
x_266 = lean_ctor_get(x_260, 1);
lean_inc(x_266);
lean_dec(x_260);
x_267 = 0;
x_268 = lean_box(x_267);
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_266);
return x_269;
}
}
else
{
lean_object* x_270; lean_object* x_271; 
x_270 = lean_ctor_get(x_260, 1);
lean_inc(x_270);
lean_dec(x_260);
x_271 = lean_ctor_get(x_261, 0);
lean_inc(x_271);
lean_dec(x_261);
x_1 = x_271;
x_8 = x_270;
goto _start;
}
}
else
{
uint8_t x_273; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_273 = !lean_is_exclusive(x_260);
if (x_273 == 0)
{
return x_260;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_260, 0);
x_275 = lean_ctor_get(x_260, 1);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_260);
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
return x_276;
}
}
}
}
else
{
lean_object* x_277; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_277 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
if (lean_obj_tag(x_278) == 0)
{
uint8_t x_279; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_279 = !lean_is_exclusive(x_277);
if (x_279 == 0)
{
lean_object* x_280; uint8_t x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_277, 0);
lean_dec(x_280);
x_281 = 0;
x_282 = lean_box(x_281);
lean_ctor_set(x_277, 0, x_282);
return x_277;
}
else
{
lean_object* x_283; uint8_t x_284; lean_object* x_285; lean_object* x_286; 
x_283 = lean_ctor_get(x_277, 1);
lean_inc(x_283);
lean_dec(x_277);
x_284 = 0;
x_285 = lean_box(x_284);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_283);
return x_286;
}
}
else
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_ctor_get(x_277, 1);
lean_inc(x_287);
lean_dec(x_277);
x_288 = lean_ctor_get(x_278, 0);
lean_inc(x_288);
lean_dec(x_278);
x_2 = x_288;
x_8 = x_287;
goto _start;
}
}
else
{
uint8_t x_290; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_290 = !lean_is_exclusive(x_277);
if (x_290 == 0)
{
return x_277;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_277, 0);
x_292 = lean_ctor_get(x_277, 1);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_277);
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
return x_293;
}
}
}
}
}
default: 
{
uint8_t x_294; 
x_294 = l_Lean_Expr_isLambda(x_1);
if (x_294 == 0)
{
uint8_t x_295; 
x_295 = l_Lean_Expr_isLambda(x_2);
if (x_295 == 0)
{
uint8_t x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_296 = 0;
x_297 = lean_box(x_296);
x_298 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_8);
return x_298;
}
else
{
lean_object* x_299; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_299 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
if (lean_obj_tag(x_300) == 0)
{
uint8_t x_301; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_301 = !lean_is_exclusive(x_299);
if (x_301 == 0)
{
lean_object* x_302; uint8_t x_303; lean_object* x_304; 
x_302 = lean_ctor_get(x_299, 0);
lean_dec(x_302);
x_303 = 0;
x_304 = lean_box(x_303);
lean_ctor_set(x_299, 0, x_304);
return x_299;
}
else
{
lean_object* x_305; uint8_t x_306; lean_object* x_307; lean_object* x_308; 
x_305 = lean_ctor_get(x_299, 1);
lean_inc(x_305);
lean_dec(x_299);
x_306 = 0;
x_307 = lean_box(x_306);
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_305);
return x_308;
}
}
else
{
lean_object* x_309; lean_object* x_310; 
x_309 = lean_ctor_get(x_299, 1);
lean_inc(x_309);
lean_dec(x_299);
x_310 = lean_ctor_get(x_300, 0);
lean_inc(x_310);
lean_dec(x_300);
x_1 = x_310;
x_8 = x_309;
goto _start;
}
}
else
{
uint8_t x_312; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_312 = !lean_is_exclusive(x_299);
if (x_312 == 0)
{
return x_299;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_299, 0);
x_314 = lean_ctor_get(x_299, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_299);
x_315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_314);
return x_315;
}
}
}
}
else
{
lean_object* x_316; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_316 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; 
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
if (lean_obj_tag(x_317) == 0)
{
uint8_t x_318; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_318 = !lean_is_exclusive(x_316);
if (x_318 == 0)
{
lean_object* x_319; uint8_t x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_316, 0);
lean_dec(x_319);
x_320 = 0;
x_321 = lean_box(x_320);
lean_ctor_set(x_316, 0, x_321);
return x_316;
}
else
{
lean_object* x_322; uint8_t x_323; lean_object* x_324; lean_object* x_325; 
x_322 = lean_ctor_get(x_316, 1);
lean_inc(x_322);
lean_dec(x_316);
x_323 = 0;
x_324 = lean_box(x_323);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_322);
return x_325;
}
}
else
{
lean_object* x_326; lean_object* x_327; 
x_326 = lean_ctor_get(x_316, 1);
lean_inc(x_326);
lean_dec(x_316);
x_327 = lean_ctor_get(x_317, 0);
lean_inc(x_327);
lean_dec(x_317);
x_2 = x_327;
x_8 = x_326;
goto _start;
}
}
else
{
uint8_t x_329; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_329 = !lean_is_exclusive(x_316);
if (x_329 == 0)
{
return x_316;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_330 = lean_ctor_get(x_316, 0);
x_331 = lean_ctor_get(x_316, 1);
lean_inc(x_331);
lean_inc(x_330);
lean_dec(x_316);
x_332 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
return x_332;
}
}
}
}
}
}
else
{
uint8_t x_333; lean_object* x_334; lean_object* x_335; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_333 = 1;
x_334 = lean_box(x_333);
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_8);
return x_335;
}
}
}
}
else
{
uint8_t x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_336 = 1;
x_337 = lean_box(x_336);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_8);
return x_338;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull___lambda__1(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_CompatibleTypes(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
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
