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
static lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__0;
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Compiler_LCNF_InferType_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isEquiv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_compatibleTypesQuick(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_List_isEqv___at___Lean_Compiler_LCNF_eqvTypes_spec__0(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_inferLambdaType_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compatibleTypesQuick___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_compatibleTypesQuick(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_10; uint8_t x_45; 
x_45 = l_Lean_Expr_isErased(x_1);
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = l_Lean_Expr_isErased(x_2);
x_10 = x_46;
goto block_44;
}
else
{
x_10 = x_45;
goto block_44;
}
block_9:
{
uint8_t x_7; 
x_7 = l_Lean_Compiler_LCNF_compatibleTypesQuick(x_3, x_5);
if (x_7 == 0)
{
lean_dec(x_6);
lean_dec(x_4);
return x_7;
}
else
{
x_1 = x_4;
x_2 = x_6;
goto _start;
}
}
block_44:
{
lean_object* x_11; 
x_11 = lean_box(1);
if (x_10 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc(x_1);
x_12 = l_Lean_Expr_headBeta(x_1);
lean_inc(x_2);
x_13 = l_Lean_Expr_headBeta(x_2);
x_14 = lean_expr_eqv(x_1, x_12);
if (x_14 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_13;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = lean_expr_eqv(x_2, x_13);
if (x_16 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_13;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_13);
lean_dec(x_12);
x_18 = lean_expr_eqv(x_1, x_2);
if (x_18 == 0)
{
switch (lean_obj_tag(x_1)) {
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = l_Lean_Level_isEquiv(x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
return x_21;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
case 4:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_dec(x_2);
x_26 = lean_name_eq(x_22, x_24);
lean_dec(x_24);
lean_dec(x_22);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_23);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = l_List_isEqv___at___Lean_Compiler_LCNF_eqvTypes_spec__0(x_23, x_25);
lean_dec(x_25);
lean_dec(x_23);
return x_27;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
case 5:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
lean_dec(x_2);
x_32 = l_Lean_Compiler_LCNF_compatibleTypesQuick(x_28, x_30);
if (x_32 == 0)
{
lean_dec(x_31);
lean_dec(x_29);
return x_32;
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
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
case 6:
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 2);
lean_inc(x_35);
lean_dec(x_1);
x_36 = lean_ctor_get(x_2, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_2, 2);
lean_inc(x_37);
lean_dec(x_2);
x_3 = x_34;
x_4 = x_35;
x_5 = x_36;
x_6 = x_37;
goto block_9;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
case 7:
{
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 2);
lean_inc(x_39);
lean_dec(x_1);
x_40 = lean_ctor_get(x_2, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 2);
lean_inc(x_41);
lean_dec(x_2);
x_3 = x_38;
x_4 = x_39;
x_5 = x_40;
x_6 = x_41;
goto block_9;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
default: 
{
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_unbox(x_11);
return x_42;
}
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_unbox(x_11);
return x_43;
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
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__0() {
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
x_15 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__0;
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
x_26 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_78; uint8_t x_140; 
x_140 = l_Lean_Expr_isErased(x_1);
if (x_140 == 0)
{
uint8_t x_141; 
x_141 = l_Lean_Expr_isErased(x_2);
x_78 = x_141;
goto block_139;
}
else
{
x_78 = x_140;
goto block_139;
}
block_35:
{
lean_object* x_21; 
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_10);
x_21 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(x_10, x_13, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_inferLambdaType_go_spec__0(x_15, x_16, x_17, x_18, x_19, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_26);
x_28 = l_Lean_Expr_fvar___override(x_26);
x_29 = lean_box(0);
x_30 = lean_unbox(x_29);
x_31 = l_Lean_LocalContext_mkLocalDecl(x_15, x_26, x_9, x_10, x_12, x_30);
x_32 = lean_expr_instantiate1(x_11, x_28);
lean_dec(x_11);
x_33 = lean_expr_instantiate1(x_14, x_28);
lean_dec(x_28);
lean_dec(x_14);
x_1 = x_32;
x_2 = x_33;
x_3 = x_31;
x_4 = x_16;
x_5 = x_17;
x_6 = x_18;
x_7 = x_19;
x_8 = x_27;
goto _start;
}
}
else
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_21;
}
}
block_77:
{
uint8_t x_43; 
x_43 = l_Lean_Expr_isLambda(x_1);
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = l_Lean_Expr_isLambda(x_2);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_box(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
else
{
lean_object* x_47; 
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
x_47 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_1, x_37, x_38, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 0);
lean_dec(x_50);
x_51 = lean_box(x_43);
lean_ctor_set(x_47, 0, x_51);
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 1);
lean_inc(x_52);
lean_dec(x_47);
x_53 = lean_box(x_43);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_47, 1);
lean_inc(x_55);
lean_dec(x_47);
x_56 = lean_ctor_get(x_48, 0);
lean_inc(x_56);
lean_dec(x_48);
x_1 = x_56;
x_3 = x_37;
x_4 = x_38;
x_5 = x_39;
x_6 = x_40;
x_7 = x_41;
x_8 = x_55;
goto _start;
}
}
else
{
uint8_t x_58; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_47);
if (x_58 == 0)
{
return x_47;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_47, 0);
x_60 = lean_ctor_get(x_47, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_47);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
else
{
lean_object* x_62; 
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
x_62 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_2, x_37, x_38, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_62, 0);
lean_dec(x_65);
x_66 = lean_box(x_36);
lean_ctor_set(x_62, 0, x_66);
return x_62;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
lean_dec(x_62);
x_68 = lean_box(x_36);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_62, 1);
lean_inc(x_70);
lean_dec(x_62);
x_71 = lean_ctor_get(x_63, 0);
lean_inc(x_71);
lean_dec(x_63);
x_2 = x_71;
x_3 = x_37;
x_4 = x_38;
x_5 = x_39;
x_6 = x_40;
x_7 = x_41;
x_8 = x_70;
goto _start;
}
}
else
{
uint8_t x_73; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_62);
if (x_73 == 0)
{
return x_62;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_62, 0);
x_75 = lean_ctor_get(x_62, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_62);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
block_139:
{
lean_object* x_79; 
x_79 = lean_box(1);
if (x_78 == 0)
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
lean_inc(x_1);
x_80 = l_Lean_Expr_headBeta(x_1);
lean_inc(x_2);
x_81 = l_Lean_Expr_headBeta(x_2);
x_82 = lean_expr_eqv(x_1, x_80);
if (x_82 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_80;
x_2 = x_81;
goto _start;
}
else
{
uint8_t x_84; 
x_84 = lean_expr_eqv(x_2, x_81);
if (x_84 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_80;
x_2 = x_81;
goto _start;
}
else
{
uint8_t x_86; 
lean_dec(x_81);
lean_dec(x_80);
x_86 = lean_expr_eqv(x_1, x_2);
if (x_86 == 0)
{
switch (lean_obj_tag(x_1)) {
case 3:
{
switch (lean_obj_tag(x_2)) {
case 3:
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_87 = lean_ctor_get(x_1, 0);
lean_inc(x_87);
lean_dec(x_1);
x_88 = lean_ctor_get(x_2, 0);
lean_inc(x_88);
lean_dec(x_2);
x_89 = l_Lean_Level_isEquiv(x_87, x_88);
lean_dec(x_88);
lean_dec(x_87);
x_90 = lean_box(x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_8);
return x_91;
}
case 10:
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_2, 1);
lean_inc(x_92);
lean_dec(x_2);
x_2 = x_92;
goto _start;
}
default: 
{
x_36 = x_86;
x_37 = x_3;
x_38 = x_4;
x_39 = x_5;
x_40 = x_6;
x_41 = x_7;
x_42 = x_8;
goto block_77;
}
}
}
case 4:
{
switch (lean_obj_tag(x_2)) {
case 4:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_94 = lean_ctor_get(x_1, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
lean_dec(x_1);
x_96 = lean_ctor_get(x_2, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_2, 1);
lean_inc(x_97);
lean_dec(x_2);
x_98 = lean_name_eq(x_94, x_96);
lean_dec(x_96);
lean_dec(x_94);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_97);
lean_dec(x_95);
x_99 = lean_box(x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_8);
return x_100;
}
else
{
uint8_t x_101; lean_object* x_102; lean_object* x_103; 
x_101 = l_List_isEqv___at___Lean_Compiler_LCNF_eqvTypes_spec__0(x_95, x_97);
lean_dec(x_97);
lean_dec(x_95);
x_102 = lean_box(x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_8);
return x_103;
}
}
case 10:
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_2, 1);
lean_inc(x_104);
lean_dec(x_2);
x_2 = x_104;
goto _start;
}
default: 
{
x_36 = x_86;
x_37 = x_3;
x_38 = x_4;
x_39 = x_5;
x_40 = x_6;
x_41 = x_7;
x_42 = x_8;
goto block_77;
}
}
}
case 5:
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_ctor_get(x_1, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_1, 1);
lean_inc(x_107);
lean_dec(x_1);
x_108 = lean_ctor_get(x_2, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_2, 1);
lean_inc(x_109);
lean_dec(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_110 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(x_106, x_108, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; uint8_t x_112; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_unbox(x_111);
lean_dec(x_111);
if (x_112 == 0)
{
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_110;
}
else
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
lean_dec(x_110);
x_1 = x_107;
x_2 = x_109;
x_8 = x_113;
goto _start;
}
}
else
{
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_110;
}
}
case 10:
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_2, 1);
lean_inc(x_115);
lean_dec(x_2);
x_2 = x_115;
goto _start;
}
default: 
{
x_36 = x_86;
x_37 = x_3;
x_38 = x_4;
x_39 = x_5;
x_40 = x_6;
x_41 = x_7;
x_42 = x_8;
goto block_77;
}
}
}
case 6:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; 
x_117 = lean_ctor_get(x_1, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_1, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_1, 2);
lean_inc(x_119);
x_120 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_121 = lean_ctor_get(x_2, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_2, 2);
lean_inc(x_122);
lean_dec(x_2);
x_9 = x_117;
x_10 = x_118;
x_11 = x_119;
x_12 = x_120;
x_13 = x_121;
x_14 = x_122;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
goto block_35;
}
case 10:
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_2, 1);
lean_inc(x_123);
lean_dec(x_2);
x_2 = x_123;
goto _start;
}
default: 
{
x_36 = x_86;
x_37 = x_3;
x_38 = x_4;
x_39 = x_5;
x_40 = x_6;
x_41 = x_7;
x_42 = x_8;
goto block_77;
}
}
}
case 7:
{
switch (lean_obj_tag(x_2)) {
case 7:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_125 = lean_ctor_get(x_1, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_1, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_1, 2);
lean_inc(x_127);
x_128 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_129 = lean_ctor_get(x_2, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_2, 2);
lean_inc(x_130);
lean_dec(x_2);
x_9 = x_125;
x_10 = x_126;
x_11 = x_127;
x_12 = x_128;
x_13 = x_129;
x_14 = x_130;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
goto block_35;
}
case 10:
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_2, 1);
lean_inc(x_131);
lean_dec(x_2);
x_2 = x_131;
goto _start;
}
default: 
{
x_36 = x_86;
x_37 = x_3;
x_38 = x_4;
x_39 = x_5;
x_40 = x_6;
x_41 = x_7;
x_42 = x_8;
goto block_77;
}
}
}
case 10:
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_1, 1);
lean_inc(x_133);
lean_dec(x_1);
x_1 = x_133;
goto _start;
}
default: 
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_2, 1);
lean_inc(x_135);
lean_dec(x_2);
x_2 = x_135;
goto _start;
}
else
{
x_36 = x_86;
x_37 = x_3;
x_38 = x_4;
x_39 = x_5;
x_40 = x_6;
x_41 = x_7;
x_42 = x_8;
goto block_77;
}
}
}
}
else
{
lean_object* x_137; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_79);
lean_ctor_set(x_137, 1, x_8);
return x_137;
}
}
}
}
else
{
lean_object* x_138; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_79);
lean_ctor_set(x_138, 1, x_8);
return x_138;
}
}
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
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
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
l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__0 = _init_l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
