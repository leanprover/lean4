// Lean compiler output
// Module: Init.Lean.Meta.InferType
// Imports: Init.Lean.Data.LBool Init.Lean.Meta.Basic
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
lean_object* l___private_Init_Lean_Meta_InferType_16__isArrowType___main(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Level_normalize___main(lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_4__inferForallType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Meta_isTypeFormerAux___main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_Meta_isTypeFormerAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
extern size_t l_PersistentHashMap_insertAux___main___rarg___closed__2;
lean_object* l___private_Init_Lean_Meta_InferType_15__isProofQuickApp___main___at_Lean_Meta_isProofQuick___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_sub(size_t, size_t);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProofQuick___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setInferTypeRef(lean_object*);
lean_object* l_Lean_Meta_instantiateLevelMVars(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_4__inferForallType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_5__inferLambdaType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_5__inferLambdaType___closed__1;
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l___private_Init_Lean_Meta_InferType_1__inferAppType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_8__inferFVarType(lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l___private_Init_Lean_Meta_InferType_9__checkInferTypeCache(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__7(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_13__isPropQuickApp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_2__inferConstType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_13__isPropQuickApp___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Meta_InferType_11__isAlwaysZero(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Meta_InferType_4__inferForallType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_15__isProofQuickApp___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_7__inferMVarType(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_14__isArrowProposition___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insert___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_12__isArrowProp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Literal_type(lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_InferType_3__inferProjType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_InferType_1__inferAppType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_11__isAlwaysZero___boxed(lean_object*);
lean_object* l_Lean_Meta_isPropQuick(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_2__mkAppRangeAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* lean_instantiate_type_lparams(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_14__isArrowProposition(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_4__inferForallType___closed__1;
extern lean_object* l_Lean_Meta_inferTypeRef;
extern lean_object* l_PersistentHashMap_insertAux___main___rarg___closed__3;
lean_object* l_Lean_Meta_isPropQuick___main(lean_object*, lean_object*, lean_object*);
size_t l_Lean_Expr_hash(lean_object*);
lean_object* l_PersistentHashMap_find_x3f___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_2__inferConstType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferTypeImpl(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_12__isArrowProp___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_1__inferAppType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_16__isArrowType___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_10__inferTypeAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_10__inferTypeAux(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__2(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_mkFreshId___rarg(lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*);
size_t l_USize_mul(size_t, size_t);
lean_object* l_Lean_Meta_setInferTypeRef___closed__1;
lean_object* l___private_Init_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_PersistentHashMap_find_x3f___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__1(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_12__isArrowProp___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_16__isArrowType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeQuick(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelSucc(lean_object*);
uint8_t lean_expr_equal(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_InferType_1__inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Bool_toLBool(uint8_t);
lean_object* l___private_Init_Lean_Meta_InferType_6__withLocalDecl___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_find_decl(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_5__inferLambdaType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormerAux___main___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_15__isProofQuickApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_16__isArrowType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_InferType_3__inferProjType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeQuick___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_4__inferForallType(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_6__withLocalDecl(lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_6__withLocalDecl___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_17__isTypeQuickApp___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Meta_InferType_4__inferForallType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar___rarg(lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_7__inferMVarType___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_17__isTypeQuickApp(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isClassQuick___main___closed__1;
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar(lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_11__isAlwaysZero___main___boxed(lean_object*);
lean_object* l_Lean_Meta_isTypeFormer(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_3__inferProjType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormerAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_InferType_12__isArrowProp(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Meta_InferType_11__isAlwaysZero___main(lean_object*);
lean_object* l_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProofQuick(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_InferType_1__inferAppType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_21 = lean_nat_sub(x_3, x_11);
x_22 = lean_nat_sub(x_21, x_10);
lean_dec(x_21);
x_23 = lean_ctor_get(x_5, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_5, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_25 = x_5;
} else {
 lean_dec_ref(x_5);
 x_25 = lean_box(0);
}
if (lean_obj_tag(x_24) == 7)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_25);
lean_dec(x_22);
x_54 = lean_ctor_get(x_24, 2);
lean_inc(x_54);
lean_dec(x_24);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_23);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_7);
x_12 = x_56;
goto block_20;
}
else
{
lean_object* x_57; 
x_57 = lean_box(0);
x_26 = x_57;
goto block_53;
}
block_20:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_4 = x_11;
x_5 = x_13;
x_7 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_1);
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
block_53:
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_26);
x_27 = lean_expr_instantiate_rev_range(x_24, x_23, x_22, x_2);
lean_dec(x_23);
lean_dec(x_24);
lean_inc(x_6);
x_28 = l_Lean_Meta_whnf(x_27, x_6, x_7);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
if (lean_obj_tag(x_29) == 7)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_31);
x_45 = lean_ctor_get(x_29, 2);
lean_inc(x_45);
lean_dec(x_29);
if (lean_is_scalar(x_25)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_25;
}
lean_ctor_set(x_46, 0, x_22);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_30);
x_12 = x_47;
goto block_20;
}
else
{
lean_object* x_48; 
lean_dec(x_29);
lean_dec(x_25);
x_48 = lean_box(0);
x_32 = x_48;
goto block_44;
}
block_44:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_32);
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_6, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_6, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 3, x_37);
lean_inc(x_1);
x_39 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_22, x_2, x_8, x_1);
x_40 = l_Lean_Expr_Inhabited;
x_41 = lean_array_get(x_40, x_2, x_22);
lean_dec(x_22);
x_42 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_38);
if (lean_is_scalar(x_31)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_31;
 lean_ctor_set_tag(x_43, 1);
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_30);
x_12 = x_43;
goto block_20;
}
}
else
{
uint8_t x_49; 
lean_dec(x_25);
lean_dec(x_22);
x_49 = !lean_is_exclusive(x_28);
if (x_49 == 0)
{
x_12 = x_28;
goto block_20;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_28, 0);
x_51 = lean_ctor_get(x_28, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_28);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_12 = x_52;
goto block_20;
}
}
}
}
else
{
lean_object* x_58; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_5);
lean_ctor_set(x_58, 1, x_7);
return x_58;
}
}
}
lean_object* l___private_Init_Lean_Meta_InferType_1__inferAppType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_Meta_inferType(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
x_10 = lean_array_get_size(x_2);
lean_inc(x_10);
x_11 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_InferType_1__inferAppType___spec__1(x_1, x_2, x_10, x_10, x_9, x_3, x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_expr_instantiate_rev_range(x_15, x_14, x_10, x_2);
lean_dec(x_10);
lean_dec(x_14);
lean_dec(x_15);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_expr_instantiate_rev_range(x_20, x_19, x_10, x_2);
lean_dec(x_10);
lean_dec(x_19);
lean_dec(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_10);
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_3);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_5);
if (x_27 == 0)
{
return x_5;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_InferType_1__inferAppType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_InferType_1__inferAppType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_InferType_1__inferAppType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_InferType_1__inferAppType(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_InferType_2__inferConstType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_5);
x_7 = lean_environment_find(x_5, x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_inc(x_8);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = l_Lean_ConstantInfo_lparams(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_List_lengthAux___main___rarg(x_15, x_16);
lean_dec(x_15);
x_18 = l_List_lengthAux___main___rarg(x_2, x_16);
x_19 = lean_nat_dec_eq(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
x_20 = lean_ctor_get(x_3, 1);
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_inc(x_20);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_22);
x_24 = lean_alloc_ctor(7, 3, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_2);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_4);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_26 = lean_instantiate_type_lparams(x_14, x_2);
lean_dec(x_2);
lean_dec(x_14);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_4);
return x_27;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_InferType_2__inferConstType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_InferType_2__inferConstType(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_InferType_3__inferProjType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_5, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_5, x_11);
lean_dec(x_5);
x_13 = lean_nat_sub(x_4, x_12);
x_14 = lean_nat_sub(x_13, x_11);
lean_dec(x_13);
lean_inc(x_7);
x_15 = l_Lean_Meta_whnf(x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 7)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 2);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Expr_hasLooseBVars(x_18);
if (x_19 == 0)
{
lean_dec(x_14);
x_5 = x_12;
x_6 = x_18;
x_8 = x_17;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_inc(x_3);
lean_inc(x_1);
x_21 = l_Lean_mkProj(x_1, x_14, x_3);
x_22 = lean_expr_instantiate1(x_18, x_21);
lean_dec(x_21);
lean_dec(x_18);
x_5 = x_12;
x_6 = x_22;
x_8 = x_17;
goto _start;
}
}
else
{
uint8_t x_24; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_15, 1);
x_26 = lean_ctor_get(x_15, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_7, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_7, 0);
lean_inc(x_30);
lean_dec(x_7);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_28);
lean_ctor_set(x_32, 2, x_29);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_2);
lean_ctor_set(x_33, 2, x_3);
lean_ctor_set(x_33, 3, x_32);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_33);
return x_15;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_15, 1);
lean_inc(x_34);
lean_dec(x_15);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_7, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_7, 0);
lean_inc(x_38);
lean_dec(x_7);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set(x_40, 2, x_37);
lean_ctor_set(x_40, 3, x_39);
x_41 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_2);
lean_ctor_set(x_41, 2, x_3);
lean_ctor_set(x_41, 3, x_40);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_34);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_15);
if (x_43 == 0)
{
return x_15;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_15, 0);
x_45 = lean_ctor_get(x_15, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_15);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_6);
lean_ctor_set(x_47, 1, x_8);
return x_47;
}
}
}
lean_object* l___private_Init_Lean_Meta_InferType_3__inferProjType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
x_6 = l_Lean_Meta_inferType(x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_4);
x_9 = l_Lean_Meta_whnf(x_7, x_4, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
x_15 = l_Lean_Expr_getAppFn___main(x_12);
if (lean_obj_tag(x_15) == 4)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_13);
x_18 = lean_environment_find(x_13, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_17);
lean_dec(x_12);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_4, 0);
lean_inc(x_20);
lean_dec(x_4);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_14);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_21);
x_23 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_2);
lean_ctor_set(x_23, 2, x_3);
lean_ctor_set(x_23, 3, x_22);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_23);
return x_9;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
if (lean_obj_tag(x_24) == 5)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_25, 4);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_12);
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_4, 0);
lean_inc(x_28);
lean_dec(x_4);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_13);
lean_ctor_set(x_30, 1, x_14);
lean_ctor_set(x_30, 2, x_27);
lean_ctor_set(x_30, 3, x_29);
x_31 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_2);
lean_ctor_set(x_31, 2, x_3);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_31);
return x_9;
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_dec(x_25);
x_34 = lean_ctor_get(x_26, 0);
lean_inc(x_34);
lean_dec(x_26);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Lean_Expr_getAppNumArgsAux___main(x_12, x_35);
x_37 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_36);
x_38 = lean_mk_array(x_36, x_37);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_sub(x_36, x_39);
lean_dec(x_36);
x_41 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_12, x_38, x_40);
x_42 = lean_array_get_size(x_41);
x_43 = lean_nat_dec_eq(x_33, x_42);
lean_dec(x_42);
lean_dec(x_33);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_17);
x_44 = lean_ctor_get(x_4, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_4, 0);
lean_inc(x_45);
lean_dec(x_4);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_13);
lean_ctor_set(x_47, 1, x_14);
lean_ctor_set(x_47, 2, x_44);
lean_ctor_set(x_47, 3, x_46);
x_48 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_2);
lean_ctor_set(x_48, 2, x_3);
lean_ctor_set(x_48, 3, x_47);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_48);
return x_9;
}
else
{
lean_object* x_49; 
lean_inc(x_34);
lean_inc(x_13);
x_49 = lean_environment_find(x_13, x_34);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_17);
x_50 = lean_ctor_get(x_4, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_4, 0);
lean_inc(x_51);
lean_dec(x_4);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_53, 0, x_13);
lean_ctor_set(x_53, 1, x_14);
lean_ctor_set(x_53, 2, x_50);
lean_ctor_set(x_53, 3, x_52);
x_54 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_2);
lean_ctor_set(x_54, 2, x_3);
lean_ctor_set(x_54, 3, x_53);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_54);
return x_9;
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_49);
lean_dec(x_14);
lean_dec(x_13);
lean_free_object(x_9);
x_55 = l_Lean_mkConst(x_34, x_17);
lean_inc(x_4);
x_56 = l___private_Init_Lean_Meta_InferType_1__inferAppType(x_55, x_41, x_4, x_11);
lean_dec(x_41);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_n(x_2, 2);
lean_inc(x_1);
x_59 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_InferType_3__inferProjType___spec__1(x_1, x_2, x_3, x_2, x_2, x_57, x_4, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_4);
x_62 = l_Lean_Meta_whnf(x_60, x_4, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 7)
{
uint8_t x_64; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_62, 0);
lean_dec(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
lean_ctor_set(x_62, 0, x_66);
return x_62;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
lean_dec(x_62);
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_dec(x_63);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec(x_63);
x_70 = !lean_is_exclusive(x_62);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_71 = lean_ctor_get(x_62, 1);
x_72 = lean_ctor_get(x_62, 0);
lean_dec(x_72);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_4, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_4, 0);
lean_inc(x_76);
lean_dec(x_4);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_78, 0, x_73);
lean_ctor_set(x_78, 1, x_74);
lean_ctor_set(x_78, 2, x_75);
lean_ctor_set(x_78, 3, x_77);
x_79 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set(x_79, 1, x_2);
lean_ctor_set(x_79, 2, x_3);
lean_ctor_set(x_79, 3, x_78);
lean_ctor_set_tag(x_62, 1);
lean_ctor_set(x_62, 0, x_79);
return x_62;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_80 = lean_ctor_get(x_62, 1);
lean_inc(x_80);
lean_dec(x_62);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_4, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_4, 0);
lean_inc(x_84);
lean_dec(x_4);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec(x_84);
x_86 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_86, 0, x_81);
lean_ctor_set(x_86, 1, x_82);
lean_ctor_set(x_86, 2, x_83);
lean_ctor_set(x_86, 3, x_85);
x_87 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_87, 0, x_1);
lean_ctor_set(x_87, 1, x_2);
lean_ctor_set(x_87, 2, x_3);
lean_ctor_set(x_87, 3, x_86);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_80);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_62);
if (x_89 == 0)
{
return x_62;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_62, 0);
x_91 = lean_ctor_get(x_62, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_62);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_59);
if (x_93 == 0)
{
return x_59;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_59, 0);
x_95 = lean_ctor_get(x_59, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_59);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_56);
if (x_97 == 0)
{
return x_56;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_56, 0);
x_99 = lean_ctor_get(x_56, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_56);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_32);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_12);
x_101 = lean_ctor_get(x_4, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_4, 0);
lean_inc(x_102);
lean_dec(x_4);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_104, 0, x_13);
lean_ctor_set(x_104, 1, x_14);
lean_ctor_set(x_104, 2, x_101);
lean_ctor_set(x_104, 3, x_103);
x_105 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_105, 0, x_1);
lean_ctor_set(x_105, 1, x_2);
lean_ctor_set(x_105, 2, x_3);
lean_ctor_set(x_105, 3, x_104);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_105);
return x_9;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_12);
x_106 = lean_ctor_get(x_4, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_4, 0);
lean_inc(x_107);
lean_dec(x_4);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_109, 0, x_13);
lean_ctor_set(x_109, 1, x_14);
lean_ctor_set(x_109, 2, x_106);
lean_ctor_set(x_109, 3, x_108);
x_110 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_110, 0, x_1);
lean_ctor_set(x_110, 1, x_2);
lean_ctor_set(x_110, 2, x_3);
lean_ctor_set(x_110, 3, x_109);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_110);
return x_9;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_15);
lean_dec(x_12);
x_111 = lean_ctor_get(x_4, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_4, 0);
lean_inc(x_112);
lean_dec(x_4);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
lean_dec(x_112);
x_114 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_114, 0, x_13);
lean_ctor_set(x_114, 1, x_14);
lean_ctor_set(x_114, 2, x_111);
lean_ctor_set(x_114, 3, x_113);
x_115 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_115, 0, x_1);
lean_ctor_set(x_115, 1, x_2);
lean_ctor_set(x_115, 2, x_3);
lean_ctor_set(x_115, 3, x_114);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_115);
return x_9;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_116 = lean_ctor_get(x_9, 1);
x_117 = lean_ctor_get(x_9, 0);
lean_inc(x_116);
lean_inc(x_117);
lean_dec(x_9);
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
x_120 = l_Lean_Expr_getAppFn___main(x_117);
if (lean_obj_tag(x_120) == 4)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
lean_inc(x_118);
x_123 = lean_environment_find(x_118, x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_122);
lean_dec(x_117);
x_124 = lean_ctor_get(x_4, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_4, 0);
lean_inc(x_125);
lean_dec(x_4);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_127, 0, x_118);
lean_ctor_set(x_127, 1, x_119);
lean_ctor_set(x_127, 2, x_124);
lean_ctor_set(x_127, 3, x_126);
x_128 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_128, 0, x_1);
lean_ctor_set(x_128, 1, x_2);
lean_ctor_set(x_128, 2, x_3);
lean_ctor_set(x_128, 3, x_127);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_116);
return x_129;
}
else
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_123, 0);
lean_inc(x_130);
lean_dec(x_123);
if (lean_obj_tag(x_130) == 5)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_dec(x_130);
x_132 = lean_ctor_get(x_131, 4);
lean_inc(x_132);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_131);
lean_dec(x_122);
lean_dec(x_117);
x_133 = lean_ctor_get(x_4, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_4, 0);
lean_inc(x_134);
lean_dec(x_4);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec(x_134);
x_136 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_136, 0, x_118);
lean_ctor_set(x_136, 1, x_119);
lean_ctor_set(x_136, 2, x_133);
lean_ctor_set(x_136, 3, x_135);
x_137 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_137, 0, x_1);
lean_ctor_set(x_137, 1, x_2);
lean_ctor_set(x_137, 2, x_3);
lean_ctor_set(x_137, 3, x_136);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_116);
return x_138;
}
else
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_132, 1);
lean_inc(x_139);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_140 = lean_ctor_get(x_131, 1);
lean_inc(x_140);
lean_dec(x_131);
x_141 = lean_ctor_get(x_132, 0);
lean_inc(x_141);
lean_dec(x_132);
x_142 = lean_unsigned_to_nat(0u);
x_143 = l_Lean_Expr_getAppNumArgsAux___main(x_117, x_142);
x_144 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_143);
x_145 = lean_mk_array(x_143, x_144);
x_146 = lean_unsigned_to_nat(1u);
x_147 = lean_nat_sub(x_143, x_146);
lean_dec(x_143);
x_148 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_117, x_145, x_147);
x_149 = lean_array_get_size(x_148);
x_150 = lean_nat_dec_eq(x_140, x_149);
lean_dec(x_149);
lean_dec(x_140);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_148);
lean_dec(x_141);
lean_dec(x_122);
x_151 = lean_ctor_get(x_4, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_4, 0);
lean_inc(x_152);
lean_dec(x_4);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
lean_dec(x_152);
x_154 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_154, 0, x_118);
lean_ctor_set(x_154, 1, x_119);
lean_ctor_set(x_154, 2, x_151);
lean_ctor_set(x_154, 3, x_153);
x_155 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_155, 0, x_1);
lean_ctor_set(x_155, 1, x_2);
lean_ctor_set(x_155, 2, x_3);
lean_ctor_set(x_155, 3, x_154);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_116);
return x_156;
}
else
{
lean_object* x_157; 
lean_inc(x_141);
lean_inc(x_118);
x_157 = lean_environment_find(x_118, x_141);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_148);
lean_dec(x_141);
lean_dec(x_122);
x_158 = lean_ctor_get(x_4, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_4, 0);
lean_inc(x_159);
lean_dec(x_4);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
lean_dec(x_159);
x_161 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_161, 0, x_118);
lean_ctor_set(x_161, 1, x_119);
lean_ctor_set(x_161, 2, x_158);
lean_ctor_set(x_161, 3, x_160);
x_162 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_162, 0, x_1);
lean_ctor_set(x_162, 1, x_2);
lean_ctor_set(x_162, 2, x_3);
lean_ctor_set(x_162, 3, x_161);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_116);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_157);
lean_dec(x_119);
lean_dec(x_118);
x_164 = l_Lean_mkConst(x_141, x_122);
lean_inc(x_4);
x_165 = l___private_Init_Lean_Meta_InferType_1__inferAppType(x_164, x_148, x_4, x_116);
lean_dec(x_148);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_n(x_2, 2);
lean_inc(x_1);
x_168 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_InferType_3__inferProjType___spec__1(x_1, x_2, x_3, x_2, x_2, x_166, x_4, x_167);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
lean_inc(x_4);
x_171 = l_Lean_Meta_whnf(x_169, x_4, x_170);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
if (lean_obj_tag(x_172) == 7)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_174 = x_171;
} else {
 lean_dec_ref(x_171);
 x_174 = lean_box(0);
}
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
lean_dec(x_172);
if (lean_is_scalar(x_174)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_174;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_173);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_172);
x_177 = lean_ctor_get(x_171, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_178 = x_171;
} else {
 lean_dec_ref(x_171);
 x_178 = lean_box(0);
}
x_179 = lean_ctor_get(x_177, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_177, 1);
lean_inc(x_180);
x_181 = lean_ctor_get(x_4, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_4, 0);
lean_inc(x_182);
lean_dec(x_4);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
lean_dec(x_182);
x_184 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_184, 0, x_179);
lean_ctor_set(x_184, 1, x_180);
lean_ctor_set(x_184, 2, x_181);
lean_ctor_set(x_184, 3, x_183);
x_185 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_185, 0, x_1);
lean_ctor_set(x_185, 1, x_2);
lean_ctor_set(x_185, 2, x_3);
lean_ctor_set(x_185, 3, x_184);
if (lean_is_scalar(x_178)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_178;
 lean_ctor_set_tag(x_186, 1);
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_177);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_187 = lean_ctor_get(x_171, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_171, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_189 = x_171;
} else {
 lean_dec_ref(x_171);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_188);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_191 = lean_ctor_get(x_168, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_168, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_193 = x_168;
} else {
 lean_dec_ref(x_168);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_195 = lean_ctor_get(x_165, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_165, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_197 = x_165;
} else {
 lean_dec_ref(x_165);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
}
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_139);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_122);
lean_dec(x_117);
x_199 = lean_ctor_get(x_4, 1);
lean_inc(x_199);
x_200 = lean_ctor_get(x_4, 0);
lean_inc(x_200);
lean_dec(x_4);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
lean_dec(x_200);
x_202 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_202, 0, x_118);
lean_ctor_set(x_202, 1, x_119);
lean_ctor_set(x_202, 2, x_199);
lean_ctor_set(x_202, 3, x_201);
x_203 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_203, 0, x_1);
lean_ctor_set(x_203, 1, x_2);
lean_ctor_set(x_203, 2, x_3);
lean_ctor_set(x_203, 3, x_202);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_116);
return x_204;
}
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_130);
lean_dec(x_122);
lean_dec(x_117);
x_205 = lean_ctor_get(x_4, 1);
lean_inc(x_205);
x_206 = lean_ctor_get(x_4, 0);
lean_inc(x_206);
lean_dec(x_4);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
lean_dec(x_206);
x_208 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_208, 0, x_118);
lean_ctor_set(x_208, 1, x_119);
lean_ctor_set(x_208, 2, x_205);
lean_ctor_set(x_208, 3, x_207);
x_209 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_209, 0, x_1);
lean_ctor_set(x_209, 1, x_2);
lean_ctor_set(x_209, 2, x_3);
lean_ctor_set(x_209, 3, x_208);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_116);
return x_210;
}
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_120);
lean_dec(x_117);
x_211 = lean_ctor_get(x_4, 1);
lean_inc(x_211);
x_212 = lean_ctor_get(x_4, 0);
lean_inc(x_212);
lean_dec(x_4);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
lean_dec(x_212);
x_214 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_214, 0, x_118);
lean_ctor_set(x_214, 1, x_119);
lean_ctor_set(x_214, 2, x_211);
lean_ctor_set(x_214, 3, x_213);
x_215 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_215, 0, x_1);
lean_ctor_set(x_215, 1, x_2);
lean_ctor_set(x_215, 2, x_3);
lean_ctor_set(x_215, 3, x_214);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_116);
return x_216;
}
}
}
else
{
uint8_t x_217; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_217 = !lean_is_exclusive(x_9);
if (x_217 == 0)
{
return x_9;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_9, 0);
x_219 = lean_ctor_get(x_9, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_9);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
}
else
{
uint8_t x_221; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_221 = !lean_is_exclusive(x_6);
if (x_221 == 0)
{
return x_6;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_6, 0);
x_223 = lean_ctor_get(x_6, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_6);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
}
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_InferType_3__inferProjType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_InferType_3__inferProjType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_Lean_Meta_getLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = l_Lean_Meta_inferType(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_2);
x_7 = l_Lean_Meta_whnfD(x_5, x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
switch (lean_obj_tag(x_8)) {
case 2:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_10);
x_11 = l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar(x_10, x_2, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_16);
x_18 = l_Lean_mkSort(x_16);
x_19 = l_Lean_Meta_assignExprMVar(x_10, x_18, x_2, x_17);
lean_dec(x_2);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_16);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_16);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_10);
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_11, 1);
x_30 = lean_ctor_get(x_11, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
lean_dec(x_2);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 2, x_33);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_37);
return x_11;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_11, 1);
lean_inc(x_38);
lean_dec(x_11);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 0);
lean_inc(x_42);
lean_dec(x_2);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_40);
lean_ctor_set(x_44, 2, x_41);
lean_ctor_set(x_44, 3, x_43);
x_45 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_38);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_11);
if (x_47 == 0)
{
return x_11;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_11, 0);
x_49 = lean_ctor_get(x_11, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_11);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
case 3:
{
uint8_t x_51; 
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_7);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_7, 0);
lean_dec(x_52);
x_53 = lean_ctor_get(x_8, 0);
lean_inc(x_53);
lean_dec(x_8);
lean_ctor_set(x_7, 0, x_53);
return x_7;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_7, 1);
lean_inc(x_54);
lean_dec(x_7);
x_55 = lean_ctor_get(x_8, 0);
lean_inc(x_55);
lean_dec(x_8);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
default: 
{
uint8_t x_57; 
lean_dec(x_8);
x_57 = !lean_is_exclusive(x_7);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = lean_ctor_get(x_7, 1);
x_59 = lean_ctor_get(x_7, 0);
lean_dec(x_59);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_2, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_2, 0);
lean_inc(x_63);
lean_dec(x_2);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_61);
lean_ctor_set(x_65, 2, x_62);
lean_ctor_set(x_65, 3, x_64);
x_66 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_66, 0, x_1);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_66);
return x_7;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_67 = lean_ctor_get(x_7, 1);
lean_inc(x_67);
lean_dec(x_7);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_2, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_2, 0);
lean_inc(x_71);
lean_dec(x_2);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_73, 0, x_68);
lean_ctor_set(x_73, 1, x_69);
lean_ctor_set(x_73, 2, x_70);
lean_ctor_set(x_73, 3, x_72);
x_74 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_74, 0, x_1);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_67);
return x_75;
}
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_7);
if (x_76 == 0)
{
return x_7;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_7, 0);
x_78 = lean_ctor_get(x_7, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_7);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_4);
if (x_80 == 0)
{
return x_4;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_4, 0);
x_82 = lean_ctor_get(x_4, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_4);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Meta_InferType_4__inferForallType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_3, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_3, x_10);
lean_dec(x_3);
x_12 = lean_array_fget(x_2, x_11);
lean_inc(x_6);
x_13 = l_Lean_Meta_inferType(x_12, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_6);
x_16 = l_Lean_Meta_getLevel(x_14, x_6, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_mkLevelIMax(x_17, x_5);
x_3 = x_11;
x_4 = lean_box(0);
x_5 = x_19;
x_7 = x_18;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
return x_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; 
lean_dec(x_6);
lean_dec(x_3);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_5);
lean_ctor_set(x_29, 1, x_7);
return x_29;
}
}
}
lean_object* l___private_Init_Lean_Meta_InferType_4__inferForallType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Meta_getLevel(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_array_get_size(x_1);
x_9 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Meta_InferType_4__inferForallType___spec__1(x_1, x_1, x_8, lean_box(0), x_6, x_3, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_Level_normalize___main(x_11);
lean_dec(x_11);
x_13 = l_Lean_mkSort(x_12);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = l_Lean_Level_normalize___main(x_14);
lean_dec(x_14);
x_17 = l_Lean_mkSort(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_5);
if (x_23 == 0)
{
return x_5;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_5, 0);
x_25 = lean_ctor_get(x_5, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_5);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* _init_l___private_Init_Lean_Meta_InferType_4__inferForallType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_InferType_4__inferForallType___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* l___private_Init_Lean_Meta_InferType_4__inferForallType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Init_Lean_Meta_InferType_4__inferForallType___closed__1;
x_5 = l_Lean_Meta_forallTelescope___rarg(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Meta_InferType_4__inferForallType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Meta_InferType_4__inferForallType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_InferType_4__inferForallType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_InferType_4__inferForallType___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_InferType_5__inferLambdaType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Meta_inferType(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Meta_mkForall(x_1, x_6, x_3, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* _init_l___private_Init_Lean_Meta_InferType_5__inferLambdaType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_InferType_5__inferLambdaType___lambda__1), 4, 0);
return x_1;
}
}
lean_object* l___private_Init_Lean_Meta_InferType_5__inferLambdaType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Init_Lean_Meta_InferType_5__inferLambdaType___closed__1;
x_5 = l_Lean_Meta_lambdaTelescope___rarg(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_InferType_6__withLocalDecl___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
x_8 = l_Lean_Meta_mkFreshId___rarg(x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_9);
x_11 = l_Lean_mkFVar(x_9);
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_local_ctx_mk_local_decl(x_13, x_9, x_1, x_3, x_2);
lean_ctor_set(x_5, 1, x_14);
x_15 = lean_apply_3(x_4, x_11, x_5, x_10);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_15, 1);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 2);
lean_dec(x_19);
lean_ctor_set(x_17, 2, x_7);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
x_22 = lean_ctor_get(x_17, 3);
x_23 = lean_ctor_get(x_17, 4);
x_24 = lean_ctor_get(x_17, 5);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_7);
lean_ctor_set(x_25, 3, x_22);
lean_ctor_set(x_25, 4, x_23);
lean_ctor_set(x_25, 5, x_24);
lean_ctor_set(x_15, 1, x_25);
return x_15;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_15, 1);
x_27 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_inc(x_27);
lean_dec(x_15);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_26, 4);
lean_inc(x_31);
x_32 = lean_ctor_get(x_26, 5);
lean_inc(x_32);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 lean_ctor_release(x_26, 3);
 lean_ctor_release(x_26, 4);
 lean_ctor_release(x_26, 5);
 x_33 = x_26;
} else {
 lean_dec_ref(x_26);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 6, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_29);
lean_ctor_set(x_34, 2, x_7);
lean_ctor_set(x_34, 3, x_30);
lean_ctor_set(x_34, 4, x_31);
lean_ctor_set(x_34, 5, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_15);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_15, 1);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 2);
lean_dec(x_39);
lean_ctor_set(x_37, 2, x_7);
return x_15;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_37, 0);
x_41 = lean_ctor_get(x_37, 1);
x_42 = lean_ctor_get(x_37, 3);
x_43 = lean_ctor_get(x_37, 4);
x_44 = lean_ctor_get(x_37, 5);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_37);
x_45 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_41);
lean_ctor_set(x_45, 2, x_7);
lean_ctor_set(x_45, 3, x_42);
lean_ctor_set(x_45, 4, x_43);
lean_ctor_set(x_45, 5, x_44);
lean_ctor_set(x_15, 1, x_45);
return x_15;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_46 = lean_ctor_get(x_15, 1);
x_47 = lean_ctor_get(x_15, 0);
lean_inc(x_46);
lean_inc(x_47);
lean_dec(x_15);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_46, 3);
lean_inc(x_50);
x_51 = lean_ctor_get(x_46, 4);
lean_inc(x_51);
x_52 = lean_ctor_get(x_46, 5);
lean_inc(x_52);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 lean_ctor_release(x_46, 4);
 lean_ctor_release(x_46, 5);
 x_53 = x_46;
} else {
 lean_dec_ref(x_46);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 6, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_49);
lean_ctor_set(x_54, 2, x_7);
lean_ctor_set(x_54, 3, x_50);
lean_ctor_set(x_54, 4, x_51);
lean_ctor_set(x_54, 5, x_52);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = lean_ctor_get(x_5, 0);
x_57 = lean_ctor_get(x_5, 1);
x_58 = lean_ctor_get(x_5, 2);
x_59 = lean_ctor_get(x_5, 3);
x_60 = lean_ctor_get(x_5, 4);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_5);
x_61 = lean_local_ctx_mk_local_decl(x_57, x_9, x_1, x_3, x_2);
x_62 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_62, 2, x_58);
lean_ctor_set(x_62, 3, x_59);
lean_ctor_set(x_62, 4, x_60);
x_63 = lean_apply_3(x_4, x_11, x_62, x_10);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = lean_ctor_get(x_64, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_64, 3);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 4);
lean_inc(x_70);
x_71 = lean_ctor_get(x_64, 5);
lean_inc(x_71);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 lean_ctor_release(x_64, 2);
 lean_ctor_release(x_64, 3);
 lean_ctor_release(x_64, 4);
 lean_ctor_release(x_64, 5);
 x_72 = x_64;
} else {
 lean_dec_ref(x_64);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 6, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_67);
lean_ctor_set(x_73, 1, x_68);
lean_ctor_set(x_73, 2, x_7);
lean_ctor_set(x_73, 3, x_69);
lean_ctor_set(x_73, 4, x_70);
lean_ctor_set(x_73, 5, x_71);
if (lean_is_scalar(x_66)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_66;
}
lean_ctor_set(x_74, 0, x_65);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_75 = lean_ctor_get(x_63, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_63, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_77 = x_63;
} else {
 lean_dec_ref(x_63);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_75, 3);
lean_inc(x_80);
x_81 = lean_ctor_get(x_75, 4);
lean_inc(x_81);
x_82 = lean_ctor_get(x_75, 5);
lean_inc(x_82);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 lean_ctor_release(x_75, 4);
 lean_ctor_release(x_75, 5);
 x_83 = x_75;
} else {
 lean_dec_ref(x_75);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 6, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set(x_84, 1, x_79);
lean_ctor_set(x_84, 2, x_7);
lean_ctor_set(x_84, 3, x_80);
lean_ctor_set(x_84, 4, x_81);
lean_ctor_set(x_84, 5, x_82);
if (lean_is_scalar(x_77)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_77;
}
lean_ctor_set(x_85, 0, x_76);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_InferType_6__withLocalDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_InferType_6__withLocalDecl___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_InferType_6__withLocalDecl___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l___private_Init_Lean_Meta_InferType_6__withLocalDecl___rarg(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_InferType_7__inferMVarType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_5);
x_6 = lean_metavar_ctx_find_decl(x_5, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_inc(x_7);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_9);
x_11 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
}
lean_object* l___private_Init_Lean_Meta_InferType_7__inferMVarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_InferType_7__inferMVarType(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_InferType_8__inferFVarType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_4);
x_5 = lean_local_ctx_find(x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_4);
lean_ctor_set(x_10, 3, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
x_14 = l_Lean_LocalDecl_type(x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_expr_equal(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
lean_object* l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_expr_equal(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = x_2 >> x_5;
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__3(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_PersistentHashMap_find_x3f___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Expr_hash(x_2);
x_5 = l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__2(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_expr_equal(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__7(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Expr_hash(x_9);
x_12 = 1;
x_13 = x_1 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
x_16 = x_11 >> x_15;
x_17 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__5(x_6, x_16, x_1, x_9, x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_5 = x_19;
x_6 = x_17;
goto _start;
}
}
}
lean_object* l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_11 = x_2 & x_10;
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(2);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_expr_equal(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_expr_equal(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = x_2 >> x_9;
x_37 = x_3 + x_8;
x_38 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__5(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = x_2 >> x_9;
x_42 = x_3 + x_8;
x_43 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__5(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_52 = x_2 & x_51;
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(2);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = lean_expr_equal(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = x_2 >> x_50;
x_74 = x_3 + x_49;
x_75 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__5(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; size_t x_84; uint8_t x_85; 
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_PersistentHashMap_insertAtCollisionNodeAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__6(x_1, x_82, x_4, x_5);
x_84 = 7;
x_85 = x_84 <= x_3;
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = l_PersistentHashMap_getCollisionNodeSize___rarg(x_83);
x_87 = lean_unsigned_to_nat(4u);
x_88 = lean_nat_dec_lt(x_86, x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
lean_dec(x_83);
x_91 = l_PersistentHashMap_insertAux___main___rarg___closed__3;
x_92 = l_Array_iterateMAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__7(x_3, x_89, x_90, x_89, x_82, x_91);
lean_dec(x_90);
lean_dec(x_89);
return x_92;
}
else
{
return x_83;
}
}
else
{
return x_83;
}
}
}
}
lean_object* l_PersistentHashMap_insert___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Expr_hash(x_2);
x_8 = 1;
x_9 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__5(x_5, x_7, x_8, x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = l_Lean_Expr_hash(x_2);
x_15 = 1;
x_16 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__5(x_12, x_14, x_15, x_2, x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_13, x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
lean_object* l___private_Init_Lean_Meta_InferType_9__checkInferTypeCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_PersistentHashMap_find_x3f___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__1(x_6, x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_apply_2(x_2, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_9, 2);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_18 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__4(x_17, x_1, x_12);
lean_ctor_set(x_10, 0, x_18);
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
x_21 = lean_ctor_get(x_10, 2);
x_22 = lean_ctor_get(x_10, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
lean_inc(x_12);
x_23 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__4(x_19, x_1, x_12);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_22);
lean_ctor_set(x_9, 2, x_24);
return x_8;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_25 = lean_ctor_get(x_9, 0);
x_26 = lean_ctor_get(x_9, 1);
x_27 = lean_ctor_get(x_9, 3);
x_28 = lean_ctor_get(x_9, 4);
x_29 = lean_ctor_get(x_9, 5);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_9);
x_30 = lean_ctor_get(x_10, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_10, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_10, 3);
lean_inc(x_33);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 lean_ctor_release(x_10, 2);
 lean_ctor_release(x_10, 3);
 x_34 = x_10;
} else {
 lean_dec_ref(x_10);
 x_34 = lean_box(0);
}
lean_inc(x_12);
x_35 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__4(x_30, x_1, x_12);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 4, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
lean_ctor_set(x_36, 2, x_32);
lean_ctor_set(x_36, 3, x_33);
x_37 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_37, 0, x_25);
lean_ctor_set(x_37, 1, x_26);
lean_ctor_set(x_37, 2, x_36);
lean_ctor_set(x_37, 3, x_27);
lean_ctor_set(x_37, 4, x_28);
lean_ctor_set(x_37, 5, x_29);
lean_ctor_set(x_8, 1, x_37);
return x_8;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_38 = lean_ctor_get(x_8, 0);
lean_inc(x_38);
lean_dec(x_8);
x_39 = lean_ctor_get(x_9, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_9, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_9, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_9, 4);
lean_inc(x_42);
x_43 = lean_ctor_get(x_9, 5);
lean_inc(x_43);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 lean_ctor_release(x_9, 2);
 lean_ctor_release(x_9, 3);
 lean_ctor_release(x_9, 4);
 lean_ctor_release(x_9, 5);
 x_44 = x_9;
} else {
 lean_dec_ref(x_9);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_10, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_10, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_10, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_10, 3);
lean_inc(x_48);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 lean_ctor_release(x_10, 2);
 lean_ctor_release(x_10, 3);
 x_49 = x_10;
} else {
 lean_dec_ref(x_10);
 x_49 = lean_box(0);
}
lean_inc(x_38);
x_50 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__4(x_45, x_1, x_38);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 4, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_46);
lean_ctor_set(x_51, 2, x_47);
lean_ctor_set(x_51, 3, x_48);
if (lean_is_scalar(x_44)) {
 x_52 = lean_alloc_ctor(0, 6, 0);
} else {
 x_52 = x_44;
}
lean_ctor_set(x_52, 0, x_39);
lean_ctor_set(x_52, 1, x_40);
lean_ctor_set(x_52, 2, x_51);
lean_ctor_set(x_52, 3, x_41);
lean_ctor_set(x_52, 4, x_42);
lean_ctor_set(x_52, 5, x_43);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_38);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_8);
if (x_54 == 0)
{
return x_8;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_8, 0);
x_56 = lean_ctor_get(x_8, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_8);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = lean_ctor_get(x_7, 0);
lean_inc(x_58);
lean_dec(x_7);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_4);
return x_59;
}
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_PersistentHashMap_find_x3f___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find_x3f___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Array_iterateMAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__7(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__5(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_InferType_10__inferTypeAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l___private_Init_Lean_Meta_InferType_8__inferFVarType(x_7, x_2, x_3);
return x_8;
}
case 2:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l___private_Init_Lean_Meta_InferType_7__inferMVarType(x_9, x_2, x_3);
lean_dec(x_2);
return x_10;
}
case 3:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_mkLevelSucc(x_11);
x_13 = l_Lean_mkSort(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
case 4:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l___private_Init_Lean_Meta_InferType_2__inferConstType(x_15, x_16, x_2, x_3);
lean_dec(x_2);
return x_17;
}
case 5:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = l_Lean_Expr_getAppFn___main(x_18);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_20);
x_22 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_21);
x_23 = lean_mk_array(x_21, x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_21, x_24);
lean_dec(x_21);
lean_inc(x_1);
x_26 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_1, x_23, x_25);
x_27 = lean_ctor_get(x_3, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_PersistentHashMap_find_x3f___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__1(x_28, x_1);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = l___private_Init_Lean_Meta_InferType_1__inferAppType(x_19, x_26, x_2, x_3);
lean_dec(x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 2);
lean_inc(x_32);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_30, 1);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_31, 2);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_32);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_40 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__4(x_39, x_1, x_34);
lean_ctor_set(x_32, 0, x_40);
return x_30;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_32, 0);
x_42 = lean_ctor_get(x_32, 1);
x_43 = lean_ctor_get(x_32, 2);
x_44 = lean_ctor_get(x_32, 3);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_32);
lean_inc(x_34);
x_45 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__4(x_41, x_1, x_34);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
lean_ctor_set(x_46, 2, x_43);
lean_ctor_set(x_46, 3, x_44);
lean_ctor_set(x_31, 2, x_46);
return x_30;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_47 = lean_ctor_get(x_31, 0);
x_48 = lean_ctor_get(x_31, 1);
x_49 = lean_ctor_get(x_31, 3);
x_50 = lean_ctor_get(x_31, 4);
x_51 = lean_ctor_get(x_31, 5);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_31);
x_52 = lean_ctor_get(x_32, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_32, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_32, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_32, 3);
lean_inc(x_55);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 x_56 = x_32;
} else {
 lean_dec_ref(x_32);
 x_56 = lean_box(0);
}
lean_inc(x_34);
x_57 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__4(x_52, x_1, x_34);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 4, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_53);
lean_ctor_set(x_58, 2, x_54);
lean_ctor_set(x_58, 3, x_55);
x_59 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_59, 0, x_47);
lean_ctor_set(x_59, 1, x_48);
lean_ctor_set(x_59, 2, x_58);
lean_ctor_set(x_59, 3, x_49);
lean_ctor_set(x_59, 4, x_50);
lean_ctor_set(x_59, 5, x_51);
lean_ctor_set(x_30, 1, x_59);
return x_30;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_60 = lean_ctor_get(x_30, 0);
lean_inc(x_60);
lean_dec(x_30);
x_61 = lean_ctor_get(x_31, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_31, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_31, 3);
lean_inc(x_63);
x_64 = lean_ctor_get(x_31, 4);
lean_inc(x_64);
x_65 = lean_ctor_get(x_31, 5);
lean_inc(x_65);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 lean_ctor_release(x_31, 3);
 lean_ctor_release(x_31, 4);
 lean_ctor_release(x_31, 5);
 x_66 = x_31;
} else {
 lean_dec_ref(x_31);
 x_66 = lean_box(0);
}
x_67 = lean_ctor_get(x_32, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_32, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_32, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_32, 3);
lean_inc(x_70);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 x_71 = x_32;
} else {
 lean_dec_ref(x_32);
 x_71 = lean_box(0);
}
lean_inc(x_60);
x_72 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__4(x_67, x_1, x_60);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 4, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_68);
lean_ctor_set(x_73, 2, x_69);
lean_ctor_set(x_73, 3, x_70);
if (lean_is_scalar(x_66)) {
 x_74 = lean_alloc_ctor(0, 6, 0);
} else {
 x_74 = x_66;
}
lean_ctor_set(x_74, 0, x_61);
lean_ctor_set(x_74, 1, x_62);
lean_ctor_set(x_74, 2, x_73);
lean_ctor_set(x_74, 3, x_63);
lean_ctor_set(x_74, 4, x_64);
lean_ctor_set(x_74, 5, x_65);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_60);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
else
{
uint8_t x_76; 
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_30);
if (x_76 == 0)
{
return x_30;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_30, 0);
x_78 = lean_ctor_get(x_30, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_30);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
x_80 = lean_ctor_get(x_29, 0);
lean_inc(x_80);
lean_dec(x_29);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_3);
return x_81;
}
}
case 7:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_3, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec(x_82);
x_84 = l_PersistentHashMap_find_x3f___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__1(x_83, x_1);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = l___private_Init_Lean_Meta_InferType_4__inferForallType___closed__1;
lean_inc(x_1);
x_86 = l_Lean_Meta_forallTelescope___rarg(x_1, x_85, x_2, x_3);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_87, 2);
lean_inc(x_88);
x_89 = !lean_is_exclusive(x_86);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = lean_ctor_get(x_86, 0);
x_91 = lean_ctor_get(x_86, 1);
lean_dec(x_91);
x_92 = !lean_is_exclusive(x_87);
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_87, 2);
lean_dec(x_93);
x_94 = !lean_is_exclusive(x_88);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
x_96 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__4(x_95, x_1, x_90);
lean_ctor_set(x_88, 0, x_96);
return x_86;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_97 = lean_ctor_get(x_88, 0);
x_98 = lean_ctor_get(x_88, 1);
x_99 = lean_ctor_get(x_88, 2);
x_100 = lean_ctor_get(x_88, 3);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_88);
lean_inc(x_90);
x_101 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__4(x_97, x_1, x_90);
x_102 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_98);
lean_ctor_set(x_102, 2, x_99);
lean_ctor_set(x_102, 3, x_100);
lean_ctor_set(x_87, 2, x_102);
return x_86;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_103 = lean_ctor_get(x_87, 0);
x_104 = lean_ctor_get(x_87, 1);
x_105 = lean_ctor_get(x_87, 3);
x_106 = lean_ctor_get(x_87, 4);
x_107 = lean_ctor_get(x_87, 5);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_87);
x_108 = lean_ctor_get(x_88, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_88, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_88, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_88, 3);
lean_inc(x_111);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 lean_ctor_release(x_88, 2);
 lean_ctor_release(x_88, 3);
 x_112 = x_88;
} else {
 lean_dec_ref(x_88);
 x_112 = lean_box(0);
}
lean_inc(x_90);
x_113 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__4(x_108, x_1, x_90);
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(0, 4, 0);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_109);
lean_ctor_set(x_114, 2, x_110);
lean_ctor_set(x_114, 3, x_111);
x_115 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_115, 0, x_103);
lean_ctor_set(x_115, 1, x_104);
lean_ctor_set(x_115, 2, x_114);
lean_ctor_set(x_115, 3, x_105);
lean_ctor_set(x_115, 4, x_106);
lean_ctor_set(x_115, 5, x_107);
lean_ctor_set(x_86, 1, x_115);
return x_86;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_116 = lean_ctor_get(x_86, 0);
lean_inc(x_116);
lean_dec(x_86);
x_117 = lean_ctor_get(x_87, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_87, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_87, 3);
lean_inc(x_119);
x_120 = lean_ctor_get(x_87, 4);
lean_inc(x_120);
x_121 = lean_ctor_get(x_87, 5);
lean_inc(x_121);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 lean_ctor_release(x_87, 2);
 lean_ctor_release(x_87, 3);
 lean_ctor_release(x_87, 4);
 lean_ctor_release(x_87, 5);
 x_122 = x_87;
} else {
 lean_dec_ref(x_87);
 x_122 = lean_box(0);
}
x_123 = lean_ctor_get(x_88, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_88, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_88, 2);
lean_inc(x_125);
x_126 = lean_ctor_get(x_88, 3);
lean_inc(x_126);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 lean_ctor_release(x_88, 2);
 lean_ctor_release(x_88, 3);
 x_127 = x_88;
} else {
 lean_dec_ref(x_88);
 x_127 = lean_box(0);
}
lean_inc(x_116);
x_128 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__4(x_123, x_1, x_116);
if (lean_is_scalar(x_127)) {
 x_129 = lean_alloc_ctor(0, 4, 0);
} else {
 x_129 = x_127;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_124);
lean_ctor_set(x_129, 2, x_125);
lean_ctor_set(x_129, 3, x_126);
if (lean_is_scalar(x_122)) {
 x_130 = lean_alloc_ctor(0, 6, 0);
} else {
 x_130 = x_122;
}
lean_ctor_set(x_130, 0, x_117);
lean_ctor_set(x_130, 1, x_118);
lean_ctor_set(x_130, 2, x_129);
lean_ctor_set(x_130, 3, x_119);
lean_ctor_set(x_130, 4, x_120);
lean_ctor_set(x_130, 5, x_121);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_116);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
else
{
uint8_t x_132; 
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_86);
if (x_132 == 0)
{
return x_86;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_86, 0);
x_134 = lean_ctor_get(x_86, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_86);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
else
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_2);
lean_dec(x_1);
x_136 = lean_ctor_get(x_84, 0);
lean_inc(x_136);
lean_dec(x_84);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_3);
return x_137;
}
}
case 9:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_2);
x_138 = lean_ctor_get(x_1, 0);
lean_inc(x_138);
lean_dec(x_1);
x_139 = l_Lean_Literal_type(x_138);
lean_dec(x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_3);
return x_140;
}
case 10:
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_1, 1);
lean_inc(x_141);
lean_dec(x_1);
x_1 = x_141;
goto _start;
}
case 11:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_143 = lean_ctor_get(x_1, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_1, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_1, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_3, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_dec(x_146);
x_148 = l_PersistentHashMap_find_x3f___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__1(x_147, x_1);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; 
x_149 = l___private_Init_Lean_Meta_InferType_3__inferProjType(x_143, x_144, x_145, x_2, x_3);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
x_151 = lean_ctor_get(x_150, 2);
lean_inc(x_151);
x_152 = !lean_is_exclusive(x_149);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_153 = lean_ctor_get(x_149, 0);
x_154 = lean_ctor_get(x_149, 1);
lean_dec(x_154);
x_155 = !lean_is_exclusive(x_150);
if (x_155 == 0)
{
lean_object* x_156; uint8_t x_157; 
x_156 = lean_ctor_get(x_150, 2);
lean_dec(x_156);
x_157 = !lean_is_exclusive(x_151);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_151, 0);
lean_inc(x_153);
x_159 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__4(x_158, x_1, x_153);
lean_ctor_set(x_151, 0, x_159);
return x_149;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_160 = lean_ctor_get(x_151, 0);
x_161 = lean_ctor_get(x_151, 1);
x_162 = lean_ctor_get(x_151, 2);
x_163 = lean_ctor_get(x_151, 3);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_151);
lean_inc(x_153);
x_164 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__4(x_160, x_1, x_153);
x_165 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_161);
lean_ctor_set(x_165, 2, x_162);
lean_ctor_set(x_165, 3, x_163);
lean_ctor_set(x_150, 2, x_165);
return x_149;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_166 = lean_ctor_get(x_150, 0);
x_167 = lean_ctor_get(x_150, 1);
x_168 = lean_ctor_get(x_150, 3);
x_169 = lean_ctor_get(x_150, 4);
x_170 = lean_ctor_get(x_150, 5);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_150);
x_171 = lean_ctor_get(x_151, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_151, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_151, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_151, 3);
lean_inc(x_174);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 lean_ctor_release(x_151, 2);
 lean_ctor_release(x_151, 3);
 x_175 = x_151;
} else {
 lean_dec_ref(x_151);
 x_175 = lean_box(0);
}
lean_inc(x_153);
x_176 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__4(x_171, x_1, x_153);
if (lean_is_scalar(x_175)) {
 x_177 = lean_alloc_ctor(0, 4, 0);
} else {
 x_177 = x_175;
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_172);
lean_ctor_set(x_177, 2, x_173);
lean_ctor_set(x_177, 3, x_174);
x_178 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_178, 0, x_166);
lean_ctor_set(x_178, 1, x_167);
lean_ctor_set(x_178, 2, x_177);
lean_ctor_set(x_178, 3, x_168);
lean_ctor_set(x_178, 4, x_169);
lean_ctor_set(x_178, 5, x_170);
lean_ctor_set(x_149, 1, x_178);
return x_149;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_179 = lean_ctor_get(x_149, 0);
lean_inc(x_179);
lean_dec(x_149);
x_180 = lean_ctor_get(x_150, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_150, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_150, 3);
lean_inc(x_182);
x_183 = lean_ctor_get(x_150, 4);
lean_inc(x_183);
x_184 = lean_ctor_get(x_150, 5);
lean_inc(x_184);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 lean_ctor_release(x_150, 2);
 lean_ctor_release(x_150, 3);
 lean_ctor_release(x_150, 4);
 lean_ctor_release(x_150, 5);
 x_185 = x_150;
} else {
 lean_dec_ref(x_150);
 x_185 = lean_box(0);
}
x_186 = lean_ctor_get(x_151, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_151, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_151, 2);
lean_inc(x_188);
x_189 = lean_ctor_get(x_151, 3);
lean_inc(x_189);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 lean_ctor_release(x_151, 2);
 lean_ctor_release(x_151, 3);
 x_190 = x_151;
} else {
 lean_dec_ref(x_151);
 x_190 = lean_box(0);
}
lean_inc(x_179);
x_191 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__4(x_186, x_1, x_179);
if (lean_is_scalar(x_190)) {
 x_192 = lean_alloc_ctor(0, 4, 0);
} else {
 x_192 = x_190;
}
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_187);
lean_ctor_set(x_192, 2, x_188);
lean_ctor_set(x_192, 3, x_189);
if (lean_is_scalar(x_185)) {
 x_193 = lean_alloc_ctor(0, 6, 0);
} else {
 x_193 = x_185;
}
lean_ctor_set(x_193, 0, x_180);
lean_ctor_set(x_193, 1, x_181);
lean_ctor_set(x_193, 2, x_192);
lean_ctor_set(x_193, 3, x_182);
lean_ctor_set(x_193, 4, x_183);
lean_ctor_set(x_193, 5, x_184);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_179);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
else
{
uint8_t x_195; 
lean_dec(x_1);
x_195 = !lean_is_exclusive(x_149);
if (x_195 == 0)
{
return x_149;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_149, 0);
x_197 = lean_ctor_get(x_149, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_149);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
else
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_2);
lean_dec(x_1);
x_199 = lean_ctor_get(x_148, 0);
lean_inc(x_199);
lean_dec(x_148);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_3);
return x_200;
}
}
case 12:
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_1);
x_201 = l_Lean_Meta_isClassQuick___main___closed__1;
x_202 = l_unreachable_x21___rarg(x_201);
x_203 = lean_apply_2(x_202, x_2, x_3);
return x_203;
}
default: 
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_3, 2);
lean_inc(x_204);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
lean_dec(x_204);
x_206 = l_PersistentHashMap_find_x3f___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__1(x_205, x_1);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; 
x_207 = l___private_Init_Lean_Meta_InferType_5__inferLambdaType___closed__1;
lean_inc(x_1);
x_208 = l_Lean_Meta_lambdaTelescope___rarg(x_1, x_207, x_2, x_3);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
x_210 = lean_ctor_get(x_209, 2);
lean_inc(x_210);
x_211 = !lean_is_exclusive(x_208);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_212 = lean_ctor_get(x_208, 0);
x_213 = lean_ctor_get(x_208, 1);
lean_dec(x_213);
x_214 = !lean_is_exclusive(x_209);
if (x_214 == 0)
{
lean_object* x_215; uint8_t x_216; 
x_215 = lean_ctor_get(x_209, 2);
lean_dec(x_215);
x_216 = !lean_is_exclusive(x_210);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_210, 0);
lean_inc(x_212);
x_218 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__4(x_217, x_1, x_212);
lean_ctor_set(x_210, 0, x_218);
return x_208;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_219 = lean_ctor_get(x_210, 0);
x_220 = lean_ctor_get(x_210, 1);
x_221 = lean_ctor_get(x_210, 2);
x_222 = lean_ctor_get(x_210, 3);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_210);
lean_inc(x_212);
x_223 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__4(x_219, x_1, x_212);
x_224 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_220);
lean_ctor_set(x_224, 2, x_221);
lean_ctor_set(x_224, 3, x_222);
lean_ctor_set(x_209, 2, x_224);
return x_208;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_225 = lean_ctor_get(x_209, 0);
x_226 = lean_ctor_get(x_209, 1);
x_227 = lean_ctor_get(x_209, 3);
x_228 = lean_ctor_get(x_209, 4);
x_229 = lean_ctor_get(x_209, 5);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_209);
x_230 = lean_ctor_get(x_210, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_210, 1);
lean_inc(x_231);
x_232 = lean_ctor_get(x_210, 2);
lean_inc(x_232);
x_233 = lean_ctor_get(x_210, 3);
lean_inc(x_233);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 lean_ctor_release(x_210, 2);
 lean_ctor_release(x_210, 3);
 x_234 = x_210;
} else {
 lean_dec_ref(x_210);
 x_234 = lean_box(0);
}
lean_inc(x_212);
x_235 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__4(x_230, x_1, x_212);
if (lean_is_scalar(x_234)) {
 x_236 = lean_alloc_ctor(0, 4, 0);
} else {
 x_236 = x_234;
}
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_231);
lean_ctor_set(x_236, 2, x_232);
lean_ctor_set(x_236, 3, x_233);
x_237 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_237, 0, x_225);
lean_ctor_set(x_237, 1, x_226);
lean_ctor_set(x_237, 2, x_236);
lean_ctor_set(x_237, 3, x_227);
lean_ctor_set(x_237, 4, x_228);
lean_ctor_set(x_237, 5, x_229);
lean_ctor_set(x_208, 1, x_237);
return x_208;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_238 = lean_ctor_get(x_208, 0);
lean_inc(x_238);
lean_dec(x_208);
x_239 = lean_ctor_get(x_209, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_209, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_209, 3);
lean_inc(x_241);
x_242 = lean_ctor_get(x_209, 4);
lean_inc(x_242);
x_243 = lean_ctor_get(x_209, 5);
lean_inc(x_243);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 lean_ctor_release(x_209, 2);
 lean_ctor_release(x_209, 3);
 lean_ctor_release(x_209, 4);
 lean_ctor_release(x_209, 5);
 x_244 = x_209;
} else {
 lean_dec_ref(x_209);
 x_244 = lean_box(0);
}
x_245 = lean_ctor_get(x_210, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_210, 1);
lean_inc(x_246);
x_247 = lean_ctor_get(x_210, 2);
lean_inc(x_247);
x_248 = lean_ctor_get(x_210, 3);
lean_inc(x_248);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 lean_ctor_release(x_210, 2);
 lean_ctor_release(x_210, 3);
 x_249 = x_210;
} else {
 lean_dec_ref(x_210);
 x_249 = lean_box(0);
}
lean_inc(x_238);
x_250 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_InferType_9__checkInferTypeCache___spec__4(x_245, x_1, x_238);
if (lean_is_scalar(x_249)) {
 x_251 = lean_alloc_ctor(0, 4, 0);
} else {
 x_251 = x_249;
}
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_246);
lean_ctor_set(x_251, 2, x_247);
lean_ctor_set(x_251, 3, x_248);
if (lean_is_scalar(x_244)) {
 x_252 = lean_alloc_ctor(0, 6, 0);
} else {
 x_252 = x_244;
}
lean_ctor_set(x_252, 0, x_239);
lean_ctor_set(x_252, 1, x_240);
lean_ctor_set(x_252, 2, x_251);
lean_ctor_set(x_252, 3, x_241);
lean_ctor_set(x_252, 4, x_242);
lean_ctor_set(x_252, 5, x_243);
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_238);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
else
{
uint8_t x_254; 
lean_dec(x_1);
x_254 = !lean_is_exclusive(x_208);
if (x_254 == 0)
{
return x_208;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_208, 0);
x_256 = lean_ctor_get(x_208, 1);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_208);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
return x_257;
}
}
}
else
{
lean_object* x_258; lean_object* x_259; 
lean_dec(x_2);
lean_dec(x_1);
x_258 = lean_ctor_get(x_206, 0);
lean_inc(x_258);
lean_dec(x_206);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_3);
return x_259;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_InferType_10__inferTypeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_InferType_10__inferTypeAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_inferTypeImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
lean_ctor_set_uint8(x_5, sizeof(void*)*1 + 6, x_7);
x_8 = l___private_Init_Lean_Meta_InferType_10__inferTypeAux___main(x_1, x_2, x_3);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_11 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_12 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 2);
x_13 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 3);
x_14 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 4);
x_15 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 5);
lean_inc(x_9);
lean_dec(x_5);
x_16 = 1;
x_17 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_10);
lean_ctor_set_uint8(x_17, sizeof(void*)*1 + 1, x_11);
lean_ctor_set_uint8(x_17, sizeof(void*)*1 + 2, x_12);
lean_ctor_set_uint8(x_17, sizeof(void*)*1 + 3, x_13);
lean_ctor_set_uint8(x_17, sizeof(void*)*1 + 4, x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*1 + 5, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*1 + 6, x_16);
lean_ctor_set(x_2, 0, x_17);
x_18 = l___private_Init_Lean_Meta_InferType_10__inferTypeAux___main(x_1, x_2, x_3);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_2, 2);
x_22 = lean_ctor_get(x_2, 3);
x_23 = lean_ctor_get(x_2, 4);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_2);
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
x_26 = lean_ctor_get_uint8(x_19, sizeof(void*)*1 + 1);
x_27 = lean_ctor_get_uint8(x_19, sizeof(void*)*1 + 2);
x_28 = lean_ctor_get_uint8(x_19, sizeof(void*)*1 + 3);
x_29 = lean_ctor_get_uint8(x_19, sizeof(void*)*1 + 4);
x_30 = lean_ctor_get_uint8(x_19, sizeof(void*)*1 + 5);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_31 = x_19;
} else {
 lean_dec_ref(x_19);
 x_31 = lean_box(0);
}
x_32 = 1;
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 1, 7);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_25);
lean_ctor_set_uint8(x_33, sizeof(void*)*1 + 1, x_26);
lean_ctor_set_uint8(x_33, sizeof(void*)*1 + 2, x_27);
lean_ctor_set_uint8(x_33, sizeof(void*)*1 + 3, x_28);
lean_ctor_set_uint8(x_33, sizeof(void*)*1 + 4, x_29);
lean_ctor_set_uint8(x_33, sizeof(void*)*1 + 5, x_30);
lean_ctor_set_uint8(x_33, sizeof(void*)*1 + 6, x_32);
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_20);
lean_ctor_set(x_34, 2, x_21);
lean_ctor_set(x_34, 3, x_22);
lean_ctor_set(x_34, 4, x_23);
x_35 = l___private_Init_Lean_Meta_InferType_10__inferTypeAux___main(x_1, x_34, x_3);
return x_35;
}
}
}
lean_object* _init_l_Lean_Meta_setInferTypeRef___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_inferTypeImpl), 3, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_setInferTypeRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_inferTypeRef;
x_3 = l_Lean_Meta_setInferTypeRef___closed__1;
x_4 = lean_io_ref_set(x_2, x_3, x_1);
return x_4;
}
}
uint8_t l___private_Init_Lean_Meta_InferType_11__isAlwaysZero___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
case 2:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l___private_Init_Lean_Meta_InferType_11__isAlwaysZero___main(x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
x_1 = x_4;
goto _start;
}
}
case 3:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 1);
x_1 = x_8;
goto _start;
}
default: 
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_InferType_11__isAlwaysZero___main___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Meta_InferType_11__isAlwaysZero___main(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l___private_Init_Lean_Meta_InferType_11__isAlwaysZero(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l___private_Init_Lean_Meta_InferType_11__isAlwaysZero___main(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_InferType_11__isAlwaysZero___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Meta_InferType_11__isAlwaysZero(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_InferType_12__isArrowProp___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_2, x_6);
lean_dec(x_2);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_8 = 2;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Meta_instantiateLevelMVars(x_5, x_3, x_4);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l___private_Init_Lean_Meta_InferType_11__isAlwaysZero___main(x_13);
lean_dec(x_13);
x_15 = l_Bool_toLBool(x_14);
x_16 = lean_box(x_15);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = l___private_Init_Lean_Meta_InferType_11__isAlwaysZero___main(x_17);
lean_dec(x_17);
x_20 = l_Bool_toLBool(x_19);
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
}
case 7:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_1, 2);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_eq(x_2, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_2, x_26);
lean_dec(x_2);
x_1 = x_23;
x_2 = x_27;
goto _start;
}
else
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_23);
lean_dec(x_2);
x_29 = 0;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_4);
return x_31;
}
}
case 8:
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_1, 3);
lean_inc(x_32);
lean_dec(x_1);
x_1 = x_32;
goto _start;
}
case 10:
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
lean_dec(x_1);
x_1 = x_34;
goto _start;
}
default: 
{
uint8_t x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_2);
lean_dec(x_1);
x_36 = 2;
x_37 = lean_box(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_4);
return x_38;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_InferType_12__isArrowProp___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_InferType_12__isArrowProp___main(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_InferType_12__isArrowProp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_InferType_12__isArrowProp___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_InferType_12__isArrowProp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_InferType_12__isArrowProp(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_InferType_13__isPropQuickApp___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_3);
x_6 = l___private_Init_Lean_Meta_InferType_8__inferFVarType(x_5, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l___private_Init_Lean_Meta_InferType_12__isArrowProp___main(x_7, x_2, x_3, x_8);
lean_dec(x_3);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
case 2:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l___private_Init_Lean_Meta_InferType_7__inferMVarType(x_14, x_3, x_4);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l___private_Init_Lean_Meta_InferType_12__isArrowProp___main(x_16, x_2, x_3, x_17);
lean_dec(x_3);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
case 4:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_dec(x_1);
x_25 = l___private_Init_Lean_Meta_InferType_2__inferConstType(x_23, x_24, x_3, x_4);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l___private_Init_Lean_Meta_InferType_12__isArrowProp___main(x_26, x_2, x_3, x_27);
lean_dec(x_3);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
case 5:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_2, x_34);
lean_dec(x_2);
x_1 = x_33;
x_2 = x_35;
goto _start;
}
case 6:
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_1, 2);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_eq(x_2, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_sub(x_2, x_40);
lean_dec(x_2);
x_1 = x_37;
x_2 = x_41;
goto _start;
}
else
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_37);
lean_dec(x_3);
lean_dec(x_2);
x_43 = 0;
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_4);
return x_45;
}
}
case 8:
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_1, 3);
lean_inc(x_46);
lean_dec(x_1);
x_1 = x_46;
goto _start;
}
case 10:
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_1, 1);
lean_inc(x_48);
lean_dec(x_1);
x_1 = x_48;
goto _start;
}
default: 
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = 2;
x_51 = lean_box(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_4);
return x_52;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_InferType_13__isPropQuickApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_InferType_13__isPropQuickApp___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_isPropQuick___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = 2;
x_5 = lean_box(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_2);
x_8 = l___private_Init_Lean_Meta_InferType_8__inferFVarType(x_7, x_2, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Init_Lean_Meta_InferType_12__isArrowProp___main(x_9, x_11, x_2, x_10);
lean_dec(x_2);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
case 2:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l___private_Init_Lean_Meta_InferType_7__inferMVarType(x_17, x_2, x_3);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l___private_Init_Lean_Meta_InferType_12__isArrowProp___main(x_19, x_21, x_2, x_20);
lean_dec(x_2);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
case 4:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_dec(x_1);
x_29 = l___private_Init_Lean_Meta_InferType_2__inferConstType(x_27, x_28, x_2, x_3);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l___private_Init_Lean_Meta_InferType_12__isArrowProp___main(x_30, x_32, x_2, x_31);
lean_dec(x_2);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
case 5:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_unsigned_to_nat(1u);
x_40 = l___private_Init_Lean_Meta_InferType_13__isPropQuickApp___main(x_38, x_39, x_2, x_3);
return x_40;
}
case 7:
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_1, 2);
lean_inc(x_41);
lean_dec(x_1);
x_1 = x_41;
goto _start;
}
case 8:
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_1, 3);
lean_inc(x_43);
lean_dec(x_1);
x_1 = x_43;
goto _start;
}
case 10:
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
lean_dec(x_1);
x_1 = x_45;
goto _start;
}
case 11:
{
uint8_t x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_2);
lean_dec(x_1);
x_47 = 2;
x_48 = lean_box(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_3);
return x_49;
}
case 12:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_1);
x_50 = l_Lean_Meta_isClassQuick___main___closed__1;
x_51 = l_unreachable_x21___rarg(x_50);
x_52 = lean_apply_2(x_51, x_2, x_3);
return x_52;
}
default: 
{
uint8_t x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_2);
lean_dec(x_1);
x_53 = 0;
x_54 = lean_box(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_3);
return x_55;
}
}
}
}
lean_object* l_Lean_Meta_isPropQuick(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isPropQuick___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_isProp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = l_Lean_Meta_isPropQuick___main(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
switch (x_6) {
case 0:
{
uint8_t x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = 0;
x_10 = lean_box(x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
case 1:
{
uint8_t x_15; 
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_4, 0);
lean_dec(x_16);
x_17 = 1;
x_18 = lean_box(x_17);
lean_ctor_set(x_4, 0, x_18);
return x_4;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_dec(x_4);
x_20 = 1;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
default: 
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_dec(x_4);
lean_inc(x_2);
x_24 = l_Lean_Meta_inferType(x_1, x_2, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_2);
x_27 = l_Lean_Meta_whnfD(x_25, x_2, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 3)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Meta_instantiateLevelMVars(x_30, x_2, x_29);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = l___private_Init_Lean_Meta_InferType_11__isAlwaysZero___main(x_33);
lean_dec(x_33);
x_35 = lean_box(x_34);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_31, 0);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_31);
x_38 = l___private_Init_Lean_Meta_InferType_11__isAlwaysZero___main(x_36);
lean_dec(x_36);
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_28);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_27);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_27, 0);
lean_dec(x_42);
x_43 = 0;
x_44 = lean_box(x_43);
lean_ctor_set(x_27, 0, x_44);
return x_27;
}
else
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_27, 1);
lean_inc(x_45);
lean_dec(x_27);
x_46 = 0;
x_47 = lean_box(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_27);
if (x_49 == 0)
{
return x_27;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_27, 0);
x_51 = lean_ctor_get(x_27, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_27);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_24);
if (x_53 == 0)
{
return x_24;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_24, 0);
x_55 = lean_ctor_get(x_24, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_24);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_4);
if (x_57 == 0)
{
return x_4;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_4, 0);
x_59 = lean_ctor_get(x_4, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_4);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_InferType_14__isArrowProposition___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
switch (lean_obj_tag(x_1)) {
case 7:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_2, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_2, x_16);
lean_dec(x_2);
x_1 = x_13;
x_2 = x_17;
goto _start;
}
else
{
lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_2);
x_19 = l_Lean_Meta_isPropQuick___main(x_1, x_3, x_4);
return x_19;
}
}
case 8:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_1, 3);
lean_inc(x_20);
lean_dec(x_1);
x_1 = x_20;
goto _start;
}
case 10:
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec(x_1);
x_1 = x_22;
goto _start;
}
default: 
{
lean_object* x_24; 
x_24 = lean_box(0);
x_5 = x_24;
goto block_12;
}
}
block_12:
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_5);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_2, x_6);
lean_dec(x_2);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = 2;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l_Lean_Meta_isPropQuick___main(x_1, x_3, x_4);
return x_11;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_InferType_14__isArrowProposition(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_InferType_14__isArrowProposition___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_InferType_15__isProofQuickApp___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
lean_inc(x_4);
x_7 = l___private_Init_Lean_Meta_InferType_8__inferFVarType(x_6, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l___private_Init_Lean_Meta_InferType_14__isArrowProposition___main(x_8, x_3, x_4, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_4);
lean_dec(x_3);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
case 2:
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l___private_Init_Lean_Meta_InferType_7__inferMVarType(x_15, x_4, x_5);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l___private_Init_Lean_Meta_InferType_14__isArrowProposition___main(x_17, x_3, x_4, x_18);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_4);
lean_dec(x_3);
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
case 4:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_dec(x_2);
x_26 = l___private_Init_Lean_Meta_InferType_2__inferConstType(x_24, x_25, x_4, x_5);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l___private_Init_Lean_Meta_InferType_14__isArrowProposition___main(x_27, x_3, x_4, x_28);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_4);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
case 5:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
lean_dec(x_2);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_3, x_35);
lean_dec(x_3);
x_2 = x_34;
x_3 = x_36;
goto _start;
}
case 6:
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_2, 2);
lean_inc(x_38);
lean_dec(x_2);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_nat_dec_eq(x_3, x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_sub(x_3, x_41);
lean_dec(x_3);
x_2 = x_38;
x_3 = x_42;
goto _start;
}
else
{
lean_object* x_44; 
lean_dec(x_3);
x_44 = lean_apply_3(x_1, x_38, x_4, x_5);
return x_44;
}
}
case 8:
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_2, 3);
lean_inc(x_45);
lean_dec(x_2);
x_2 = x_45;
goto _start;
}
case 10:
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_2, 1);
lean_inc(x_47);
lean_dec(x_2);
x_2 = x_47;
goto _start;
}
default: 
{
uint8_t x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = 2;
x_50 = lean_box(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_5);
return x_51;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_InferType_15__isProofQuickApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Meta_InferType_15__isProofQuickApp___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Meta_InferType_15__isProofQuickApp___main___at_Lean_Meta_isProofQuick___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_3);
x_6 = l___private_Init_Lean_Meta_InferType_8__inferFVarType(x_5, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l___private_Init_Lean_Meta_InferType_14__isArrowProposition___main(x_7, x_2, x_3, x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
case 2:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l___private_Init_Lean_Meta_InferType_7__inferMVarType(x_14, x_3, x_4);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l___private_Init_Lean_Meta_InferType_14__isArrowProposition___main(x_16, x_2, x_3, x_17);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
case 4:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_dec(x_1);
x_25 = l___private_Init_Lean_Meta_InferType_2__inferConstType(x_23, x_24, x_3, x_4);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l___private_Init_Lean_Meta_InferType_14__isArrowProposition___main(x_26, x_2, x_3, x_27);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
case 5:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_2, x_34);
lean_dec(x_2);
x_1 = x_33;
x_2 = x_35;
goto _start;
}
case 6:
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_1, 2);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_eq(x_2, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_sub(x_2, x_40);
lean_dec(x_2);
x_1 = x_37;
x_2 = x_41;
goto _start;
}
else
{
lean_object* x_43; 
lean_dec(x_2);
x_43 = l_Lean_Meta_isProofQuick___main(x_37, x_3, x_4);
return x_43;
}
}
case 8:
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_1, 3);
lean_inc(x_44);
lean_dec(x_1);
x_1 = x_44;
goto _start;
}
case 10:
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_1, 1);
lean_inc(x_46);
lean_dec(x_1);
x_1 = x_46;
goto _start;
}
default: 
{
uint8_t x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = 2;
x_49 = lean_box(x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_4);
return x_50;
}
}
}
}
lean_object* l_Lean_Meta_isProofQuick___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = 2;
x_5 = lean_box(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_2);
x_8 = l___private_Init_Lean_Meta_InferType_8__inferFVarType(x_7, x_2, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Init_Lean_Meta_InferType_14__isArrowProposition___main(x_9, x_11, x_2, x_10);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
case 2:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l___private_Init_Lean_Meta_InferType_7__inferMVarType(x_17, x_2, x_3);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l___private_Init_Lean_Meta_InferType_14__isArrowProposition___main(x_19, x_21, x_2, x_20);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
case 4:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_dec(x_1);
x_29 = l___private_Init_Lean_Meta_InferType_2__inferConstType(x_27, x_28, x_2, x_3);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l___private_Init_Lean_Meta_InferType_14__isArrowProposition___main(x_30, x_32, x_2, x_31);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
case 5:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_unsigned_to_nat(1u);
x_40 = l___private_Init_Lean_Meta_InferType_15__isProofQuickApp___main___at_Lean_Meta_isProofQuick___main___spec__1(x_38, x_39, x_2, x_3);
return x_40;
}
case 6:
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_1, 2);
lean_inc(x_41);
lean_dec(x_1);
x_1 = x_41;
goto _start;
}
case 8:
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_1, 3);
lean_inc(x_43);
lean_dec(x_1);
x_1 = x_43;
goto _start;
}
case 10:
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
lean_dec(x_1);
x_1 = x_45;
goto _start;
}
case 11:
{
uint8_t x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_2);
lean_dec(x_1);
x_47 = 2;
x_48 = lean_box(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_3);
return x_49;
}
case 12:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_1);
x_50 = l_Lean_Meta_isClassQuick___main___closed__1;
x_51 = l_unreachable_x21___rarg(x_50);
x_52 = lean_apply_2(x_51, x_2, x_3);
return x_52;
}
default: 
{
uint8_t x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_2);
lean_dec(x_1);
x_53 = 0;
x_54 = lean_box(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_3);
return x_55;
}
}
}
}
lean_object* l_Lean_Meta_isProofQuick(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isProofQuick___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_isProof(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = l_Lean_Meta_isProofQuick___main(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
switch (x_6) {
case 0:
{
uint8_t x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = 0;
x_10 = lean_box(x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
case 1:
{
uint8_t x_15; 
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_4, 0);
lean_dec(x_16);
x_17 = 1;
x_18 = lean_box(x_17);
lean_ctor_set(x_4, 0, x_18);
return x_4;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_dec(x_4);
x_20 = 1;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
default: 
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_dec(x_4);
lean_inc(x_2);
x_24 = l_Lean_Meta_inferType(x_1, x_2, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Meta_isProp(x_25, x_2, x_26);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
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
uint8_t x_32; 
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_4);
if (x_32 == 0)
{
return x_4;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_4, 0);
x_34 = lean_ctor_get(x_4, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_4);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_InferType_16__isArrowType___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
lean_dec(x_2);
if (x_6 == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 2;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
}
case 7:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_2, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_2, x_16);
lean_dec(x_2);
x_1 = x_13;
x_2 = x_17;
goto _start;
}
else
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
}
case 8:
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_1, 3);
x_1 = x_22;
goto _start;
}
case 10:
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_1, 1);
x_1 = x_24;
goto _start;
}
default: 
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_2);
x_26 = 2;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
return x_28;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_InferType_16__isArrowType___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_InferType_16__isArrowType___main(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_InferType_16__isArrowType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_InferType_16__isArrowType___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_InferType_16__isArrowType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_InferType_16__isArrowType(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_InferType_17__isTypeQuickApp___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_3);
x_6 = l___private_Init_Lean_Meta_InferType_8__inferFVarType(x_5, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l___private_Init_Lean_Meta_InferType_16__isArrowType___main(x_7, x_2, x_3, x_8);
lean_dec(x_3);
lean_dec(x_7);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
case 2:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l___private_Init_Lean_Meta_InferType_7__inferMVarType(x_14, x_3, x_4);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l___private_Init_Lean_Meta_InferType_16__isArrowType___main(x_16, x_2, x_3, x_17);
lean_dec(x_3);
lean_dec(x_16);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
case 4:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_dec(x_1);
x_25 = l___private_Init_Lean_Meta_InferType_2__inferConstType(x_23, x_24, x_3, x_4);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l___private_Init_Lean_Meta_InferType_16__isArrowType___main(x_26, x_2, x_3, x_27);
lean_dec(x_3);
lean_dec(x_26);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
case 5:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_2, x_34);
lean_dec(x_2);
x_1 = x_33;
x_2 = x_35;
goto _start;
}
case 6:
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_1, 2);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_eq(x_2, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_sub(x_2, x_40);
lean_dec(x_2);
x_1 = x_37;
x_2 = x_41;
goto _start;
}
else
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_37);
lean_dec(x_3);
lean_dec(x_2);
x_43 = 0;
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_4);
return x_45;
}
}
case 8:
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_1, 3);
lean_inc(x_46);
lean_dec(x_1);
x_1 = x_46;
goto _start;
}
case 10:
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_1, 1);
lean_inc(x_48);
lean_dec(x_1);
x_1 = x_48;
goto _start;
}
default: 
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = 2;
x_51 = lean_box(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_4);
return x_52;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_InferType_17__isTypeQuickApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_InferType_17__isTypeQuickApp___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_isTypeQuick___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
lean_inc(x_2);
x_5 = l___private_Init_Lean_Meta_InferType_8__inferFVarType(x_4, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Init_Lean_Meta_InferType_16__isArrowType___main(x_6, x_8, x_2, x_7);
lean_dec(x_2);
lean_dec(x_6);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
case 2:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l___private_Init_Lean_Meta_InferType_7__inferMVarType(x_14, x_2, x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l___private_Init_Lean_Meta_InferType_16__isArrowType___main(x_16, x_18, x_2, x_17);
lean_dec(x_2);
lean_dec(x_16);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
case 3:
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_24 = 1;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
return x_26;
}
case 4:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_dec(x_1);
x_29 = l___private_Init_Lean_Meta_InferType_2__inferConstType(x_27, x_28, x_2, x_3);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l___private_Init_Lean_Meta_InferType_16__isArrowType___main(x_30, x_32, x_2, x_31);
lean_dec(x_2);
lean_dec(x_30);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
case 5:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_unsigned_to_nat(1u);
x_40 = l___private_Init_Lean_Meta_InferType_17__isTypeQuickApp___main(x_38, x_39, x_2, x_3);
return x_40;
}
case 6:
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_2);
lean_dec(x_1);
x_41 = 0;
x_42 = lean_box(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_3);
return x_43;
}
case 7:
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_2);
lean_dec(x_1);
x_44 = 1;
x_45 = lean_box(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_3);
return x_46;
}
case 8:
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_1, 3);
lean_inc(x_47);
lean_dec(x_1);
x_1 = x_47;
goto _start;
}
case 9:
{
uint8_t x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_2);
lean_dec(x_1);
x_49 = 0;
x_50 = lean_box(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_3);
return x_51;
}
case 10:
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_1, 1);
lean_inc(x_52);
lean_dec(x_1);
x_1 = x_52;
goto _start;
}
case 12:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_1);
x_54 = l_Lean_Meta_isClassQuick___main___closed__1;
x_55 = l_unreachable_x21___rarg(x_54);
x_56 = lean_apply_2(x_55, x_2, x_3);
return x_56;
}
default: 
{
uint8_t x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_2);
lean_dec(x_1);
x_57 = 2;
x_58 = lean_box(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_3);
return x_59;
}
}
}
}
lean_object* l_Lean_Meta_isTypeQuick(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isTypeQuick___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_isType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = l_Lean_Meta_isTypeQuick___main(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
switch (x_6) {
case 0:
{
uint8_t x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = 0;
x_10 = lean_box(x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
case 1:
{
uint8_t x_15; 
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_4, 0);
lean_dec(x_16);
x_17 = 1;
x_18 = lean_box(x_17);
lean_ctor_set(x_4, 0, x_18);
return x_4;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_dec(x_4);
x_20 = 1;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
default: 
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_dec(x_4);
lean_inc(x_2);
x_24 = l_Lean_Meta_inferType(x_1, x_2, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Meta_whnfD(x_25, x_2, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 3)
{
uint8_t x_29; 
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = 1;
x_32 = lean_box(x_31);
lean_ctor_set(x_27, 0, x_32);
return x_27;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = 1;
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_28);
x_37 = !lean_is_exclusive(x_27);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_27, 0);
lean_dec(x_38);
x_39 = 0;
x_40 = lean_box(x_39);
lean_ctor_set(x_27, 0, x_40);
return x_27;
}
else
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_27, 1);
lean_inc(x_41);
lean_dec(x_27);
x_42 = 0;
x_43 = lean_box(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_27);
if (x_45 == 0)
{
return x_27;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_27, 0);
x_47 = lean_ctor_get(x_27, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_27);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_24);
if (x_49 == 0)
{
return x_24;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_24, 0);
x_51 = lean_ctor_get(x_24, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_24);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_4);
if (x_53 == 0)
{
return x_4;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_4, 0);
x_55 = lean_ctor_get(x_4, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_4);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
lean_object* l_Lean_Meta_isTypeFormerAux___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_expr_instantiate1(x_1, x_2);
x_6 = l_Lean_Meta_isTypeFormerAux___main(x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Meta_isTypeFormerAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Meta_whnfD(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
switch (lean_obj_tag(x_5)) {
case 3:
{
uint8_t x_6; 
lean_dec(x_5);
lean_dec(x_2);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = 1;
x_9 = lean_box(x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
case 7:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec(x_4);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 2);
lean_inc(x_17);
x_18 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_dec(x_5);
x_19 = (uint8_t)((x_18 << 24) >> 61);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_isTypeFormerAux___main___lambda__1___boxed), 4, 1);
lean_closure_set(x_20, 0, x_17);
x_21 = l_Lean_Meta_withLocalDecl___rarg(x_15, x_16, x_19, x_20, x_2, x_14);
return x_21;
}
default: 
{
uint8_t x_22; 
lean_dec(x_5);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_4, 0);
lean_dec(x_23);
x_24 = 0;
x_25 = lean_box(x_24);
lean_ctor_set(x_4, 0, x_25);
return x_4;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_4, 1);
lean_inc(x_26);
lean_dec(x_4);
x_27 = 0;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_4);
if (x_30 == 0)
{
return x_4;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_4, 0);
x_32 = lean_ctor_get(x_4, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_4);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_Lean_Meta_isTypeFormerAux___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_isTypeFormerAux___main___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_isTypeFormerAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isTypeFormerAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_isTypeFormer(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Meta_inferType(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Meta_isTypeFormerAux___main(x_5, x_2, x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
lean_object* initialize_Init_Lean_Data_LBool(lean_object*);
lean_object* initialize_Init_Lean_Meta_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_InferType(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Data_LBool(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Lean_Meta_InferType_4__inferForallType___closed__1 = _init_l___private_Init_Lean_Meta_InferType_4__inferForallType___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_InferType_4__inferForallType___closed__1);
l___private_Init_Lean_Meta_InferType_5__inferLambdaType___closed__1 = _init_l___private_Init_Lean_Meta_InferType_5__inferLambdaType___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_InferType_5__inferLambdaType___closed__1);
l_Lean_Meta_setInferTypeRef___closed__1 = _init_l_Lean_Meta_setInferTypeRef___closed__1();
lean_mark_persistent(l_Lean_Meta_setInferTypeRef___closed__1);
res = l_Lean_Meta_setInferTypeRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
