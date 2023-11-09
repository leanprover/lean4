// Lean compiler output
// Module: Lean.Widget.Diff
// Imports: Init Lean.Meta.PPGoal Lean.Widget.InteractiveCode Lean.Widget.InteractiveGoal Lean.Data.Lsp.Extra Lean.Elab.InfoTree
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
static lean_object* l_Lean_Widget_ExprDiffTag_toString___closed__3;
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_ExprDiff_withChange(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__2;
lean_object* l_Lean_MetavarContext_findDecl_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_Widget_exprDiffCore___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lean_Widget_ExprDiff_insertBeforeChange___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Widget_diffHypotheses___spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_ExprDiffTag_toString(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Widget_diffInteractiveGoals(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4___lambda__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Widget_diffInteractiveGoal___closed__1;
lean_object* l_Lean_Expr_getForallBodyMaxDepth(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Widget_instAppendExprDiff___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_findCore___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp___spec__4(lean_object*, lean_object*);
static lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_noConfusion___rarg___closed__1;
lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at_Lean_Widget_instToStringExprDiff___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toCtorIdx___boxed(lean_object*);
static lean_object* l_Lean_Widget_diffInteractiveGoal___closed__2;
uint8_t l_Lean_RBNode_isRed___rarg(lean_object*);
static lean_object* l_Lean_Widget_instEmptyCollectionExprDiff___closed__1;
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___at_Lean_Widget_exprDiffCore_piDiff___spec__2(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Widget_instToStringExprDiff___closed__2;
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Widget_diffInteractiveGoals___spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_diffHypothesesBundle_withTypeDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Widget_diffHypothesesBundle___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Widget_exprDiffCore___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_List_foldlM___at_Lean_Widget_diffInteractiveGoals___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Widget_diffHypothesesBundle___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiffCore_piDiff___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Widget_addDiffTags___spec__2(lean_object*, lean_object*);
lean_object* l_List_find_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiffCore_piDiff___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_ExprDiffTag_toDiffTag___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addDiffTags___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_Lean_Meta_getFVarFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Widget_diffHypothesesBundle___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instEmptyCollectionExprDiff;
lean_object* l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lean_Widget_ExprDiff_insertBeforeChange___spec__1(lean_object*, lean_object*, uint8_t);
static lean_object* l_List_mapTR_loop___at_Lean_Widget_instToStringExprDiff___spec__3___closed__3;
static lean_object* l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__5;
LEAN_EXPORT lean_object* l_Lean_Widget_diffHypotheses(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6_(lean_object*);
static lean_object* l_Lean_Widget_diffInteractiveGoal___closed__7;
LEAN_EXPORT lean_object* l_Lean_Widget_diffHypothesesBundle___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__7;
LEAN_EXPORT lean_object* l_Lean_Widget_showTacticDiff;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at_Lean_Widget_addDiffTags___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__8;
LEAN_EXPORT lean_object* l_Lean_Widget_instAppendExprDiff___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_diffInteractiveGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Widget_diffInteractiveGoals___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Widget_diffInteractiveGoals___closed__1;
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiffCore_piDiff___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Widget_diffInteractiveGoal___closed__8;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_toString(lean_object*);
lean_object* l_Array_zip___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiff(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBTree_fromArray___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4___at_Lean_Widget_diffInteractiveGoals___spec__5(uint8_t, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instAppendExprDiff___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_setBlack___rarg(lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiffCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_diffHypothesesBundle___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Widget_diffInteractiveGoal___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_noConfusion(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_ExprDiff_insertBeforeChange___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_ExprDiff_changesBefore___default;
lean_object* l_Lean_Widget_withGoalCtx___at_Lean_Widget_goalToInteractive___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_pushNthBindingDomain(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Widget_exprDiffCore_piDiff___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f___at_Lean_Widget_exprDiffCore_piDiff___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_diffHypotheses___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Widget_diffInteractiveGoal___closed__6;
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiffCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_diffInteractiveGoal(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_SubExpr_Pos_root;
static lean_object* l_List_mapTR_loop___at_Lean_Widget_instToStringExprDiff___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Widget_diffHypotheses___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_MVarIdMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Widget_exprDiffCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Widget_diffHypothesesBundle_withTypeDiff___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Widget_diffInteractiveGoal___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Widget_diffInteractiveGoal___closed__5;
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiffCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_diffHypothesesBundle___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiffCore_piDiff___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Widget_diffHypothesesBundle___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiffCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Widget_ExprDiffTag_toDiffTag(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at_Lean_Widget_addDiffTags___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_ExprDiff_withChangePos___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_pushNaryArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_pushNthBindingBody(lean_object*, lean_object*);
static lean_object* l_Lean_Widget_instToStringExprDiff___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Widget_addDiffTags___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_ExprDiff_insertAfterChange(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___at_Lean_Widget_instToStringExprDiff___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_ExprDiff_insertBeforeChange(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__2;
lean_object* l_Lean_Widget_SubexprInfo_withDiffTag(uint8_t, lean_object*);
lean_object* l_Lean_SubExpr_Pos_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Widget_ExprDiff_insertBeforeChange___spec__2(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Widget_ExprDiffTag_toString___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Widget_diffHypothesesBundle_withTypeDiff___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Widget_diffInteractiveGoals___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_diffHypothesesBundle_withTypeDiff(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instToStringExprDiff(lean_object*);
LEAN_EXPORT uint8_t l_List_foldr___at_Lean_Widget_diffInteractiveGoals___spec__3(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Widget_exprDiffCore_piDiff___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Widget_addDiffTags(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_diffHypothesesBundle(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_noConfusion___rarg___lambda__1(lean_object*);
static lean_object* l_Lean_Widget_instToStringExprDiffTag___closed__1;
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiffCore___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at_Lean_Widget_instToStringExprDiff___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__4;
static lean_object* l_Lean_Widget_exprDiffCore_piDiff___lambda__3___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Widget_diffInteractiveGoals___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Widget_ExprDiff_withChange___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getForallBinderNames(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instAppendExprDiff(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at_Lean_Widget_diffInteractiveGoals___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiffCore_piDiff___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Widget_exprDiffCore_piDiff___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_ExprDiffTag_toString___boxed(lean_object*);
static lean_object* l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__6;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addDiffTags___lambda__1(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Widget_ExprDiff_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at_Lean_Widget_addDiffTags___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiffCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Widget_ExprDiffTag_toString___closed__1;
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addDiffTags___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Widget_instAppendExprDiff___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4___at_Lean_Widget_diffInteractiveGoals___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Widget_instToStringExprDiff___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiffCore_piDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
static lean_object* l_Lean_Widget_instAppendExprDiff___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at_Lean_Widget_addDiffTags___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___at_Lean_Widget_exprDiffCore_piDiff___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_noConfusion___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Widget_exprDiffCore_piDiff___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Widget_exprDiffCore_piDiff___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
static lean_object* l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Widget_addDiffTags___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_ExprDiff_isEmpty___boxed(lean_object*);
static lean_object* l_Lean_Widget_diffInteractiveGoal___closed__3;
LEAN_EXPORT lean_object* l_Lean_Widget_ExprDiff_withChangePos(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Widget_addDiffTags___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_LocalContext_sanitizeNames(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiffCore_piDiff___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Widget_instAppendExprDiff___lambda__2(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Widget_diffInteractiveGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Widget_exprDiffCore___spec__3(lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_ExprDiff_changesAfter___default;
lean_object* l_List_toString___at_Lean_MetavarContext_MkBinding_instToStringException___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Widget_exprDiffCore___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Widget_exprDiffCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Widget_instToStringExprDiff___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instToStringExprDiffTag;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_ExprDiff_insertAfterChange___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Widget_ExprDiff_insertBeforeChange___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Widget_diffInteractiveGoal___closed__4;
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("showTacticDiff", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("When true, interactive goals for tactics will be decorated with diffing information. ", 85);
return x_1;
}
}
static lean_object* _init_l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__3;
x_3 = l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Widget", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__6;
x_2 = l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__7;
x_3 = l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__2;
x_3 = l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__5;
x_4 = l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__8;
x_5 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_ExprDiffTag_toDiffTag(uint8_t x_1, uint8_t x_2) {
_start:
{
if (x_1 == 0)
{
switch (x_2) {
case 0:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
case 1:
{
uint8_t x_4; 
x_4 = 3;
return x_4;
}
default: 
{
uint8_t x_5; 
x_5 = 5;
return x_5;
}
}
}
else
{
switch (x_2) {
case 0:
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
case 1:
{
uint8_t x_7; 
x_7 = 2;
return x_7;
}
default: 
{
uint8_t x_8; 
x_8 = 4;
return x_8;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_ExprDiffTag_toDiffTag___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Widget_ExprDiffTag_toDiffTag(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Widget_ExprDiffTag_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("change", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Widget_ExprDiffTag_toString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("delete", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Widget_ExprDiffTag_toString___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("insert", 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_ExprDiffTag_toString(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_Widget_ExprDiffTag_toString___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_Widget_ExprDiffTag_toString___closed__2;
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = l_Lean_Widget_ExprDiffTag_toString___closed__3;
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_ExprDiffTag_toString___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Widget_ExprDiffTag_toString(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Widget_instToStringExprDiffTag___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Widget_ExprDiffTag_toString___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Widget_instToStringExprDiffTag() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Widget_instToStringExprDiffTag___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Widget_ExprDiff_changesBefore___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Widget_ExprDiff_changesAfter___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Widget_instEmptyCollectionExprDiff___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Widget_instEmptyCollectionExprDiff() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Widget_instEmptyCollectionExprDiff___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_instAppendExprDiff___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_instAppendExprDiff___lambda__2(lean_object* x_1, uint8_t x_2, uint8_t x_3) {
_start:
{
return x_3;
}
}
static lean_object* _init_l_Lean_Widget_instAppendExprDiff___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Widget_instAppendExprDiff___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Widget_instAppendExprDiff___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Widget_instAppendExprDiff___lambda__2___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instAppendExprDiff(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = l_Lean_Widget_instAppendExprDiff___closed__1;
x_6 = l_Lean_Widget_instAppendExprDiff___closed__2;
x_7 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_5, x_6, x_3, x_4);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_5, x_6, x_8, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instAppendExprDiff___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Widget_instAppendExprDiff___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instAppendExprDiff___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_Widget_instAppendExprDiff___lambda__2(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at_Lean_Widget_instToStringExprDiff___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = l_Lean_RBNode_revFold___at_Lean_Widget_instToStringExprDiff___spec__2(x_1, x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_1 = x_9;
x_2 = x_3;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___at_Lean_Widget_instToStringExprDiff___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Lean_RBNode_revFold___at_Lean_Widget_instToStringExprDiff___spec__2(x_2, x_1);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Widget_instToStringExprDiff___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(", 1);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Widget_instToStringExprDiff___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Widget_instToStringExprDiff___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(")", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Widget_instToStringExprDiff___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Lean_SubExpr_Pos_toString(x_7);
x_10 = l_List_mapTR_loop___at_Lean_Widget_instToStringExprDiff___spec__3___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_List_mapTR_loop___at_Lean_Widget_instToStringExprDiff___spec__3___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_unbox(x_8);
lean_dec(x_8);
x_15 = l_Lean_Widget_ExprDiffTag_toString(x_14);
x_16 = lean_string_append(x_13, x_15);
lean_dec(x_15);
x_17 = l_List_mapTR_loop___at_Lean_Widget_instToStringExprDiff___spec__3___closed__3;
x_18 = lean_string_append(x_16, x_17);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_18);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Lean_SubExpr_Pos_toString(x_22);
x_25 = l_List_mapTR_loop___at_Lean_Widget_instToStringExprDiff___spec__3___closed__1;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = l_List_mapTR_loop___at_Lean_Widget_instToStringExprDiff___spec__3___closed__2;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_unbox(x_23);
lean_dec(x_23);
x_30 = l_Lean_Widget_ExprDiffTag_toString(x_29);
x_31 = lean_string_append(x_28, x_30);
lean_dec(x_30);
x_32 = l_List_mapTR_loop___at_Lean_Widget_instToStringExprDiff___spec__3___closed__3;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_2);
x_1 = x_21;
x_2 = x_34;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Widget_instToStringExprDiff___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("before: ", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Widget_instToStringExprDiff___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nafter: ", 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToStringExprDiff(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_RBMap_toList___at_Lean_Widget_instToStringExprDiff___spec__1(x_2);
x_4 = lean_box(0);
x_5 = l_List_mapTR_loop___at_Lean_Widget_instToStringExprDiff___spec__3(x_3, x_4);
x_6 = l_List_toString___at_Lean_MetavarContext_MkBinding_instToStringException___spec__2(x_5);
lean_dec(x_5);
x_7 = l_Lean_Widget_instToStringExprDiff___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lean_Widget_instToStringExprDiff___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_RBMap_toList___at_Lean_Widget_instToStringExprDiff___spec__1(x_11);
x_13 = l_List_mapTR_loop___at_Lean_Widget_instToStringExprDiff___spec__3(x_12, x_4);
x_14 = l_List_toString___at_Lean_MetavarContext_MkBinding_instToStringException___spec__2(x_13);
lean_dec(x_13);
x_15 = lean_string_append(x_10, x_14);
lean_dec(x_14);
x_16 = l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__3;
x_17 = lean_string_append(x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at_Lean_Widget_instToStringExprDiff___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_revFold___at_Lean_Widget_instToStringExprDiff___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Widget_ExprDiff_insertBeforeChange___spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = 0;
x_6 = lean_box(x_3);
x_7 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_6);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_5);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
x_14 = lean_nat_dec_lt(x_2, x_11);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = lean_nat_dec_eq(x_2, x_11);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_RBNode_ins___at_Lean_Widget_ExprDiff_insertBeforeChange___spec__2(x_13, x_2, x_3);
x_17 = 0;
lean_ctor_set(x_1, 3, x_16);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_17);
return x_1;
}
else
{
uint8_t x_18; lean_object* x_19; 
lean_dec(x_12);
lean_dec(x_11);
x_18 = 0;
x_19 = lean_box(x_3);
lean_ctor_set(x_1, 2, x_19);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_18);
return x_1;
}
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_RBNode_ins___at_Lean_Widget_ExprDiff_insertBeforeChange___spec__2(x_10, x_2, x_3);
x_21 = 0;
lean_ctor_set(x_1, 0, x_20);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_ctor_get(x_1, 2);
x_25 = lean_ctor_get(x_1, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_26 = lean_nat_dec_lt(x_2, x_23);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = lean_nat_dec_eq(x_2, x_23);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = l_Lean_RBNode_ins___at_Lean_Widget_ExprDiff_insertBeforeChange___spec__2(x_25, x_2, x_3);
x_29 = 0;
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_23);
lean_ctor_set(x_30, 2, x_24);
lean_ctor_set(x_30, 3, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_29);
return x_30;
}
else
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_24);
lean_dec(x_23);
x_31 = 0;
x_32 = lean_box(x_3);
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_22);
lean_ctor_set(x_33, 1, x_2);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_25);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_31);
return x_33;
}
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = l_Lean_RBNode_ins___at_Lean_Widget_ExprDiff_insertBeforeChange___spec__2(x_22, x_2, x_3);
x_35 = 0;
x_36 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_23);
lean_ctor_set(x_36, 2, x_24);
lean_ctor_set(x_36, 3, x_25);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_1);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_1, 0);
x_39 = lean_ctor_get(x_1, 1);
x_40 = lean_ctor_get(x_1, 2);
x_41 = lean_ctor_get(x_1, 3);
x_42 = lean_nat_dec_lt(x_2, x_39);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = lean_nat_dec_eq(x_2, x_39);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = l_Lean_RBNode_ins___at_Lean_Widget_ExprDiff_insertBeforeChange___spec__2(x_41, x_2, x_3);
x_45 = lean_ctor_get_uint8(x_44, sizeof(void*)*4);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_44, 3);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_44, 3);
lean_dec(x_49);
x_50 = lean_ctor_get(x_44, 0);
lean_dec(x_50);
lean_ctor_set(x_44, 0, x_47);
x_51 = 1;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_51);
return x_1;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_44, 1);
x_53 = lean_ctor_get(x_44, 2);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_44);
x_54 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_52);
lean_ctor_set(x_54, 2, x_53);
lean_ctor_set(x_54, 3, x_47);
lean_ctor_set_uint8(x_54, sizeof(void*)*4, x_45);
x_55 = 1;
lean_ctor_set(x_1, 3, x_54);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_55);
return x_1;
}
}
else
{
uint8_t x_56; 
x_56 = lean_ctor_get_uint8(x_47, sizeof(void*)*4);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_44);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_44, 1);
x_59 = lean_ctor_get(x_44, 2);
x_60 = lean_ctor_get(x_44, 3);
lean_dec(x_60);
x_61 = lean_ctor_get(x_44, 0);
lean_dec(x_61);
x_62 = !lean_is_exclusive(x_47);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_68; 
x_63 = lean_ctor_get(x_47, 0);
x_64 = lean_ctor_get(x_47, 1);
x_65 = lean_ctor_get(x_47, 2);
x_66 = lean_ctor_get(x_47, 3);
x_67 = 1;
lean_ctor_set(x_47, 3, x_46);
lean_ctor_set(x_47, 2, x_40);
lean_ctor_set(x_47, 1, x_39);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_67);
lean_ctor_set(x_44, 3, x_66);
lean_ctor_set(x_44, 2, x_65);
lean_ctor_set(x_44, 1, x_64);
lean_ctor_set(x_44, 0, x_63);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_67);
x_68 = 0;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set(x_1, 2, x_59);
lean_ctor_set(x_1, 1, x_58);
lean_ctor_set(x_1, 0, x_47);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_68);
return x_1;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; uint8_t x_75; 
x_69 = lean_ctor_get(x_47, 0);
x_70 = lean_ctor_get(x_47, 1);
x_71 = lean_ctor_get(x_47, 2);
x_72 = lean_ctor_get(x_47, 3);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_47);
x_73 = 1;
x_74 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_74, 0, x_38);
lean_ctor_set(x_74, 1, x_39);
lean_ctor_set(x_74, 2, x_40);
lean_ctor_set(x_74, 3, x_46);
lean_ctor_set_uint8(x_74, sizeof(void*)*4, x_73);
lean_ctor_set(x_44, 3, x_72);
lean_ctor_set(x_44, 2, x_71);
lean_ctor_set(x_44, 1, x_70);
lean_ctor_set(x_44, 0, x_69);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_73);
x_75 = 0;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set(x_1, 2, x_59);
lean_ctor_set(x_1, 1, x_58);
lean_ctor_set(x_1, 0, x_74);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_75);
return x_1;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_76 = lean_ctor_get(x_44, 1);
x_77 = lean_ctor_get(x_44, 2);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_44);
x_78 = lean_ctor_get(x_47, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_47, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_47, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_47, 3);
lean_inc(x_81);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_82 = x_47;
} else {
 lean_dec_ref(x_47);
 x_82 = lean_box(0);
}
x_83 = 1;
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(1, 4, 1);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_38);
lean_ctor_set(x_84, 1, x_39);
lean_ctor_set(x_84, 2, x_40);
lean_ctor_set(x_84, 3, x_46);
lean_ctor_set_uint8(x_84, sizeof(void*)*4, x_83);
x_85 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_85, 0, x_78);
lean_ctor_set(x_85, 1, x_79);
lean_ctor_set(x_85, 2, x_80);
lean_ctor_set(x_85, 3, x_81);
lean_ctor_set_uint8(x_85, sizeof(void*)*4, x_83);
x_86 = 0;
lean_ctor_set(x_1, 3, x_85);
lean_ctor_set(x_1, 2, x_77);
lean_ctor_set(x_1, 1, x_76);
lean_ctor_set(x_1, 0, x_84);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_86);
return x_1;
}
}
else
{
uint8_t x_87; 
lean_free_object(x_1);
x_87 = !lean_is_exclusive(x_47);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_88 = lean_ctor_get(x_47, 3);
lean_dec(x_88);
x_89 = lean_ctor_get(x_47, 2);
lean_dec(x_89);
x_90 = lean_ctor_get(x_47, 1);
lean_dec(x_90);
x_91 = lean_ctor_get(x_47, 0);
lean_dec(x_91);
x_92 = 1;
lean_ctor_set(x_47, 3, x_44);
lean_ctor_set(x_47, 2, x_40);
lean_ctor_set(x_47, 1, x_39);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_92);
return x_47;
}
else
{
uint8_t x_93; lean_object* x_94; 
lean_dec(x_47);
x_93 = 1;
x_94 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_94, 0, x_38);
lean_ctor_set(x_94, 1, x_39);
lean_ctor_set(x_94, 2, x_40);
lean_ctor_set(x_94, 3, x_44);
lean_ctor_set_uint8(x_94, sizeof(void*)*4, x_93);
return x_94;
}
}
}
}
else
{
uint8_t x_95; 
x_95 = lean_ctor_get_uint8(x_46, sizeof(void*)*4);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_44);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_44, 0);
lean_dec(x_97);
x_98 = !lean_is_exclusive(x_46);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_104; 
x_99 = lean_ctor_get(x_46, 0);
x_100 = lean_ctor_get(x_46, 1);
x_101 = lean_ctor_get(x_46, 2);
x_102 = lean_ctor_get(x_46, 3);
x_103 = 1;
lean_ctor_set(x_46, 3, x_99);
lean_ctor_set(x_46, 2, x_40);
lean_ctor_set(x_46, 1, x_39);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_103);
lean_ctor_set(x_44, 0, x_102);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_103);
x_104 = 0;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set(x_1, 2, x_101);
lean_ctor_set(x_1, 1, x_100);
lean_ctor_set(x_1, 0, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_104);
return x_1;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; uint8_t x_111; 
x_105 = lean_ctor_get(x_46, 0);
x_106 = lean_ctor_get(x_46, 1);
x_107 = lean_ctor_get(x_46, 2);
x_108 = lean_ctor_get(x_46, 3);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_46);
x_109 = 1;
x_110 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_110, 0, x_38);
lean_ctor_set(x_110, 1, x_39);
lean_ctor_set(x_110, 2, x_40);
lean_ctor_set(x_110, 3, x_105);
lean_ctor_set_uint8(x_110, sizeof(void*)*4, x_109);
lean_ctor_set(x_44, 0, x_108);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_109);
x_111 = 0;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set(x_1, 2, x_107);
lean_ctor_set(x_1, 1, x_106);
lean_ctor_set(x_1, 0, x_110);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_111);
return x_1;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_112 = lean_ctor_get(x_44, 1);
x_113 = lean_ctor_get(x_44, 2);
x_114 = lean_ctor_get(x_44, 3);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_44);
x_115 = lean_ctor_get(x_46, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_46, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_46, 2);
lean_inc(x_117);
x_118 = lean_ctor_get(x_46, 3);
lean_inc(x_118);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_119 = x_46;
} else {
 lean_dec_ref(x_46);
 x_119 = lean_box(0);
}
x_120 = 1;
if (lean_is_scalar(x_119)) {
 x_121 = lean_alloc_ctor(1, 4, 1);
} else {
 x_121 = x_119;
}
lean_ctor_set(x_121, 0, x_38);
lean_ctor_set(x_121, 1, x_39);
lean_ctor_set(x_121, 2, x_40);
lean_ctor_set(x_121, 3, x_115);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_120);
x_122 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_122, 0, x_118);
lean_ctor_set(x_122, 1, x_112);
lean_ctor_set(x_122, 2, x_113);
lean_ctor_set(x_122, 3, x_114);
lean_ctor_set_uint8(x_122, sizeof(void*)*4, x_120);
x_123 = 0;
lean_ctor_set(x_1, 3, x_122);
lean_ctor_set(x_1, 2, x_117);
lean_ctor_set(x_1, 1, x_116);
lean_ctor_set(x_1, 0, x_121);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_123);
return x_1;
}
}
else
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_44, 3);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 0)
{
uint8_t x_125; 
lean_free_object(x_1);
x_125 = !lean_is_exclusive(x_46);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_126 = lean_ctor_get(x_46, 3);
lean_dec(x_126);
x_127 = lean_ctor_get(x_46, 2);
lean_dec(x_127);
x_128 = lean_ctor_get(x_46, 1);
lean_dec(x_128);
x_129 = lean_ctor_get(x_46, 0);
lean_dec(x_129);
x_130 = 1;
lean_ctor_set(x_46, 3, x_44);
lean_ctor_set(x_46, 2, x_40);
lean_ctor_set(x_46, 1, x_39);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_130);
return x_46;
}
else
{
uint8_t x_131; lean_object* x_132; 
lean_dec(x_46);
x_131 = 1;
x_132 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_132, 0, x_38);
lean_ctor_set(x_132, 1, x_39);
lean_ctor_set(x_132, 2, x_40);
lean_ctor_set(x_132, 3, x_44);
lean_ctor_set_uint8(x_132, sizeof(void*)*4, x_131);
return x_132;
}
}
else
{
uint8_t x_133; 
x_133 = lean_ctor_get_uint8(x_124, sizeof(void*)*4);
if (x_133 == 0)
{
uint8_t x_134; 
lean_free_object(x_1);
x_134 = !lean_is_exclusive(x_44);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_135 = lean_ctor_get(x_44, 3);
lean_dec(x_135);
x_136 = lean_ctor_get(x_44, 0);
lean_dec(x_136);
x_137 = !lean_is_exclusive(x_124);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; uint8_t x_143; 
x_138 = lean_ctor_get(x_124, 0);
x_139 = lean_ctor_get(x_124, 1);
x_140 = lean_ctor_get(x_124, 2);
x_141 = lean_ctor_get(x_124, 3);
x_142 = 1;
lean_inc(x_46);
lean_ctor_set(x_124, 3, x_46);
lean_ctor_set(x_124, 2, x_40);
lean_ctor_set(x_124, 1, x_39);
lean_ctor_set(x_124, 0, x_38);
x_143 = !lean_is_exclusive(x_46);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_144 = lean_ctor_get(x_46, 3);
lean_dec(x_144);
x_145 = lean_ctor_get(x_46, 2);
lean_dec(x_145);
x_146 = lean_ctor_get(x_46, 1);
lean_dec(x_146);
x_147 = lean_ctor_get(x_46, 0);
lean_dec(x_147);
lean_ctor_set_uint8(x_124, sizeof(void*)*4, x_142);
lean_ctor_set(x_46, 3, x_141);
lean_ctor_set(x_46, 2, x_140);
lean_ctor_set(x_46, 1, x_139);
lean_ctor_set(x_46, 0, x_138);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_142);
x_148 = 0;
lean_ctor_set(x_44, 3, x_46);
lean_ctor_set(x_44, 0, x_124);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_148);
return x_44;
}
else
{
lean_object* x_149; uint8_t x_150; 
lean_dec(x_46);
lean_ctor_set_uint8(x_124, sizeof(void*)*4, x_142);
x_149 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_149, 0, x_138);
lean_ctor_set(x_149, 1, x_139);
lean_ctor_set(x_149, 2, x_140);
lean_ctor_set(x_149, 3, x_141);
lean_ctor_set_uint8(x_149, sizeof(void*)*4, x_142);
x_150 = 0;
lean_ctor_set(x_44, 3, x_149);
lean_ctor_set(x_44, 0, x_124);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_150);
return x_44;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_151 = lean_ctor_get(x_124, 0);
x_152 = lean_ctor_get(x_124, 1);
x_153 = lean_ctor_get(x_124, 2);
x_154 = lean_ctor_get(x_124, 3);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_124);
x_155 = 1;
lean_inc(x_46);
x_156 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_156, 0, x_38);
lean_ctor_set(x_156, 1, x_39);
lean_ctor_set(x_156, 2, x_40);
lean_ctor_set(x_156, 3, x_46);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_157 = x_46;
} else {
 lean_dec_ref(x_46);
 x_157 = lean_box(0);
}
lean_ctor_set_uint8(x_156, sizeof(void*)*4, x_155);
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 4, 1);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_151);
lean_ctor_set(x_158, 1, x_152);
lean_ctor_set(x_158, 2, x_153);
lean_ctor_set(x_158, 3, x_154);
lean_ctor_set_uint8(x_158, sizeof(void*)*4, x_155);
x_159 = 0;
lean_ctor_set(x_44, 3, x_158);
lean_ctor_set(x_44, 0, x_156);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_159);
return x_44;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; 
x_160 = lean_ctor_get(x_44, 1);
x_161 = lean_ctor_get(x_44, 2);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_44);
x_162 = lean_ctor_get(x_124, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_124, 1);
lean_inc(x_163);
x_164 = lean_ctor_get(x_124, 2);
lean_inc(x_164);
x_165 = lean_ctor_get(x_124, 3);
lean_inc(x_165);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 lean_ctor_release(x_124, 2);
 lean_ctor_release(x_124, 3);
 x_166 = x_124;
} else {
 lean_dec_ref(x_124);
 x_166 = lean_box(0);
}
x_167 = 1;
lean_inc(x_46);
if (lean_is_scalar(x_166)) {
 x_168 = lean_alloc_ctor(1, 4, 1);
} else {
 x_168 = x_166;
}
lean_ctor_set(x_168, 0, x_38);
lean_ctor_set(x_168, 1, x_39);
lean_ctor_set(x_168, 2, x_40);
lean_ctor_set(x_168, 3, x_46);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_169 = x_46;
} else {
 lean_dec_ref(x_46);
 x_169 = lean_box(0);
}
lean_ctor_set_uint8(x_168, sizeof(void*)*4, x_167);
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 4, 1);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_162);
lean_ctor_set(x_170, 1, x_163);
lean_ctor_set(x_170, 2, x_164);
lean_ctor_set(x_170, 3, x_165);
lean_ctor_set_uint8(x_170, sizeof(void*)*4, x_167);
x_171 = 0;
x_172 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_172, 0, x_168);
lean_ctor_set(x_172, 1, x_160);
lean_ctor_set(x_172, 2, x_161);
lean_ctor_set(x_172, 3, x_170);
lean_ctor_set_uint8(x_172, sizeof(void*)*4, x_171);
return x_172;
}
}
else
{
uint8_t x_173; 
x_173 = !lean_is_exclusive(x_44);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_174 = lean_ctor_get(x_44, 3);
lean_dec(x_174);
x_175 = lean_ctor_get(x_44, 0);
lean_dec(x_175);
x_176 = !lean_is_exclusive(x_46);
if (x_176 == 0)
{
uint8_t x_177; 
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_133);
x_177 = 1;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_177);
return x_1;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_178 = lean_ctor_get(x_46, 0);
x_179 = lean_ctor_get(x_46, 1);
x_180 = lean_ctor_get(x_46, 2);
x_181 = lean_ctor_get(x_46, 3);
lean_inc(x_181);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_46);
x_182 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_182, 0, x_178);
lean_ctor_set(x_182, 1, x_179);
lean_ctor_set(x_182, 2, x_180);
lean_ctor_set(x_182, 3, x_181);
lean_ctor_set_uint8(x_182, sizeof(void*)*4, x_133);
lean_ctor_set(x_44, 0, x_182);
x_183 = 1;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_183);
return x_1;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_184 = lean_ctor_get(x_44, 1);
x_185 = lean_ctor_get(x_44, 2);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_44);
x_186 = lean_ctor_get(x_46, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_46, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_46, 2);
lean_inc(x_188);
x_189 = lean_ctor_get(x_46, 3);
lean_inc(x_189);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_190 = x_46;
} else {
 lean_dec_ref(x_46);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 4, 1);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_186);
lean_ctor_set(x_191, 1, x_187);
lean_ctor_set(x_191, 2, x_188);
lean_ctor_set(x_191, 3, x_189);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_133);
x_192 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_184);
lean_ctor_set(x_192, 2, x_185);
lean_ctor_set(x_192, 3, x_124);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_45);
x_193 = 1;
lean_ctor_set(x_1, 3, x_192);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_193);
return x_1;
}
}
}
}
}
}
else
{
uint8_t x_194; 
x_194 = 1;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_194);
return x_1;
}
}
else
{
uint8_t x_195; lean_object* x_196; 
lean_dec(x_40);
lean_dec(x_39);
x_195 = 1;
x_196 = lean_box(x_3);
lean_ctor_set(x_1, 2, x_196);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_195);
return x_1;
}
}
else
{
lean_object* x_197; uint8_t x_198; 
x_197 = l_Lean_RBNode_ins___at_Lean_Widget_ExprDiff_insertBeforeChange___spec__2(x_38, x_2, x_3);
x_198 = lean_ctor_get_uint8(x_197, sizeof(void*)*4);
if (x_198 == 0)
{
lean_object* x_199; 
x_199 = lean_ctor_get(x_197, 0);
lean_inc(x_199);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; 
x_200 = lean_ctor_get(x_197, 3);
lean_inc(x_200);
if (lean_obj_tag(x_200) == 0)
{
uint8_t x_201; 
x_201 = !lean_is_exclusive(x_197);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_202 = lean_ctor_get(x_197, 3);
lean_dec(x_202);
x_203 = lean_ctor_get(x_197, 0);
lean_dec(x_203);
lean_ctor_set(x_197, 0, x_200);
x_204 = 1;
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_204);
return x_1;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_205 = lean_ctor_get(x_197, 1);
x_206 = lean_ctor_get(x_197, 2);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_197);
x_207 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_207, 0, x_200);
lean_ctor_set(x_207, 1, x_205);
lean_ctor_set(x_207, 2, x_206);
lean_ctor_set(x_207, 3, x_200);
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_198);
x_208 = 1;
lean_ctor_set(x_1, 0, x_207);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_208);
return x_1;
}
}
else
{
uint8_t x_209; 
x_209 = lean_ctor_get_uint8(x_200, sizeof(void*)*4);
if (x_209 == 0)
{
uint8_t x_210; 
x_210 = !lean_is_exclusive(x_197);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; 
x_211 = lean_ctor_get(x_197, 1);
x_212 = lean_ctor_get(x_197, 2);
x_213 = lean_ctor_get(x_197, 3);
lean_dec(x_213);
x_214 = lean_ctor_get(x_197, 0);
lean_dec(x_214);
x_215 = !lean_is_exclusive(x_200);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; uint8_t x_221; 
x_216 = lean_ctor_get(x_200, 0);
x_217 = lean_ctor_get(x_200, 1);
x_218 = lean_ctor_get(x_200, 2);
x_219 = lean_ctor_get(x_200, 3);
x_220 = 1;
lean_ctor_set(x_200, 3, x_216);
lean_ctor_set(x_200, 2, x_212);
lean_ctor_set(x_200, 1, x_211);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set_uint8(x_200, sizeof(void*)*4, x_220);
lean_ctor_set(x_197, 3, x_41);
lean_ctor_set(x_197, 2, x_40);
lean_ctor_set(x_197, 1, x_39);
lean_ctor_set(x_197, 0, x_219);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_220);
x_221 = 0;
lean_ctor_set(x_1, 3, x_197);
lean_ctor_set(x_1, 2, x_218);
lean_ctor_set(x_1, 1, x_217);
lean_ctor_set(x_1, 0, x_200);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_221);
return x_1;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; uint8_t x_228; 
x_222 = lean_ctor_get(x_200, 0);
x_223 = lean_ctor_get(x_200, 1);
x_224 = lean_ctor_get(x_200, 2);
x_225 = lean_ctor_get(x_200, 3);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_200);
x_226 = 1;
x_227 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_227, 0, x_199);
lean_ctor_set(x_227, 1, x_211);
lean_ctor_set(x_227, 2, x_212);
lean_ctor_set(x_227, 3, x_222);
lean_ctor_set_uint8(x_227, sizeof(void*)*4, x_226);
lean_ctor_set(x_197, 3, x_41);
lean_ctor_set(x_197, 2, x_40);
lean_ctor_set(x_197, 1, x_39);
lean_ctor_set(x_197, 0, x_225);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_226);
x_228 = 0;
lean_ctor_set(x_1, 3, x_197);
lean_ctor_set(x_1, 2, x_224);
lean_ctor_set(x_1, 1, x_223);
lean_ctor_set(x_1, 0, x_227);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_228);
return x_1;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_229 = lean_ctor_get(x_197, 1);
x_230 = lean_ctor_get(x_197, 2);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_197);
x_231 = lean_ctor_get(x_200, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_200, 1);
lean_inc(x_232);
x_233 = lean_ctor_get(x_200, 2);
lean_inc(x_233);
x_234 = lean_ctor_get(x_200, 3);
lean_inc(x_234);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 lean_ctor_release(x_200, 2);
 lean_ctor_release(x_200, 3);
 x_235 = x_200;
} else {
 lean_dec_ref(x_200);
 x_235 = lean_box(0);
}
x_236 = 1;
if (lean_is_scalar(x_235)) {
 x_237 = lean_alloc_ctor(1, 4, 1);
} else {
 x_237 = x_235;
}
lean_ctor_set(x_237, 0, x_199);
lean_ctor_set(x_237, 1, x_229);
lean_ctor_set(x_237, 2, x_230);
lean_ctor_set(x_237, 3, x_231);
lean_ctor_set_uint8(x_237, sizeof(void*)*4, x_236);
x_238 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_238, 0, x_234);
lean_ctor_set(x_238, 1, x_39);
lean_ctor_set(x_238, 2, x_40);
lean_ctor_set(x_238, 3, x_41);
lean_ctor_set_uint8(x_238, sizeof(void*)*4, x_236);
x_239 = 0;
lean_ctor_set(x_1, 3, x_238);
lean_ctor_set(x_1, 2, x_233);
lean_ctor_set(x_1, 1, x_232);
lean_ctor_set(x_1, 0, x_237);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_239);
return x_1;
}
}
else
{
uint8_t x_240; 
lean_free_object(x_1);
x_240 = !lean_is_exclusive(x_200);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_241 = lean_ctor_get(x_200, 3);
lean_dec(x_241);
x_242 = lean_ctor_get(x_200, 2);
lean_dec(x_242);
x_243 = lean_ctor_get(x_200, 1);
lean_dec(x_243);
x_244 = lean_ctor_get(x_200, 0);
lean_dec(x_244);
x_245 = 1;
lean_ctor_set(x_200, 3, x_41);
lean_ctor_set(x_200, 2, x_40);
lean_ctor_set(x_200, 1, x_39);
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set_uint8(x_200, sizeof(void*)*4, x_245);
return x_200;
}
else
{
uint8_t x_246; lean_object* x_247; 
lean_dec(x_200);
x_246 = 1;
x_247 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_247, 0, x_197);
lean_ctor_set(x_247, 1, x_39);
lean_ctor_set(x_247, 2, x_40);
lean_ctor_set(x_247, 3, x_41);
lean_ctor_set_uint8(x_247, sizeof(void*)*4, x_246);
return x_247;
}
}
}
}
else
{
uint8_t x_248; 
x_248 = lean_ctor_get_uint8(x_199, sizeof(void*)*4);
if (x_248 == 0)
{
uint8_t x_249; 
x_249 = !lean_is_exclusive(x_197);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_250 = lean_ctor_get(x_197, 1);
x_251 = lean_ctor_get(x_197, 2);
x_252 = lean_ctor_get(x_197, 3);
x_253 = lean_ctor_get(x_197, 0);
lean_dec(x_253);
x_254 = !lean_is_exclusive(x_199);
if (x_254 == 0)
{
uint8_t x_255; uint8_t x_256; 
x_255 = 1;
lean_ctor_set_uint8(x_199, sizeof(void*)*4, x_255);
lean_ctor_set(x_197, 3, x_41);
lean_ctor_set(x_197, 2, x_40);
lean_ctor_set(x_197, 1, x_39);
lean_ctor_set(x_197, 0, x_252);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_255);
x_256 = 0;
lean_ctor_set(x_1, 3, x_197);
lean_ctor_set(x_1, 2, x_251);
lean_ctor_set(x_1, 1, x_250);
lean_ctor_set(x_1, 0, x_199);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_256);
return x_1;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; lean_object* x_262; uint8_t x_263; 
x_257 = lean_ctor_get(x_199, 0);
x_258 = lean_ctor_get(x_199, 1);
x_259 = lean_ctor_get(x_199, 2);
x_260 = lean_ctor_get(x_199, 3);
lean_inc(x_260);
lean_inc(x_259);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_199);
x_261 = 1;
x_262 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_262, 0, x_257);
lean_ctor_set(x_262, 1, x_258);
lean_ctor_set(x_262, 2, x_259);
lean_ctor_set(x_262, 3, x_260);
lean_ctor_set_uint8(x_262, sizeof(void*)*4, x_261);
lean_ctor_set(x_197, 3, x_41);
lean_ctor_set(x_197, 2, x_40);
lean_ctor_set(x_197, 1, x_39);
lean_ctor_set(x_197, 0, x_252);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_261);
x_263 = 0;
lean_ctor_set(x_1, 3, x_197);
lean_ctor_set(x_1, 2, x_251);
lean_ctor_set(x_1, 1, x_250);
lean_ctor_set(x_1, 0, x_262);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_263);
return x_1;
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_264 = lean_ctor_get(x_197, 1);
x_265 = lean_ctor_get(x_197, 2);
x_266 = lean_ctor_get(x_197, 3);
lean_inc(x_266);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_197);
x_267 = lean_ctor_get(x_199, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_199, 1);
lean_inc(x_268);
x_269 = lean_ctor_get(x_199, 2);
lean_inc(x_269);
x_270 = lean_ctor_get(x_199, 3);
lean_inc(x_270);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 lean_ctor_release(x_199, 2);
 lean_ctor_release(x_199, 3);
 x_271 = x_199;
} else {
 lean_dec_ref(x_199);
 x_271 = lean_box(0);
}
x_272 = 1;
if (lean_is_scalar(x_271)) {
 x_273 = lean_alloc_ctor(1, 4, 1);
} else {
 x_273 = x_271;
}
lean_ctor_set(x_273, 0, x_267);
lean_ctor_set(x_273, 1, x_268);
lean_ctor_set(x_273, 2, x_269);
lean_ctor_set(x_273, 3, x_270);
lean_ctor_set_uint8(x_273, sizeof(void*)*4, x_272);
x_274 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_274, 0, x_266);
lean_ctor_set(x_274, 1, x_39);
lean_ctor_set(x_274, 2, x_40);
lean_ctor_set(x_274, 3, x_41);
lean_ctor_set_uint8(x_274, sizeof(void*)*4, x_272);
x_275 = 0;
lean_ctor_set(x_1, 3, x_274);
lean_ctor_set(x_1, 2, x_265);
lean_ctor_set(x_1, 1, x_264);
lean_ctor_set(x_1, 0, x_273);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_275);
return x_1;
}
}
else
{
lean_object* x_276; 
x_276 = lean_ctor_get(x_197, 3);
lean_inc(x_276);
if (lean_obj_tag(x_276) == 0)
{
uint8_t x_277; 
lean_free_object(x_1);
x_277 = !lean_is_exclusive(x_199);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
x_278 = lean_ctor_get(x_199, 3);
lean_dec(x_278);
x_279 = lean_ctor_get(x_199, 2);
lean_dec(x_279);
x_280 = lean_ctor_get(x_199, 1);
lean_dec(x_280);
x_281 = lean_ctor_get(x_199, 0);
lean_dec(x_281);
x_282 = 1;
lean_ctor_set(x_199, 3, x_41);
lean_ctor_set(x_199, 2, x_40);
lean_ctor_set(x_199, 1, x_39);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set_uint8(x_199, sizeof(void*)*4, x_282);
return x_199;
}
else
{
uint8_t x_283; lean_object* x_284; 
lean_dec(x_199);
x_283 = 1;
x_284 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_284, 0, x_197);
lean_ctor_set(x_284, 1, x_39);
lean_ctor_set(x_284, 2, x_40);
lean_ctor_set(x_284, 3, x_41);
lean_ctor_set_uint8(x_284, sizeof(void*)*4, x_283);
return x_284;
}
}
else
{
uint8_t x_285; 
x_285 = lean_ctor_get_uint8(x_276, sizeof(void*)*4);
if (x_285 == 0)
{
uint8_t x_286; 
lean_free_object(x_1);
x_286 = !lean_is_exclusive(x_197);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; 
x_287 = lean_ctor_get(x_197, 1);
x_288 = lean_ctor_get(x_197, 2);
x_289 = lean_ctor_get(x_197, 3);
lean_dec(x_289);
x_290 = lean_ctor_get(x_197, 0);
lean_dec(x_290);
x_291 = !lean_is_exclusive(x_276);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; uint8_t x_297; 
x_292 = lean_ctor_get(x_276, 0);
x_293 = lean_ctor_get(x_276, 1);
x_294 = lean_ctor_get(x_276, 2);
x_295 = lean_ctor_get(x_276, 3);
x_296 = 1;
lean_inc(x_199);
lean_ctor_set(x_276, 3, x_292);
lean_ctor_set(x_276, 2, x_288);
lean_ctor_set(x_276, 1, x_287);
lean_ctor_set(x_276, 0, x_199);
x_297 = !lean_is_exclusive(x_199);
if (x_297 == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_298 = lean_ctor_get(x_199, 3);
lean_dec(x_298);
x_299 = lean_ctor_get(x_199, 2);
lean_dec(x_299);
x_300 = lean_ctor_get(x_199, 1);
lean_dec(x_300);
x_301 = lean_ctor_get(x_199, 0);
lean_dec(x_301);
lean_ctor_set_uint8(x_276, sizeof(void*)*4, x_296);
lean_ctor_set(x_199, 3, x_41);
lean_ctor_set(x_199, 2, x_40);
lean_ctor_set(x_199, 1, x_39);
lean_ctor_set(x_199, 0, x_295);
lean_ctor_set_uint8(x_199, sizeof(void*)*4, x_296);
x_302 = 0;
lean_ctor_set(x_197, 3, x_199);
lean_ctor_set(x_197, 2, x_294);
lean_ctor_set(x_197, 1, x_293);
lean_ctor_set(x_197, 0, x_276);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_302);
return x_197;
}
else
{
lean_object* x_303; uint8_t x_304; 
lean_dec(x_199);
lean_ctor_set_uint8(x_276, sizeof(void*)*4, x_296);
x_303 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_303, 0, x_295);
lean_ctor_set(x_303, 1, x_39);
lean_ctor_set(x_303, 2, x_40);
lean_ctor_set(x_303, 3, x_41);
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_296);
x_304 = 0;
lean_ctor_set(x_197, 3, x_303);
lean_ctor_set(x_197, 2, x_294);
lean_ctor_set(x_197, 1, x_293);
lean_ctor_set(x_197, 0, x_276);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_304);
return x_197;
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; 
x_305 = lean_ctor_get(x_276, 0);
x_306 = lean_ctor_get(x_276, 1);
x_307 = lean_ctor_get(x_276, 2);
x_308 = lean_ctor_get(x_276, 3);
lean_inc(x_308);
lean_inc(x_307);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_276);
x_309 = 1;
lean_inc(x_199);
x_310 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_310, 0, x_199);
lean_ctor_set(x_310, 1, x_287);
lean_ctor_set(x_310, 2, x_288);
lean_ctor_set(x_310, 3, x_305);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 lean_ctor_release(x_199, 2);
 lean_ctor_release(x_199, 3);
 x_311 = x_199;
} else {
 lean_dec_ref(x_199);
 x_311 = lean_box(0);
}
lean_ctor_set_uint8(x_310, sizeof(void*)*4, x_309);
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 4, 1);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_308);
lean_ctor_set(x_312, 1, x_39);
lean_ctor_set(x_312, 2, x_40);
lean_ctor_set(x_312, 3, x_41);
lean_ctor_set_uint8(x_312, sizeof(void*)*4, x_309);
x_313 = 0;
lean_ctor_set(x_197, 3, x_312);
lean_ctor_set(x_197, 2, x_307);
lean_ctor_set(x_197, 1, x_306);
lean_ctor_set(x_197, 0, x_310);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_313);
return x_197;
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; lean_object* x_326; 
x_314 = lean_ctor_get(x_197, 1);
x_315 = lean_ctor_get(x_197, 2);
lean_inc(x_315);
lean_inc(x_314);
lean_dec(x_197);
x_316 = lean_ctor_get(x_276, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_276, 1);
lean_inc(x_317);
x_318 = lean_ctor_get(x_276, 2);
lean_inc(x_318);
x_319 = lean_ctor_get(x_276, 3);
lean_inc(x_319);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 lean_ctor_release(x_276, 2);
 lean_ctor_release(x_276, 3);
 x_320 = x_276;
} else {
 lean_dec_ref(x_276);
 x_320 = lean_box(0);
}
x_321 = 1;
lean_inc(x_199);
if (lean_is_scalar(x_320)) {
 x_322 = lean_alloc_ctor(1, 4, 1);
} else {
 x_322 = x_320;
}
lean_ctor_set(x_322, 0, x_199);
lean_ctor_set(x_322, 1, x_314);
lean_ctor_set(x_322, 2, x_315);
lean_ctor_set(x_322, 3, x_316);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 lean_ctor_release(x_199, 2);
 lean_ctor_release(x_199, 3);
 x_323 = x_199;
} else {
 lean_dec_ref(x_199);
 x_323 = lean_box(0);
}
lean_ctor_set_uint8(x_322, sizeof(void*)*4, x_321);
if (lean_is_scalar(x_323)) {
 x_324 = lean_alloc_ctor(1, 4, 1);
} else {
 x_324 = x_323;
}
lean_ctor_set(x_324, 0, x_319);
lean_ctor_set(x_324, 1, x_39);
lean_ctor_set(x_324, 2, x_40);
lean_ctor_set(x_324, 3, x_41);
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_321);
x_325 = 0;
x_326 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_326, 0, x_322);
lean_ctor_set(x_326, 1, x_317);
lean_ctor_set(x_326, 2, x_318);
lean_ctor_set(x_326, 3, x_324);
lean_ctor_set_uint8(x_326, sizeof(void*)*4, x_325);
return x_326;
}
}
else
{
uint8_t x_327; 
x_327 = !lean_is_exclusive(x_197);
if (x_327 == 0)
{
lean_object* x_328; lean_object* x_329; uint8_t x_330; 
x_328 = lean_ctor_get(x_197, 3);
lean_dec(x_328);
x_329 = lean_ctor_get(x_197, 0);
lean_dec(x_329);
x_330 = !lean_is_exclusive(x_199);
if (x_330 == 0)
{
uint8_t x_331; 
lean_ctor_set_uint8(x_199, sizeof(void*)*4, x_285);
x_331 = 1;
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_331);
return x_1;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; 
x_332 = lean_ctor_get(x_199, 0);
x_333 = lean_ctor_get(x_199, 1);
x_334 = lean_ctor_get(x_199, 2);
x_335 = lean_ctor_get(x_199, 3);
lean_inc(x_335);
lean_inc(x_334);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_199);
x_336 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_336, 0, x_332);
lean_ctor_set(x_336, 1, x_333);
lean_ctor_set(x_336, 2, x_334);
lean_ctor_set(x_336, 3, x_335);
lean_ctor_set_uint8(x_336, sizeof(void*)*4, x_285);
lean_ctor_set(x_197, 0, x_336);
x_337 = 1;
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_337);
return x_1;
}
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; uint8_t x_347; 
x_338 = lean_ctor_get(x_197, 1);
x_339 = lean_ctor_get(x_197, 2);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_197);
x_340 = lean_ctor_get(x_199, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_199, 1);
lean_inc(x_341);
x_342 = lean_ctor_get(x_199, 2);
lean_inc(x_342);
x_343 = lean_ctor_get(x_199, 3);
lean_inc(x_343);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 lean_ctor_release(x_199, 2);
 lean_ctor_release(x_199, 3);
 x_344 = x_199;
} else {
 lean_dec_ref(x_199);
 x_344 = lean_box(0);
}
if (lean_is_scalar(x_344)) {
 x_345 = lean_alloc_ctor(1, 4, 1);
} else {
 x_345 = x_344;
}
lean_ctor_set(x_345, 0, x_340);
lean_ctor_set(x_345, 1, x_341);
lean_ctor_set(x_345, 2, x_342);
lean_ctor_set(x_345, 3, x_343);
lean_ctor_set_uint8(x_345, sizeof(void*)*4, x_285);
x_346 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_338);
lean_ctor_set(x_346, 2, x_339);
lean_ctor_set(x_346, 3, x_276);
lean_ctor_set_uint8(x_346, sizeof(void*)*4, x_198);
x_347 = 1;
lean_ctor_set(x_1, 0, x_346);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_347);
return x_1;
}
}
}
}
}
}
else
{
uint8_t x_348; 
x_348 = 1;
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_348);
return x_1;
}
}
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; uint8_t x_353; 
x_349 = lean_ctor_get(x_1, 0);
x_350 = lean_ctor_get(x_1, 1);
x_351 = lean_ctor_get(x_1, 2);
x_352 = lean_ctor_get(x_1, 3);
lean_inc(x_352);
lean_inc(x_351);
lean_inc(x_350);
lean_inc(x_349);
lean_dec(x_1);
x_353 = lean_nat_dec_lt(x_2, x_350);
if (x_353 == 0)
{
uint8_t x_354; 
x_354 = lean_nat_dec_eq(x_2, x_350);
if (x_354 == 0)
{
lean_object* x_355; uint8_t x_356; 
x_355 = l_Lean_RBNode_ins___at_Lean_Widget_ExprDiff_insertBeforeChange___spec__2(x_352, x_2, x_3);
x_356 = lean_ctor_get_uint8(x_355, sizeof(void*)*4);
if (x_356 == 0)
{
lean_object* x_357; 
x_357 = lean_ctor_get(x_355, 0);
lean_inc(x_357);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; 
x_358 = lean_ctor_get(x_355, 3);
lean_inc(x_358);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; uint8_t x_363; lean_object* x_364; 
x_359 = lean_ctor_get(x_355, 1);
lean_inc(x_359);
x_360 = lean_ctor_get(x_355, 2);
lean_inc(x_360);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 lean_ctor_release(x_355, 2);
 lean_ctor_release(x_355, 3);
 x_361 = x_355;
} else {
 lean_dec_ref(x_355);
 x_361 = lean_box(0);
}
if (lean_is_scalar(x_361)) {
 x_362 = lean_alloc_ctor(1, 4, 1);
} else {
 x_362 = x_361;
}
lean_ctor_set(x_362, 0, x_358);
lean_ctor_set(x_362, 1, x_359);
lean_ctor_set(x_362, 2, x_360);
lean_ctor_set(x_362, 3, x_358);
lean_ctor_set_uint8(x_362, sizeof(void*)*4, x_356);
x_363 = 1;
x_364 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_364, 0, x_349);
lean_ctor_set(x_364, 1, x_350);
lean_ctor_set(x_364, 2, x_351);
lean_ctor_set(x_364, 3, x_362);
lean_ctor_set_uint8(x_364, sizeof(void*)*4, x_363);
return x_364;
}
else
{
uint8_t x_365; 
x_365 = lean_ctor_get_uint8(x_358, sizeof(void*)*4);
if (x_365 == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; uint8_t x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; lean_object* x_378; 
x_366 = lean_ctor_get(x_355, 1);
lean_inc(x_366);
x_367 = lean_ctor_get(x_355, 2);
lean_inc(x_367);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 lean_ctor_release(x_355, 2);
 lean_ctor_release(x_355, 3);
 x_368 = x_355;
} else {
 lean_dec_ref(x_355);
 x_368 = lean_box(0);
}
x_369 = lean_ctor_get(x_358, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_358, 1);
lean_inc(x_370);
x_371 = lean_ctor_get(x_358, 2);
lean_inc(x_371);
x_372 = lean_ctor_get(x_358, 3);
lean_inc(x_372);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 lean_ctor_release(x_358, 2);
 lean_ctor_release(x_358, 3);
 x_373 = x_358;
} else {
 lean_dec_ref(x_358);
 x_373 = lean_box(0);
}
x_374 = 1;
if (lean_is_scalar(x_373)) {
 x_375 = lean_alloc_ctor(1, 4, 1);
} else {
 x_375 = x_373;
}
lean_ctor_set(x_375, 0, x_349);
lean_ctor_set(x_375, 1, x_350);
lean_ctor_set(x_375, 2, x_351);
lean_ctor_set(x_375, 3, x_357);
lean_ctor_set_uint8(x_375, sizeof(void*)*4, x_374);
if (lean_is_scalar(x_368)) {
 x_376 = lean_alloc_ctor(1, 4, 1);
} else {
 x_376 = x_368;
}
lean_ctor_set(x_376, 0, x_369);
lean_ctor_set(x_376, 1, x_370);
lean_ctor_set(x_376, 2, x_371);
lean_ctor_set(x_376, 3, x_372);
lean_ctor_set_uint8(x_376, sizeof(void*)*4, x_374);
x_377 = 0;
x_378 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_378, 0, x_375);
lean_ctor_set(x_378, 1, x_366);
lean_ctor_set(x_378, 2, x_367);
lean_ctor_set(x_378, 3, x_376);
lean_ctor_set_uint8(x_378, sizeof(void*)*4, x_377);
return x_378;
}
else
{
lean_object* x_379; uint8_t x_380; lean_object* x_381; 
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 lean_ctor_release(x_358, 2);
 lean_ctor_release(x_358, 3);
 x_379 = x_358;
} else {
 lean_dec_ref(x_358);
 x_379 = lean_box(0);
}
x_380 = 1;
if (lean_is_scalar(x_379)) {
 x_381 = lean_alloc_ctor(1, 4, 1);
} else {
 x_381 = x_379;
}
lean_ctor_set(x_381, 0, x_349);
lean_ctor_set(x_381, 1, x_350);
lean_ctor_set(x_381, 2, x_351);
lean_ctor_set(x_381, 3, x_355);
lean_ctor_set_uint8(x_381, sizeof(void*)*4, x_380);
return x_381;
}
}
}
else
{
uint8_t x_382; 
x_382 = lean_ctor_get_uint8(x_357, sizeof(void*)*4);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; lean_object* x_393; lean_object* x_394; uint8_t x_395; lean_object* x_396; 
x_383 = lean_ctor_get(x_355, 1);
lean_inc(x_383);
x_384 = lean_ctor_get(x_355, 2);
lean_inc(x_384);
x_385 = lean_ctor_get(x_355, 3);
lean_inc(x_385);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 lean_ctor_release(x_355, 2);
 lean_ctor_release(x_355, 3);
 x_386 = x_355;
} else {
 lean_dec_ref(x_355);
 x_386 = lean_box(0);
}
x_387 = lean_ctor_get(x_357, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_357, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_357, 2);
lean_inc(x_389);
x_390 = lean_ctor_get(x_357, 3);
lean_inc(x_390);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 lean_ctor_release(x_357, 2);
 lean_ctor_release(x_357, 3);
 x_391 = x_357;
} else {
 lean_dec_ref(x_357);
 x_391 = lean_box(0);
}
x_392 = 1;
if (lean_is_scalar(x_391)) {
 x_393 = lean_alloc_ctor(1, 4, 1);
} else {
 x_393 = x_391;
}
lean_ctor_set(x_393, 0, x_349);
lean_ctor_set(x_393, 1, x_350);
lean_ctor_set(x_393, 2, x_351);
lean_ctor_set(x_393, 3, x_387);
lean_ctor_set_uint8(x_393, sizeof(void*)*4, x_392);
if (lean_is_scalar(x_386)) {
 x_394 = lean_alloc_ctor(1, 4, 1);
} else {
 x_394 = x_386;
}
lean_ctor_set(x_394, 0, x_390);
lean_ctor_set(x_394, 1, x_383);
lean_ctor_set(x_394, 2, x_384);
lean_ctor_set(x_394, 3, x_385);
lean_ctor_set_uint8(x_394, sizeof(void*)*4, x_392);
x_395 = 0;
x_396 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_396, 0, x_393);
lean_ctor_set(x_396, 1, x_388);
lean_ctor_set(x_396, 2, x_389);
lean_ctor_set(x_396, 3, x_394);
lean_ctor_set_uint8(x_396, sizeof(void*)*4, x_395);
return x_396;
}
else
{
lean_object* x_397; 
x_397 = lean_ctor_get(x_355, 3);
lean_inc(x_397);
if (lean_obj_tag(x_397) == 0)
{
lean_object* x_398; uint8_t x_399; lean_object* x_400; 
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 lean_ctor_release(x_357, 2);
 lean_ctor_release(x_357, 3);
 x_398 = x_357;
} else {
 lean_dec_ref(x_357);
 x_398 = lean_box(0);
}
x_399 = 1;
if (lean_is_scalar(x_398)) {
 x_400 = lean_alloc_ctor(1, 4, 1);
} else {
 x_400 = x_398;
}
lean_ctor_set(x_400, 0, x_349);
lean_ctor_set(x_400, 1, x_350);
lean_ctor_set(x_400, 2, x_351);
lean_ctor_set(x_400, 3, x_355);
lean_ctor_set_uint8(x_400, sizeof(void*)*4, x_399);
return x_400;
}
else
{
uint8_t x_401; 
x_401 = lean_ctor_get_uint8(x_397, sizeof(void*)*4);
if (x_401 == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; uint8_t x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; uint8_t x_414; lean_object* x_415; 
x_402 = lean_ctor_get(x_355, 1);
lean_inc(x_402);
x_403 = lean_ctor_get(x_355, 2);
lean_inc(x_403);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 lean_ctor_release(x_355, 2);
 lean_ctor_release(x_355, 3);
 x_404 = x_355;
} else {
 lean_dec_ref(x_355);
 x_404 = lean_box(0);
}
x_405 = lean_ctor_get(x_397, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_397, 1);
lean_inc(x_406);
x_407 = lean_ctor_get(x_397, 2);
lean_inc(x_407);
x_408 = lean_ctor_get(x_397, 3);
lean_inc(x_408);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 lean_ctor_release(x_397, 2);
 lean_ctor_release(x_397, 3);
 x_409 = x_397;
} else {
 lean_dec_ref(x_397);
 x_409 = lean_box(0);
}
x_410 = 1;
lean_inc(x_357);
if (lean_is_scalar(x_409)) {
 x_411 = lean_alloc_ctor(1, 4, 1);
} else {
 x_411 = x_409;
}
lean_ctor_set(x_411, 0, x_349);
lean_ctor_set(x_411, 1, x_350);
lean_ctor_set(x_411, 2, x_351);
lean_ctor_set(x_411, 3, x_357);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 lean_ctor_release(x_357, 2);
 lean_ctor_release(x_357, 3);
 x_412 = x_357;
} else {
 lean_dec_ref(x_357);
 x_412 = lean_box(0);
}
lean_ctor_set_uint8(x_411, sizeof(void*)*4, x_410);
if (lean_is_scalar(x_412)) {
 x_413 = lean_alloc_ctor(1, 4, 1);
} else {
 x_413 = x_412;
}
lean_ctor_set(x_413, 0, x_405);
lean_ctor_set(x_413, 1, x_406);
lean_ctor_set(x_413, 2, x_407);
lean_ctor_set(x_413, 3, x_408);
lean_ctor_set_uint8(x_413, sizeof(void*)*4, x_410);
x_414 = 0;
if (lean_is_scalar(x_404)) {
 x_415 = lean_alloc_ctor(1, 4, 1);
} else {
 x_415 = x_404;
}
lean_ctor_set(x_415, 0, x_411);
lean_ctor_set(x_415, 1, x_402);
lean_ctor_set(x_415, 2, x_403);
lean_ctor_set(x_415, 3, x_413);
lean_ctor_set_uint8(x_415, sizeof(void*)*4, x_414);
return x_415;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; uint8_t x_426; lean_object* x_427; 
x_416 = lean_ctor_get(x_355, 1);
lean_inc(x_416);
x_417 = lean_ctor_get(x_355, 2);
lean_inc(x_417);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 lean_ctor_release(x_355, 2);
 lean_ctor_release(x_355, 3);
 x_418 = x_355;
} else {
 lean_dec_ref(x_355);
 x_418 = lean_box(0);
}
x_419 = lean_ctor_get(x_357, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_357, 1);
lean_inc(x_420);
x_421 = lean_ctor_get(x_357, 2);
lean_inc(x_421);
x_422 = lean_ctor_get(x_357, 3);
lean_inc(x_422);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 lean_ctor_release(x_357, 2);
 lean_ctor_release(x_357, 3);
 x_423 = x_357;
} else {
 lean_dec_ref(x_357);
 x_423 = lean_box(0);
}
if (lean_is_scalar(x_423)) {
 x_424 = lean_alloc_ctor(1, 4, 1);
} else {
 x_424 = x_423;
}
lean_ctor_set(x_424, 0, x_419);
lean_ctor_set(x_424, 1, x_420);
lean_ctor_set(x_424, 2, x_421);
lean_ctor_set(x_424, 3, x_422);
lean_ctor_set_uint8(x_424, sizeof(void*)*4, x_401);
if (lean_is_scalar(x_418)) {
 x_425 = lean_alloc_ctor(1, 4, 1);
} else {
 x_425 = x_418;
}
lean_ctor_set(x_425, 0, x_424);
lean_ctor_set(x_425, 1, x_416);
lean_ctor_set(x_425, 2, x_417);
lean_ctor_set(x_425, 3, x_397);
lean_ctor_set_uint8(x_425, sizeof(void*)*4, x_356);
x_426 = 1;
x_427 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_427, 0, x_349);
lean_ctor_set(x_427, 1, x_350);
lean_ctor_set(x_427, 2, x_351);
lean_ctor_set(x_427, 3, x_425);
lean_ctor_set_uint8(x_427, sizeof(void*)*4, x_426);
return x_427;
}
}
}
}
}
else
{
uint8_t x_428; lean_object* x_429; 
x_428 = 1;
x_429 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_429, 0, x_349);
lean_ctor_set(x_429, 1, x_350);
lean_ctor_set(x_429, 2, x_351);
lean_ctor_set(x_429, 3, x_355);
lean_ctor_set_uint8(x_429, sizeof(void*)*4, x_428);
return x_429;
}
}
else
{
uint8_t x_430; lean_object* x_431; lean_object* x_432; 
lean_dec(x_351);
lean_dec(x_350);
x_430 = 1;
x_431 = lean_box(x_3);
x_432 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_432, 0, x_349);
lean_ctor_set(x_432, 1, x_2);
lean_ctor_set(x_432, 2, x_431);
lean_ctor_set(x_432, 3, x_352);
lean_ctor_set_uint8(x_432, sizeof(void*)*4, x_430);
return x_432;
}
}
else
{
lean_object* x_433; uint8_t x_434; 
x_433 = l_Lean_RBNode_ins___at_Lean_Widget_ExprDiff_insertBeforeChange___spec__2(x_349, x_2, x_3);
x_434 = lean_ctor_get_uint8(x_433, sizeof(void*)*4);
if (x_434 == 0)
{
lean_object* x_435; 
x_435 = lean_ctor_get(x_433, 0);
lean_inc(x_435);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; 
x_436 = lean_ctor_get(x_433, 3);
lean_inc(x_436);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; uint8_t x_441; lean_object* x_442; 
x_437 = lean_ctor_get(x_433, 1);
lean_inc(x_437);
x_438 = lean_ctor_get(x_433, 2);
lean_inc(x_438);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 lean_ctor_release(x_433, 2);
 lean_ctor_release(x_433, 3);
 x_439 = x_433;
} else {
 lean_dec_ref(x_433);
 x_439 = lean_box(0);
}
if (lean_is_scalar(x_439)) {
 x_440 = lean_alloc_ctor(1, 4, 1);
} else {
 x_440 = x_439;
}
lean_ctor_set(x_440, 0, x_436);
lean_ctor_set(x_440, 1, x_437);
lean_ctor_set(x_440, 2, x_438);
lean_ctor_set(x_440, 3, x_436);
lean_ctor_set_uint8(x_440, sizeof(void*)*4, x_434);
x_441 = 1;
x_442 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_442, 0, x_440);
lean_ctor_set(x_442, 1, x_350);
lean_ctor_set(x_442, 2, x_351);
lean_ctor_set(x_442, 3, x_352);
lean_ctor_set_uint8(x_442, sizeof(void*)*4, x_441);
return x_442;
}
else
{
uint8_t x_443; 
x_443 = lean_ctor_get_uint8(x_436, sizeof(void*)*4);
if (x_443 == 0)
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; uint8_t x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; lean_object* x_456; 
x_444 = lean_ctor_get(x_433, 1);
lean_inc(x_444);
x_445 = lean_ctor_get(x_433, 2);
lean_inc(x_445);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 lean_ctor_release(x_433, 2);
 lean_ctor_release(x_433, 3);
 x_446 = x_433;
} else {
 lean_dec_ref(x_433);
 x_446 = lean_box(0);
}
x_447 = lean_ctor_get(x_436, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_436, 1);
lean_inc(x_448);
x_449 = lean_ctor_get(x_436, 2);
lean_inc(x_449);
x_450 = lean_ctor_get(x_436, 3);
lean_inc(x_450);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 lean_ctor_release(x_436, 1);
 lean_ctor_release(x_436, 2);
 lean_ctor_release(x_436, 3);
 x_451 = x_436;
} else {
 lean_dec_ref(x_436);
 x_451 = lean_box(0);
}
x_452 = 1;
if (lean_is_scalar(x_451)) {
 x_453 = lean_alloc_ctor(1, 4, 1);
} else {
 x_453 = x_451;
}
lean_ctor_set(x_453, 0, x_435);
lean_ctor_set(x_453, 1, x_444);
lean_ctor_set(x_453, 2, x_445);
lean_ctor_set(x_453, 3, x_447);
lean_ctor_set_uint8(x_453, sizeof(void*)*4, x_452);
if (lean_is_scalar(x_446)) {
 x_454 = lean_alloc_ctor(1, 4, 1);
} else {
 x_454 = x_446;
}
lean_ctor_set(x_454, 0, x_450);
lean_ctor_set(x_454, 1, x_350);
lean_ctor_set(x_454, 2, x_351);
lean_ctor_set(x_454, 3, x_352);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_452);
x_455 = 0;
x_456 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_456, 0, x_453);
lean_ctor_set(x_456, 1, x_448);
lean_ctor_set(x_456, 2, x_449);
lean_ctor_set(x_456, 3, x_454);
lean_ctor_set_uint8(x_456, sizeof(void*)*4, x_455);
return x_456;
}
else
{
lean_object* x_457; uint8_t x_458; lean_object* x_459; 
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 lean_ctor_release(x_436, 1);
 lean_ctor_release(x_436, 2);
 lean_ctor_release(x_436, 3);
 x_457 = x_436;
} else {
 lean_dec_ref(x_436);
 x_457 = lean_box(0);
}
x_458 = 1;
if (lean_is_scalar(x_457)) {
 x_459 = lean_alloc_ctor(1, 4, 1);
} else {
 x_459 = x_457;
}
lean_ctor_set(x_459, 0, x_433);
lean_ctor_set(x_459, 1, x_350);
lean_ctor_set(x_459, 2, x_351);
lean_ctor_set(x_459, 3, x_352);
lean_ctor_set_uint8(x_459, sizeof(void*)*4, x_458);
return x_459;
}
}
}
else
{
uint8_t x_460; 
x_460 = lean_ctor_get_uint8(x_435, sizeof(void*)*4);
if (x_460 == 0)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; uint8_t x_470; lean_object* x_471; lean_object* x_472; uint8_t x_473; lean_object* x_474; 
x_461 = lean_ctor_get(x_433, 1);
lean_inc(x_461);
x_462 = lean_ctor_get(x_433, 2);
lean_inc(x_462);
x_463 = lean_ctor_get(x_433, 3);
lean_inc(x_463);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 lean_ctor_release(x_433, 2);
 lean_ctor_release(x_433, 3);
 x_464 = x_433;
} else {
 lean_dec_ref(x_433);
 x_464 = lean_box(0);
}
x_465 = lean_ctor_get(x_435, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_435, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_435, 2);
lean_inc(x_467);
x_468 = lean_ctor_get(x_435, 3);
lean_inc(x_468);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 lean_ctor_release(x_435, 2);
 lean_ctor_release(x_435, 3);
 x_469 = x_435;
} else {
 lean_dec_ref(x_435);
 x_469 = lean_box(0);
}
x_470 = 1;
if (lean_is_scalar(x_469)) {
 x_471 = lean_alloc_ctor(1, 4, 1);
} else {
 x_471 = x_469;
}
lean_ctor_set(x_471, 0, x_465);
lean_ctor_set(x_471, 1, x_466);
lean_ctor_set(x_471, 2, x_467);
lean_ctor_set(x_471, 3, x_468);
lean_ctor_set_uint8(x_471, sizeof(void*)*4, x_470);
if (lean_is_scalar(x_464)) {
 x_472 = lean_alloc_ctor(1, 4, 1);
} else {
 x_472 = x_464;
}
lean_ctor_set(x_472, 0, x_463);
lean_ctor_set(x_472, 1, x_350);
lean_ctor_set(x_472, 2, x_351);
lean_ctor_set(x_472, 3, x_352);
lean_ctor_set_uint8(x_472, sizeof(void*)*4, x_470);
x_473 = 0;
x_474 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_474, 0, x_471);
lean_ctor_set(x_474, 1, x_461);
lean_ctor_set(x_474, 2, x_462);
lean_ctor_set(x_474, 3, x_472);
lean_ctor_set_uint8(x_474, sizeof(void*)*4, x_473);
return x_474;
}
else
{
lean_object* x_475; 
x_475 = lean_ctor_get(x_433, 3);
lean_inc(x_475);
if (lean_obj_tag(x_475) == 0)
{
lean_object* x_476; uint8_t x_477; lean_object* x_478; 
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 lean_ctor_release(x_435, 2);
 lean_ctor_release(x_435, 3);
 x_476 = x_435;
} else {
 lean_dec_ref(x_435);
 x_476 = lean_box(0);
}
x_477 = 1;
if (lean_is_scalar(x_476)) {
 x_478 = lean_alloc_ctor(1, 4, 1);
} else {
 x_478 = x_476;
}
lean_ctor_set(x_478, 0, x_433);
lean_ctor_set(x_478, 1, x_350);
lean_ctor_set(x_478, 2, x_351);
lean_ctor_set(x_478, 3, x_352);
lean_ctor_set_uint8(x_478, sizeof(void*)*4, x_477);
return x_478;
}
else
{
uint8_t x_479; 
x_479 = lean_ctor_get_uint8(x_475, sizeof(void*)*4);
if (x_479 == 0)
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; uint8_t x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; uint8_t x_492; lean_object* x_493; 
x_480 = lean_ctor_get(x_433, 1);
lean_inc(x_480);
x_481 = lean_ctor_get(x_433, 2);
lean_inc(x_481);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 lean_ctor_release(x_433, 2);
 lean_ctor_release(x_433, 3);
 x_482 = x_433;
} else {
 lean_dec_ref(x_433);
 x_482 = lean_box(0);
}
x_483 = lean_ctor_get(x_475, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_475, 1);
lean_inc(x_484);
x_485 = lean_ctor_get(x_475, 2);
lean_inc(x_485);
x_486 = lean_ctor_get(x_475, 3);
lean_inc(x_486);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 lean_ctor_release(x_475, 1);
 lean_ctor_release(x_475, 2);
 lean_ctor_release(x_475, 3);
 x_487 = x_475;
} else {
 lean_dec_ref(x_475);
 x_487 = lean_box(0);
}
x_488 = 1;
lean_inc(x_435);
if (lean_is_scalar(x_487)) {
 x_489 = lean_alloc_ctor(1, 4, 1);
} else {
 x_489 = x_487;
}
lean_ctor_set(x_489, 0, x_435);
lean_ctor_set(x_489, 1, x_480);
lean_ctor_set(x_489, 2, x_481);
lean_ctor_set(x_489, 3, x_483);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 lean_ctor_release(x_435, 2);
 lean_ctor_release(x_435, 3);
 x_490 = x_435;
} else {
 lean_dec_ref(x_435);
 x_490 = lean_box(0);
}
lean_ctor_set_uint8(x_489, sizeof(void*)*4, x_488);
if (lean_is_scalar(x_490)) {
 x_491 = lean_alloc_ctor(1, 4, 1);
} else {
 x_491 = x_490;
}
lean_ctor_set(x_491, 0, x_486);
lean_ctor_set(x_491, 1, x_350);
lean_ctor_set(x_491, 2, x_351);
lean_ctor_set(x_491, 3, x_352);
lean_ctor_set_uint8(x_491, sizeof(void*)*4, x_488);
x_492 = 0;
if (lean_is_scalar(x_482)) {
 x_493 = lean_alloc_ctor(1, 4, 1);
} else {
 x_493 = x_482;
}
lean_ctor_set(x_493, 0, x_489);
lean_ctor_set(x_493, 1, x_484);
lean_ctor_set(x_493, 2, x_485);
lean_ctor_set(x_493, 3, x_491);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_492);
return x_493;
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; lean_object* x_505; 
x_494 = lean_ctor_get(x_433, 1);
lean_inc(x_494);
x_495 = lean_ctor_get(x_433, 2);
lean_inc(x_495);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 lean_ctor_release(x_433, 2);
 lean_ctor_release(x_433, 3);
 x_496 = x_433;
} else {
 lean_dec_ref(x_433);
 x_496 = lean_box(0);
}
x_497 = lean_ctor_get(x_435, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_435, 1);
lean_inc(x_498);
x_499 = lean_ctor_get(x_435, 2);
lean_inc(x_499);
x_500 = lean_ctor_get(x_435, 3);
lean_inc(x_500);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 lean_ctor_release(x_435, 2);
 lean_ctor_release(x_435, 3);
 x_501 = x_435;
} else {
 lean_dec_ref(x_435);
 x_501 = lean_box(0);
}
if (lean_is_scalar(x_501)) {
 x_502 = lean_alloc_ctor(1, 4, 1);
} else {
 x_502 = x_501;
}
lean_ctor_set(x_502, 0, x_497);
lean_ctor_set(x_502, 1, x_498);
lean_ctor_set(x_502, 2, x_499);
lean_ctor_set(x_502, 3, x_500);
lean_ctor_set_uint8(x_502, sizeof(void*)*4, x_479);
if (lean_is_scalar(x_496)) {
 x_503 = lean_alloc_ctor(1, 4, 1);
} else {
 x_503 = x_496;
}
lean_ctor_set(x_503, 0, x_502);
lean_ctor_set(x_503, 1, x_494);
lean_ctor_set(x_503, 2, x_495);
lean_ctor_set(x_503, 3, x_475);
lean_ctor_set_uint8(x_503, sizeof(void*)*4, x_434);
x_504 = 1;
x_505 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_505, 0, x_503);
lean_ctor_set(x_505, 1, x_350);
lean_ctor_set(x_505, 2, x_351);
lean_ctor_set(x_505, 3, x_352);
lean_ctor_set_uint8(x_505, sizeof(void*)*4, x_504);
return x_505;
}
}
}
}
}
else
{
uint8_t x_506; lean_object* x_507; 
x_506 = 1;
x_507 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_507, 0, x_433);
lean_ctor_set(x_507, 1, x_350);
lean_ctor_set(x_507, 2, x_351);
lean_ctor_set(x_507, 3, x_352);
lean_ctor_set_uint8(x_507, sizeof(void*)*4, x_506);
return x_507;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lean_Widget_ExprDiff_insertBeforeChange___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at_Lean_Widget_ExprDiff_insertBeforeChange___spec__2(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_RBNode_ins___at_Lean_Widget_ExprDiff_insertBeforeChange___spec__2(x_1, x_2, x_3);
x_7 = l_Lean_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_ExprDiff_insertBeforeChange(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_RBNode_insert___at_Lean_Widget_ExprDiff_insertBeforeChange___spec__1(x_5, x_1, x_2);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = l_Lean_RBNode_insert___at_Lean_Widget_ExprDiff_insertBeforeChange___spec__1(x_7, x_1, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Widget_ExprDiff_insertBeforeChange___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_RBNode_ins___at_Lean_Widget_ExprDiff_insertBeforeChange___spec__2(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lean_Widget_ExprDiff_insertBeforeChange___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_RBNode_insert___at_Lean_Widget_ExprDiff_insertBeforeChange___spec__1(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_ExprDiff_insertBeforeChange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Widget_ExprDiff_insertBeforeChange(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_ExprDiff_insertAfterChange(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_RBNode_insert___at_Lean_Widget_ExprDiff_insertBeforeChange___spec__1(x_5, x_1, x_2);
lean_ctor_set(x_3, 1, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = l_Lean_RBNode_insert___at_Lean_Widget_ExprDiff_insertBeforeChange___spec__1(x_8, x_1, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_ExprDiff_insertAfterChange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Widget_ExprDiff_insertAfterChange(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_ExprDiff_withChangePos(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = l_Lean_RBNode_insert___at_Lean_Widget_ExprDiff_insertBeforeChange___spec__1(x_4, x_1, x_3);
x_6 = l_Lean_RBNode_insert___at_Lean_Widget_ExprDiff_insertBeforeChange___spec__1(x_4, x_2, x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_ExprDiff_withChangePos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Widget_ExprDiff_withChangePos(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_ExprDiff_withChange(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Widget_ExprDiff_withChangePos(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_ExprDiff_withChange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Widget_ExprDiff_withChange(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_ExprDiff_isEmpty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_ExprDiff_isEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Widget_ExprDiff_isEmpty(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___at_Lean_Widget_exprDiffCore_piDiff___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_name_eq(x_5, x_7);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
x_10 = lean_box(0);
return x_10;
}
else
{
x_1 = x_6;
x_2 = x_8;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f___at_Lean_Widget_exprDiffCore_piDiff___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_List_reverse___rarg(x_1);
x_4 = l_List_reverse___rarg(x_2);
x_5 = l_List_isPrefixOf_x3f___at_Lean_Widget_exprDiffCore_piDiff___spec__2(x_3, x_4);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = l_List_reverse___rarg(x_8);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = l_List_reverse___rarg(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Widget_exprDiffCore_piDiff___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_2, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_2, x_15);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_3);
x_18 = l_Lean_SubExpr_Pos_pushNthBindingDomain(x_3, x_17);
x_19 = 1;
x_20 = l_Lean_Widget_ExprDiff_insertBeforeChange(x_18, x_19, x_6);
x_21 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_2 = x_16;
x_3 = x_21;
x_6 = x_20;
goto _start;
}
else
{
lean_object* x_23; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_11);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_6);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Widget_exprDiffCore_piDiff___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_8 = l_List_reverse___rarg(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_13 = l_Lean_Meta_getFVarFromUserName(x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_14);
{
lean_object* _tmp_0 = x_12;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_6 = x_15;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_7 = _tmp_6;
}
goto _start;
}
else
{
uint8_t x_17; 
lean_free_object(x_1);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
lean_inc(x_3);
x_23 = l_Lean_Meta_getFVarFromUserName(x_21, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_2);
x_1 = x_22;
x_2 = x_26;
x_7 = x_25;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_30 = x_23;
} else {
 lean_dec_ref(x_23);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiffCore_piDiff___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = 0;
x_10 = l_Lean_Widget_ExprDiff_withChange(x_1, x_2, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiffCore_piDiff___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_40; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_List_lengthTRAux___rarg(x_1, x_11);
lean_inc(x_12);
x_13 = l_Lean_Expr_getForallBodyMaxDepth(x_12, x_2);
x_14 = lean_box(0);
x_24 = l_Lean_Meta_saveState___rarg(x_7, x_8, x_9, x_10);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
lean_inc(x_6);
x_40 = l_List_mapM_loop___at_Lean_Widget_exprDiffCore_piDiff___spec__4(x_1, x_14, x_6, x_7, x_8, x_9, x_26);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_List_redLength___rarg(x_41);
x_44 = lean_mk_empty_array_with_capacity(x_43);
lean_dec(x_43);
x_45 = l_List_toArrayAux___rarg(x_41, x_44);
x_46 = lean_expr_instantiate_rev(x_13, x_45);
lean_dec(x_45);
lean_dec(x_13);
x_47 = lean_ctor_get(x_3, 1);
lean_inc(x_47);
lean_inc(x_12);
x_48 = l_Lean_SubExpr_Pos_pushNthBindingBody(x_12, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_50 = l_Lean_Widget_exprDiffCore(x_49, x_4, x_6, x_7, x_8, x_9, x_42);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_27);
lean_dec(x_25);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_15 = x_51;
x_16 = x_52;
goto block_23;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_28 = x_53;
x_29 = x_54;
goto block_39;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_13);
lean_dec(x_4);
x_55 = lean_ctor_get(x_40, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_40, 1);
lean_inc(x_56);
lean_dec(x_40);
x_28 = x_55;
x_29 = x_56;
goto block_39;
}
block_23:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(1u);
lean_inc(x_12);
x_18 = l_Std_Range_forIn_loop___at_Lean_Widget_exprDiffCore_piDiff___spec__3(x_3, x_12, x_11, x_12, x_17, x_15, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
block_39:
{
uint8_t x_30; 
x_30 = l_Lean_Exception_isRuntime(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_28);
lean_dec(x_27);
x_31 = l_Lean_Meta_SavedState_restore(x_25, x_6, x_7, x_8, x_9, x_29);
lean_dec(x_25);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_Widget_instEmptyCollectionExprDiff___closed__1;
x_15 = x_33;
x_16 = x_32;
goto block_23;
}
else
{
uint8_t x_34; 
x_34 = lean_ctor_get_uint8(x_8, sizeof(void*)*11);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
if (lean_is_scalar(x_27)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_27;
 lean_ctor_set_tag(x_35, 1);
}
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_29);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_28);
lean_dec(x_27);
x_36 = l_Lean_Meta_SavedState_restore(x_25, x_6, x_7, x_8, x_9, x_29);
lean_dec(x_25);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lean_Widget_instEmptyCollectionExprDiff___closed__1;
x_15 = x_38;
x_16 = x_37;
goto block_23;
}
}
}
}
}
static lean_object* _init_l_Lean_Widget_exprDiffCore_piDiff___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("should not happen", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Widget_exprDiffCore_piDiff___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Widget_exprDiffCore_piDiff___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiffCore_piDiff___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = l_Lean_Expr_getForallBinderNames(x_10);
lean_dec(x_10);
x_12 = l_Lean_Expr_getForallBinderNames(x_3);
x_13 = l_List_isSuffixOf_x3f___at_Lean_Widget_exprDiffCore_piDiff___spec__1(x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = l_Lean_Widget_exprDiffCore_piDiff___lambda__1(x_1, x_2, x_14, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_List_lengthTRAux___rarg(x_16, x_17);
x_19 = lean_nat_dec_eq(x_18, x_17);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l_Lean_Widget_exprDiffCore_piDiff___lambda__2(x_16, x_3, x_1, x_2, x_20, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_16);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = l_Lean_Widget_exprDiffCore_piDiff___lambda__3___closed__2;
x_23 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_22, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiffCore_piDiff___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_expr_instantiate1(x_1, x_5);
lean_dec(x_1);
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_SubExpr_Pos_push(x_2, x_12);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_expr_instantiate1(x_3, x_5);
lean_dec(x_5);
lean_dec(x_3);
x_16 = l_Lean_SubExpr_Pos_push(x_4, x_12);
lean_dec(x_4);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Widget_exprDiffCore(x_14, x_17, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiffCore_piDiff(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 7)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 7)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 2);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_9, 2);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 8);
lean_dec(x_9);
x_18 = lean_name_eq(x_10, x_14);
lean_dec(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_19 = lean_box(0);
x_20 = l_Lean_Widget_exprDiffCore_piDiff___lambda__3(x_1, x_2, x_8, x_19, x_3, x_4, x_5, x_6, x_7);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_13, x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_22 = lean_box(0);
x_23 = l_Lean_Widget_exprDiffCore_piDiff___lambda__3(x_1, x_2, x_8, x_22, x_3, x_4, x_5, x_6, x_7);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_8);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_SubExpr_Pos_push(x_24, x_25);
lean_inc(x_11);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_11);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
lean_dec(x_2);
x_29 = l_Lean_SubExpr_Pos_push(x_28, x_25);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_15);
lean_ctor_set(x_30, 1, x_29);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_31 = l_Lean_Widget_exprDiffCore(x_27, x_30, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = l_Lean_Widget_ExprDiff_isEmpty(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_36 = lean_unsigned_to_nat(1u);
x_37 = l_Lean_SubExpr_Pos_push(x_24, x_36);
lean_dec(x_24);
x_38 = l_Lean_SubExpr_Pos_push(x_28, x_36);
lean_dec(x_28);
x_39 = 0;
x_40 = l_Lean_Widget_ExprDiff_withChangePos(x_37, x_38, x_39);
x_41 = lean_ctor_get(x_33, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = l_Lean_Widget_instAppendExprDiff___closed__1;
x_44 = l_Lean_Widget_instAppendExprDiff___closed__2;
x_45 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_43, x_44, x_41, x_42);
x_46 = lean_ctor_get(x_33, 1);
lean_inc(x_46);
lean_dec(x_33);
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
lean_dec(x_40);
x_48 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_43, x_44, x_46, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_31, 0, x_49);
return x_31;
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
lean_free_object(x_31);
lean_dec(x_33);
x_50 = lean_alloc_closure((void*)(l_Lean_Widget_exprDiffCore_piDiff___lambda__4), 10, 4);
lean_closure_set(x_50, 0, x_12);
lean_closure_set(x_50, 1, x_24);
lean_closure_set(x_50, 2, x_16);
lean_closure_set(x_50, 3, x_28);
x_51 = 0;
x_52 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(x_10, x_13, x_11, x_50, x_51, x_3, x_4, x_5, x_6, x_34);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
return x_52;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_52);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
return x_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_52, 0);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_52);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_31, 0);
x_62 = lean_ctor_get(x_31, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_31);
x_63 = l_Lean_Widget_ExprDiff_isEmpty(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_64 = lean_unsigned_to_nat(1u);
x_65 = l_Lean_SubExpr_Pos_push(x_24, x_64);
lean_dec(x_24);
x_66 = l_Lean_SubExpr_Pos_push(x_28, x_64);
lean_dec(x_28);
x_67 = 0;
x_68 = l_Lean_Widget_ExprDiff_withChangePos(x_65, x_66, x_67);
x_69 = lean_ctor_get(x_61, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
x_71 = l_Lean_Widget_instAppendExprDiff___closed__1;
x_72 = l_Lean_Widget_instAppendExprDiff___closed__2;
x_73 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_71, x_72, x_69, x_70);
x_74 = lean_ctor_get(x_61, 1);
lean_inc(x_74);
lean_dec(x_61);
x_75 = lean_ctor_get(x_68, 1);
lean_inc(x_75);
lean_dec(x_68);
x_76 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_71, x_72, x_74, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_62);
return x_78;
}
else
{
lean_object* x_79; uint8_t x_80; lean_object* x_81; 
lean_dec(x_61);
x_79 = lean_alloc_closure((void*)(l_Lean_Widget_exprDiffCore_piDiff___lambda__4), 10, 4);
lean_closure_set(x_79, 0, x_12);
lean_closure_set(x_79, 1, x_24);
lean_closure_set(x_79, 2, x_16);
lean_closure_set(x_79, 3, x_28);
x_80 = 0;
x_81 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(x_10, x_13, x_11, x_79, x_80, x_3, x_4, x_5, x_6, x_62);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_81, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_88 = x_81;
} else {
 lean_dec_ref(x_81);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_90 = !lean_is_exclusive(x_31);
if (x_90 == 0)
{
return x_31;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_31, 0);
x_92 = lean_ctor_get(x_31, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_31);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_9);
x_94 = lean_box(0);
x_95 = l_Lean_Widget_exprDiffCore_piDiff___lambda__3(x_1, x_2, x_8, x_94, x_3, x_4, x_5, x_6, x_7);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = l_Lean_Widget_instEmptyCollectionExprDiff___closed__1;
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_7);
return x_97;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Widget_exprDiffCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_array_set(x_2, x_3, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_1 = x_4;
x_2 = x_6;
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Widget_exprDiffCore___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_6, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_6, x_17);
lean_dec(x_6);
x_19 = lean_array_fget(x_5, x_7);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_array_get_size(x_3);
x_23 = lean_ctor_get(x_1, 1);
x_24 = l_Lean_SubExpr_Pos_pushNaryArg(x_22, x_7, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_ctor_get(x_2, 1);
x_27 = l_Lean_SubExpr_Pos_pushNaryArg(x_22, x_7, x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_27);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_29 = l_Lean_Widget_exprDiffCore(x_25, x_28, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_nat_add(x_7, x_17);
lean_dec(x_7);
x_33 = lean_array_push(x_9, x_30);
x_6 = x_18;
x_7 = x_32;
x_8 = lean_box(0);
x_9 = x_33;
x_14 = x_31;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
return x_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_29, 0);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_29);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_9);
lean_ctor_set(x_39, 1, x_14);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Widget_exprDiffCore___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = l_Lean_Widget_instAppendExprDiff___closed__1;
x_10 = l_Lean_Widget_instAppendExprDiff___closed__2;
x_11 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_9, x_10, x_7, x_8);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_9, x_10, x_12, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_2 = x_17;
x_4 = x_15;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiffCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_Array_zip___rarg(x_1, x_2);
x_12 = lean_array_get_size(x_11);
x_13 = lean_mk_empty_array_with_capacity(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Array_mapIdxM_map___at_Lean_Widget_exprDiffCore___spec__2(x_3, x_4, x_1, x_11, x_11, x_12, x_14, lean_box(0), x_13, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_array_get_size(x_17);
x_19 = lean_nat_dec_lt(x_14, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_18);
lean_dec(x_17);
x_20 = l_Lean_Widget_instEmptyCollectionExprDiff___closed__1;
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_18, x_18);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_17);
x_22 = l_Lean_Widget_instEmptyCollectionExprDiff___closed__1;
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_23 = 0;
x_24 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_25 = l_Lean_Widget_instEmptyCollectionExprDiff___closed__1;
x_26 = l_Array_foldlMUnsafe_fold___at_Lean_Widget_exprDiffCore___spec__3(x_17, x_23, x_24, x_25);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_26);
return x_15;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
x_29 = lean_array_get_size(x_27);
x_30 = lean_nat_dec_lt(x_14, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_29);
lean_dec(x_27);
x_31 = l_Lean_Widget_instEmptyCollectionExprDiff___closed__1;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_29, x_29);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_29);
lean_dec(x_27);
x_34 = l_Lean_Widget_instEmptyCollectionExprDiff___closed__1;
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_28);
return x_35;
}
else
{
size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = 0;
x_37 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_38 = l_Lean_Widget_instEmptyCollectionExprDiff___closed__1;
x_39 = l_Array_foldlMUnsafe_fold___at_Lean_Widget_exprDiffCore___spec__3(x_27, x_36, x_37, x_38);
lean_dec(x_27);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_28);
return x_40;
}
}
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_15);
if (x_41 == 0)
{
return x_15;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_15, 0);
x_43 = lean_ctor_get(x_15, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_15);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiffCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_SubExpr_Pos_push(x_13, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_ctor_get(x_3, 1);
x_18 = l_Lean_SubExpr_Pos_push(x_17, x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_20 = l_Lean_Widget_exprDiffCore(x_16, x_19, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = l_Lean_Widget_ExprDiff_isEmpty(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_25 = lean_unsigned_to_nat(1u);
x_26 = l_Lean_SubExpr_Pos_push(x_13, x_25);
x_27 = l_Lean_SubExpr_Pos_push(x_17, x_25);
x_28 = 0;
x_29 = l_Lean_Widget_ExprDiff_withChangePos(x_26, x_27, x_28);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = l_Lean_Widget_instAppendExprDiff___closed__1;
x_33 = l_Lean_Widget_instAppendExprDiff___closed__2;
x_34 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_32, x_33, x_30, x_31);
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_dec(x_22);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_dec(x_29);
x_37 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_32, x_33, x_35, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_20, 0, x_38);
return x_20;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_free_object(x_20);
lean_dec(x_22);
x_39 = lean_unsigned_to_nat(1u);
x_40 = l_Lean_SubExpr_Pos_push(x_13, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_5);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_SubExpr_Pos_push(x_17, x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_6);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Widget_exprDiffCore(x_41, x_43, x_8, x_9, x_10, x_11, x_23);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
return x_44;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_44);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_44);
if (x_49 == 0)
{
return x_44;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_44, 0);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_44);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_20, 0);
x_54 = lean_ctor_get(x_20, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_20);
x_55 = l_Lean_Widget_ExprDiff_isEmpty(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_56 = lean_unsigned_to_nat(1u);
x_57 = l_Lean_SubExpr_Pos_push(x_13, x_56);
x_58 = l_Lean_SubExpr_Pos_push(x_17, x_56);
x_59 = 0;
x_60 = l_Lean_Widget_ExprDiff_withChangePos(x_57, x_58, x_59);
x_61 = lean_ctor_get(x_53, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = l_Lean_Widget_instAppendExprDiff___closed__1;
x_64 = l_Lean_Widget_instAppendExprDiff___closed__2;
x_65 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_63, x_64, x_61, x_62);
x_66 = lean_ctor_get(x_53, 1);
lean_inc(x_66);
lean_dec(x_53);
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_dec(x_60);
x_68 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_63, x_64, x_66, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_54);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_53);
x_71 = lean_unsigned_to_nat(1u);
x_72 = l_Lean_SubExpr_Pos_push(x_13, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_5);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_SubExpr_Pos_push(x_17, x_71);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_6);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_Widget_exprDiffCore(x_73, x_75, x_8, x_9, x_10, x_11, x_54);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_76, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_83 = x_76;
} else {
 lean_dec_ref(x_76);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_85 = !lean_is_exclusive(x_20);
if (x_85 == 0)
{
return x_20;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_20, 0);
x_87 = lean_ctor_get(x_20, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_20);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
static lean_object* _init_l_Lean_Widget_exprDiffCore___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiffCore___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
switch (lean_obj_tag(x_9)) {
case 5:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
switch (lean_obj_tag(x_10)) {
case 5:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_10, x_11);
x_13 = l_Lean_Widget_exprDiffCore___lambda__3___closed__1;
lean_inc(x_12);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_12, x_15);
lean_dec(x_12);
x_17 = l_Lean_Expr_withAppAux___at_Lean_Widget_exprDiffCore___spec__1(x_10, x_14, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_9, x_11);
lean_inc(x_20);
x_21 = lean_mk_array(x_20, x_13);
x_22 = lean_nat_sub(x_20, x_15);
lean_dec(x_20);
x_23 = l_Lean_Expr_withAppAux___at_Lean_Widget_exprDiffCore___spec__1(x_9, x_21, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_expr_eqv(x_18, x_24);
lean_dec(x_24);
lean_dec(x_18);
if (x_26 == 0)
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_25);
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_27 = 0;
x_28 = l_Lean_Widget_ExprDiff_withChange(x_1, x_2, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_8);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_array_get_size(x_19);
x_31 = lean_array_get_size(x_25);
x_32 = lean_nat_dec_eq(x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
if (x_32 == 0)
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_25);
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_33 = 0;
x_34 = l_Lean_Widget_ExprDiff_withChange(x_1, x_2, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_8);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_box(0);
x_37 = l_Lean_Widget_exprDiffCore___lambda__1(x_19, x_25, x_1, x_2, x_36, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
lean_dec(x_25);
lean_dec(x_19);
return x_37;
}
}
}
case 10:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_9);
x_38 = lean_ctor_get(x_10, 1);
lean_inc(x_38);
lean_dec(x_10);
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
lean_dec(x_2);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Widget_exprDiffCore(x_1, x_40, x_4, x_5, x_6, x_7, x_8);
return x_41;
}
default: 
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_42 = 0;
x_43 = l_Lean_Widget_ExprDiff_withChange(x_1, x_2, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_8);
return x_44;
}
}
}
case 6:
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_2, 0);
lean_inc(x_45);
switch (lean_obj_tag(x_45)) {
case 6:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_54; 
x_46 = lean_ctor_get(x_9, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_9, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_9, 2);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 8);
lean_dec(x_9);
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_45, 2);
lean_inc(x_52);
x_53 = lean_ctor_get_uint8(x_45, sizeof(void*)*3 + 8);
lean_dec(x_45);
x_54 = lean_name_eq(x_46, x_50);
lean_dec(x_50);
lean_dec(x_46);
if (x_54 == 0)
{
uint8_t x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_55 = 0;
x_56 = l_Lean_Widget_ExprDiff_withChange(x_1, x_2, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_8);
return x_57;
}
else
{
uint8_t x_58; 
x_58 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_49, x_53);
if (x_58 == 0)
{
uint8_t x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_59 = 0;
x_60 = l_Lean_Widget_ExprDiff_withChange(x_1, x_2, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_8);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_box(0);
x_63 = l_Lean_Widget_exprDiffCore___lambda__2(x_1, x_47, x_2, x_51, x_48, x_52, x_62, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_63;
}
}
}
case 10:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_9);
x_64 = lean_ctor_get(x_45, 1);
lean_inc(x_64);
lean_dec(x_45);
x_65 = lean_ctor_get(x_2, 1);
lean_inc(x_65);
lean_dec(x_2);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_Widget_exprDiffCore(x_1, x_66, x_4, x_5, x_6, x_7, x_8);
return x_67;
}
default: 
{
uint8_t x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_45);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_68 = 0;
x_69 = l_Lean_Widget_ExprDiff_withChange(x_1, x_2, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_8);
return x_70;
}
}
}
case 7:
{
lean_object* x_71; 
lean_dec(x_9);
x_71 = lean_ctor_get(x_2, 0);
lean_inc(x_71);
if (lean_obj_tag(x_71) == 10)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_ctor_get(x_2, 1);
lean_inc(x_73);
lean_dec(x_2);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_Widget_exprDiffCore(x_1, x_74, x_4, x_5, x_6, x_7, x_8);
return x_75;
}
else
{
lean_object* x_76; 
lean_dec(x_71);
x_76 = l_Lean_Widget_exprDiffCore_piDiff(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
return x_76;
}
}
case 10:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_9, 1);
lean_inc(x_77);
lean_dec(x_9);
x_78 = lean_ctor_get(x_1, 1);
lean_inc(x_78);
lean_dec(x_1);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_Widget_exprDiffCore(x_79, x_2, x_4, x_5, x_6, x_7, x_8);
return x_80;
}
case 11:
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_2, 0);
lean_inc(x_81);
switch (lean_obj_tag(x_81)) {
case 10:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_9);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_ctor_get(x_2, 1);
lean_inc(x_83);
lean_dec(x_2);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_Widget_exprDiffCore(x_1, x_84, x_4, x_5, x_6, x_7, x_8);
return x_85;
}
case 11:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_86 = lean_ctor_get(x_9, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_9, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_9, 2);
lean_inc(x_88);
lean_dec(x_9);
x_89 = lean_ctor_get(x_81, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_81, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_81, 2);
lean_inc(x_91);
lean_dec(x_81);
x_92 = lean_name_eq(x_86, x_89);
lean_dec(x_89);
lean_dec(x_86);
if (x_92 == 0)
{
uint8_t x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_93 = 0;
x_94 = l_Lean_Widget_ExprDiff_withChange(x_1, x_2, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_8);
return x_95;
}
else
{
uint8_t x_96; 
x_96 = lean_nat_dec_eq(x_87, x_90);
lean_dec(x_90);
lean_dec(x_87);
if (x_96 == 0)
{
uint8_t x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_91);
lean_dec(x_88);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_97 = 0;
x_98 = l_Lean_Widget_ExprDiff_withChange(x_1, x_2, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_8);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_100 = lean_ctor_get(x_1, 1);
lean_inc(x_100);
lean_dec(x_1);
x_101 = lean_unsigned_to_nat(0u);
x_102 = l_Lean_SubExpr_Pos_push(x_100, x_101);
lean_dec(x_100);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_88);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_ctor_get(x_2, 1);
lean_inc(x_104);
lean_dec(x_2);
x_105 = l_Lean_SubExpr_Pos_push(x_104, x_101);
lean_dec(x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_91);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_Widget_exprDiffCore(x_103, x_106, x_4, x_5, x_6, x_7, x_8);
return x_107;
}
}
}
default: 
{
uint8_t x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_81);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_108 = 0;
x_109 = l_Lean_Widget_ExprDiff_withChange(x_1, x_2, x_108);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_8);
return x_110;
}
}
}
default: 
{
lean_object* x_111; 
lean_dec(x_9);
x_111 = lean_ctor_get(x_2, 0);
lean_inc(x_111);
if (lean_obj_tag(x_111) == 10)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_ctor_get(x_2, 1);
lean_inc(x_113);
lean_dec(x_2);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Lean_Widget_exprDiffCore(x_1, x_114, x_4, x_5, x_6, x_7, x_8);
return x_115;
}
else
{
uint8_t x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_111);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_116 = 0;
x_117 = l_Lean_Widget_ExprDiff_withChange(x_1, x_2, x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_8);
return x_118;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiffCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_expr_eqv(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Widget_exprDiffCore___lambda__3(x_1, x_2, x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Widget_instEmptyCollectionExprDiff___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___at_Lean_Widget_exprDiffCore_piDiff___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_isPrefixOf_x3f___at_Lean_Widget_exprDiffCore_piDiff___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Widget_exprDiffCore_piDiff___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Widget_exprDiffCore_piDiff___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Widget_exprDiffCore_piDiff___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_mapM_loop___at_Lean_Widget_exprDiffCore_piDiff___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiffCore_piDiff___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Widget_exprDiffCore_piDiff___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiffCore_piDiff___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Widget_exprDiffCore_piDiff___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Widget_exprDiffCore___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_mapIdxM_map___at_Lean_Widget_exprDiffCore___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Widget_exprDiffCore___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Widget_exprDiffCore___spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiffCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Widget_exprDiffCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiffCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Widget_exprDiffCore___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiff(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_SubExpr_Pos_root;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_9);
if (x_3 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Widget_exprDiffCore(x_11, x_10, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = l_Lean_Widget_exprDiffCore(x_10, x_11, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_exprDiff___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Widget_exprDiff(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Widget_addDiffTags___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_nat_dec_lt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_nat_dec_eq(x_2, x_5);
if (x_9 == 0)
{
x_1 = x_7;
goto _start;
}
else
{
lean_object* x_11; 
lean_inc(x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_6);
return x_11;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Widget_addDiffTags___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_array_uget(x_4, x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_4, x_3, x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_15 = l_Lean_Widget_TaggedText_mapM___at_Lean_Widget_addDiffTags___spec__3(x_1, x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_20 = lean_array_uset(x_14, x_3, x_16);
x_3 = x_19;
x_4 = x_20;
x_9 = x_17;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at_Lean_Widget_addDiffTags___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
case 1:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_array_get_size(x_14);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
x_18 = l_Array_mapMUnsafe_map___at_Lean_Widget_addDiffTags___spec__4(x_1, x_16, x_17, x_14, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_ctor_set(x_2, 0, x_20);
lean_ctor_set(x_18, 0, x_2);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_18);
lean_ctor_set(x_2, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_free_object(x_2);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
lean_dec(x_2);
x_29 = lean_array_get_size(x_28);
x_30 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_31 = 0;
x_32 = l_Array_mapMUnsafe_map___at_Lean_Widget_addDiffTags___spec__4(x_1, x_30, x_31, x_28, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_33);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_40 = x_32;
} else {
 lean_dec_ref(x_32);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
default: 
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_2);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_2, 0);
x_44 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_45 = lean_apply_6(x_1, x_43, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Widget_TaggedText_mapM___at_Lean_Widget_addDiffTags___spec__3(x_1, x_44, x_3, x_4, x_5, x_6, x_47);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_ctor_set(x_2, 1, x_50);
lean_ctor_set(x_2, 0, x_46);
lean_ctor_set(x_48, 0, x_2);
return x_48;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_48, 0);
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_48);
lean_ctor_set(x_2, 1, x_51);
lean_ctor_set(x_2, 0, x_46);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_2);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_46);
lean_free_object(x_2);
x_54 = !lean_is_exclusive(x_48);
if (x_54 == 0)
{
return x_48;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_48, 0);
x_56 = lean_ctor_get(x_48, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_48);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_free_object(x_2);
lean_dec(x_44);
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
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_2, 0);
x_63 = lean_ctor_get(x_2, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_64 = lean_apply_6(x_1, x_62, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_Lean_Widget_TaggedText_mapM___at_Lean_Widget_addDiffTags___spec__3(x_1, x_63, x_3, x_4, x_5, x_6, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_70 = x_67;
} else {
 lean_dec_ref(x_67);
 x_70 = lean_box(0);
}
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_68);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_65);
x_73 = lean_ctor_get(x_67, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_67, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_75 = x_67;
} else {
 lean_dec_ref(x_67);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_63);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_77 = lean_ctor_get(x_64, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_64, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_79 = x_64;
} else {
 lean_dec_ref(x_64);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at_Lean_Widget_addDiffTags___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = l_Lean_RBNode_find___at_Lean_Widget_addDiffTags___spec__2(x_1, x_9);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_apply_7(x_2, x_3, x_12, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at_Lean_Widget_addDiffTags___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Widget_CodeWithInfos_mergePosMap___at_Lean_Widget_addDiffTags___spec__1___lambda__1___boxed), 8, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_1);
x_11 = l_Lean_Widget_TaggedText_mapM___at_Lean_Widget_addDiffTags___spec__3(x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addDiffTags___lambda__1(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Widget_ExprDiffTag_toDiffTag(x_1, x_3);
x_10 = l_Lean_Widget_SubexprInfo_withDiffTag(x_9, x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addDiffTags(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Widget_addDiffTags___lambda__1___boxed), 8, 1);
lean_closure_set(x_10, 0, x_9);
if (x_1 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = l_Lean_Widget_CodeWithInfos_mergePosMap___at_Lean_Widget_addDiffTags___spec__1(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_Widget_CodeWithInfos_mergePosMap___at_Lean_Widget_addDiffTags___spec__1(x_10, x_13, x_3, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Widget_addDiffTags___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_Widget_addDiffTags___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Widget_addDiffTags___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Widget_addDiffTags___spec__4(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at_Lean_Widget_addDiffTags___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Widget_CodeWithInfos_mergePosMap___at_Lean_Widget_addDiffTags___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addDiffTags___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Widget_addDiffTags___lambda__1(x_9, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addDiffTags___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Widget_addDiffTags(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Widget_diffHypothesesBundle_withTypeDiff___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
static lean_object* _init_l_Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("internal error: empty fvar list!", 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_diffHypothesesBundle_withTypeDiff(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_60 = lean_array_get_size(x_9);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_nat_dec_lt(x_61, x_60);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_box(0);
x_10 = x_63;
goto block_59;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_array_fget(x_9, x_61);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_10 = x_65;
goto block_59;
}
block_59:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_11 = l_Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__2;
x_12 = l_Lean_throwError___at_Lean_Widget_diffHypothesesBundle_withTypeDiff___spec__1(x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_Expr_fvar___override(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = lean_infer_type(x_14, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_Widget_exprDiff(x_2, x_16, x_1, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_3, 2);
lean_inc(x_21);
x_22 = l_Lean_Widget_addDiffTags(x_1, x_19, x_21, x_4, x_5, x_6, x_7, x_20);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_3, 2);
lean_dec(x_26);
x_27 = lean_ctor_get(x_3, 1);
lean_dec(x_27);
lean_ctor_set(x_3, 2, x_25);
lean_ctor_set(x_22, 0, x_3);
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_3, 0);
x_30 = lean_ctor_get(x_3, 3);
x_31 = lean_ctor_get(x_3, 4);
x_32 = lean_ctor_get(x_3, 5);
x_33 = lean_ctor_get(x_3, 6);
x_34 = lean_ctor_get(x_3, 7);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_3);
x_35 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_9);
lean_ctor_set(x_35, 2, x_28);
lean_ctor_set(x_35, 3, x_30);
lean_ctor_set(x_35, 4, x_31);
lean_ctor_set(x_35, 5, x_32);
lean_ctor_set(x_35, 6, x_33);
lean_ctor_set(x_35, 7, x_34);
lean_ctor_set(x_22, 0, x_35);
return x_22;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_36 = lean_ctor_get(x_22, 0);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_22);
x_38 = lean_ctor_get(x_3, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_3, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_3, 4);
lean_inc(x_40);
x_41 = lean_ctor_get(x_3, 5);
lean_inc(x_41);
x_42 = lean_ctor_get(x_3, 6);
lean_inc(x_42);
x_43 = lean_ctor_get(x_3, 7);
lean_inc(x_43);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 x_44 = x_3;
} else {
 lean_dec_ref(x_3);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 8, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_9);
lean_ctor_set(x_45, 2, x_36);
lean_ctor_set(x_45, 3, x_39);
lean_ctor_set(x_45, 4, x_40);
lean_ctor_set(x_45, 5, x_41);
lean_ctor_set(x_45, 6, x_42);
lean_ctor_set(x_45, 7, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_37);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_9);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_22);
if (x_47 == 0)
{
return x_22;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_22, 0);
x_49 = lean_ctor_get(x_22, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_22);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_18);
if (x_51 == 0)
{
return x_18;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_18, 0);
x_53 = lean_ctor_get(x_18, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_18);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_15);
if (x_55 == 0)
{
return x_15;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_15, 0);
x_57 = lean_ctor_get(x_15, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_15);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Widget_diffHypothesesBundle_withTypeDiff___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Widget_diffHypothesesBundle_withTypeDiff___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_diffHypothesesBundle_withTypeDiff___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Widget_diffHypothesesBundle_withTypeDiff(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Widget_diffHypothesesBundle___spec__1___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Widget_diffHypothesesBundle___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_9, x_8);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_10);
x_18 = lean_array_uget(x_7, x_9);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_2);
x_21 = l_Lean_LocalContext_contains(x_2, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_6);
x_22 = lean_box(0);
x_23 = l_Lean_Name_str___override(x_22, x_19);
x_24 = l_Lean_LocalContext_findFromUserName_x3f(x_2, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
if (x_1 == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_3);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_3, 7);
lean_dec(x_26);
x_27 = lean_ctor_get(x_3, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_3, 0);
lean_dec(x_28);
x_29 = l_Array_forInUnsafe_loop___at_Lean_Widget_diffHypothesesBundle___spec__1___closed__1;
lean_ctor_set(x_3, 7, x_29);
lean_ctor_set(x_3, 1, x_5);
lean_ctor_set(x_3, 0, x_4);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_3);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_15);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_ctor_get(x_3, 2);
x_35 = lean_ctor_get(x_3, 3);
x_36 = lean_ctor_get(x_3, 4);
x_37 = lean_ctor_get(x_3, 5);
x_38 = lean_ctor_get(x_3, 6);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_3);
x_39 = l_Array_forInUnsafe_loop___at_Lean_Widget_diffHypothesesBundle___spec__1___closed__1;
x_40 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_5);
lean_ctor_set(x_40, 2, x_34);
lean_ctor_set(x_40, 3, x_35);
lean_ctor_set(x_40, 4, x_36);
lean_ctor_set(x_40, 5, x_37);
lean_ctor_set(x_40, 6, x_38);
lean_ctor_set(x_40, 7, x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_15);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_3);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_3, 6);
lean_dec(x_46);
x_47 = lean_ctor_get(x_3, 1);
lean_dec(x_47);
x_48 = lean_ctor_get(x_3, 0);
lean_dec(x_48);
x_49 = l_Array_forInUnsafe_loop___at_Lean_Widget_diffHypothesesBundle___spec__1___closed__1;
lean_ctor_set(x_3, 6, x_49);
lean_ctor_set(x_3, 1, x_5);
lean_ctor_set(x_3, 0, x_4);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_3);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_15);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_54 = lean_ctor_get(x_3, 2);
x_55 = lean_ctor_get(x_3, 3);
x_56 = lean_ctor_get(x_3, 4);
x_57 = lean_ctor_get(x_3, 5);
x_58 = lean_ctor_get(x_3, 7);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_3);
x_59 = l_Array_forInUnsafe_loop___at_Lean_Widget_diffHypothesesBundle___spec__1___closed__1;
x_60 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_60, 0, x_4);
lean_ctor_set(x_60, 1, x_5);
lean_ctor_set(x_60, 2, x_54);
lean_ctor_set(x_60, 3, x_55);
lean_ctor_set(x_60, 4, x_56);
lean_ctor_set(x_60, 5, x_57);
lean_ctor_set(x_60, 6, x_59);
lean_ctor_set(x_60, 7, x_58);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_15);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_5);
lean_dec(x_4);
x_65 = !lean_is_exclusive(x_24);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_24, 0);
x_67 = l_Lean_LocalDecl_type(x_66);
lean_dec(x_66);
x_68 = l_Lean_Widget_diffHypothesesBundle_withTypeDiff(x_1, x_67, x_3, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_68, 0);
lean_ctor_set(x_24, 0, x_70);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_24);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_68, 0, x_72);
return x_68;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_68, 0);
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_68);
lean_ctor_set(x_24, 0, x_73);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_24);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
}
else
{
uint8_t x_78; 
lean_free_object(x_24);
x_78 = !lean_is_exclusive(x_68);
if (x_78 == 0)
{
return x_68;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_68, 0);
x_80 = lean_ctor_get(x_68, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_68);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_24, 0);
lean_inc(x_82);
lean_dec(x_24);
x_83 = l_Lean_LocalDecl_type(x_82);
lean_dec(x_82);
x_84 = l_Lean_Widget_diffHypothesesBundle_withTypeDiff(x_1, x_83, x_3, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_87 = x_84;
} else {
 lean_dec_ref(x_84);
 x_87 = lean_box(0);
}
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_85);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
if (lean_is_scalar(x_87)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_87;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_86);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_84, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_84, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_94 = x_84;
} else {
 lean_dec_ref(x_84);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
}
else
{
size_t x_96; size_t x_97; 
lean_dec(x_19);
x_96 = 1;
x_97 = lean_usize_add(x_9, x_96);
lean_inc(x_6);
{
size_t _tmp_8 = x_97;
lean_object* _tmp_9 = x_6;
x_9 = _tmp_8;
x_10 = _tmp_9;
}
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_diffHypothesesBundle___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Widget_diffHypothesesBundle___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_diffHypothesesBundle(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = l_Array_zip___rarg(x_9, x_10);
x_12 = lean_array_get_size(x_11);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = 0;
x_15 = l_Lean_Widget_diffHypothesesBundle___closed__1;
lean_inc(x_3);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Widget_diffHypothesesBundle___spec__1(x_1, x_2, x_3, x_9, x_10, x_15, x_11, x_13, x_14, x_15, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
lean_ctor_set(x_16, 0, x_3);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_16, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_25);
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Widget_diffHypothesesBundle___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_1);
lean_dec(x_1);
x_17 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_18 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Widget_diffHypothesesBundle___spec__1(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_17, x_18, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_diffHypothesesBundle___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Widget_diffHypothesesBundle___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_diffHypothesesBundle___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Widget_diffHypothesesBundle(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Widget_diffHypotheses___spec__1(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_uget(x_5, x_4);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_5, x_4, x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_16 = l_Lean_Widget_diffHypothesesBundle(x_1, x_2, x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_4, x_19);
x_21 = lean_array_uset(x_15, x_4, x_17);
x_4 = x_20;
x_5 = x_21;
x_10 = x_18;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_diffHypotheses(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at_Lean_Widget_diffHypotheses___spec__1(x_1, x_2, x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Widget_diffHypotheses___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Widget_diffHypotheses___spec__1(x_11, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_diffHypotheses___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Widget_diffHypotheses(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Widget_diffInteractiveGoal___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
static lean_object* _init_l_Lean_Widget_diffInteractiveGoal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Failed to find decl for ", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Widget_diffInteractiveGoal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Widget_diffInteractiveGoal___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Widget_diffInteractiveGoal___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Widget_diffInteractiveGoal___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Widget_diffInteractiveGoal___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Widget_diffInteractiveGoal___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Unknown goal ", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Widget_diffInteractiveGoal___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Widget_diffInteractiveGoal___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Widget_diffInteractiveGoal___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Widget_diffInteractiveGoal___closed__8() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_diffInteractiveGoal(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_st_ref_get(x_5, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_2);
x_13 = l_Lean_MetavarContext_findDecl_x3f(x_12, x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_2);
x_15 = l_Lean_Widget_diffInteractiveGoal___closed__2;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Widget_diffInteractiveGoal___closed__4;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at_Lean_Widget_diffInteractiveGoal___spec__1(x_18, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_ctor_get(x_6, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_23);
x_25 = l_Lean_LocalContext_sanitizeNames(x_22, x_24);
x_26 = lean_ctor_get(x_3, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_3);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_29 = lean_ctor_get(x_3, 1);
x_30 = lean_ctor_get(x_3, 2);
x_31 = lean_ctor_get(x_3, 3);
x_32 = lean_ctor_get(x_3, 5);
x_33 = lean_ctor_get(x_3, 4);
lean_dec(x_33);
x_34 = lean_ctor_get(x_3, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_26);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_26, 0);
x_37 = lean_ctor_get(x_26, 1);
x_38 = lean_ctor_get(x_26, 2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_39 = l_Lean_Widget_diffHypotheses(x_1, x_27, x_36, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Expr_mvar___override(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_43 = lean_infer_type(x_42, x_4, x_5, x_6, x_7, x_41);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_44, x_4, x_5, x_6, x_7, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_st_ref_get(x_5, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_31);
x_53 = l_Lean_MetavarContext_findDecl_x3f(x_52, x_31);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_47);
lean_dec(x_40);
lean_free_object(x_26);
lean_dec(x_38);
lean_dec(x_37);
lean_free_object(x_3);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_29);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_31);
x_55 = l_Lean_Widget_diffInteractiveGoal___closed__6;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_Widget_diffInteractiveGoal___closed__7;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_throwError___at_Lean_Widget_diffInteractiveGoal___spec__1(x_58, x_4, x_5, x_6, x_7, x_51);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_53, 0);
lean_inc(x_60);
lean_dec(x_53);
x_61 = lean_ctor_get(x_60, 2);
lean_inc(x_61);
lean_dec(x_60);
x_62 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_61, x_4, x_5, x_6, x_7, x_51);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_65 = l_Lean_Widget_exprDiff(x_47, x_63, x_1, x_4, x_5, x_6, x_7, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_Widget_addDiffTags(x_1, x_66, x_37, x_4, x_5, x_6, x_7, x_67);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_68, 0);
lean_ctor_set(x_26, 1, x_70);
lean_ctor_set(x_26, 0, x_40);
x_71 = l_Lean_Widget_diffInteractiveGoal___closed__8;
lean_ctor_set(x_3, 4, x_71);
lean_ctor_set(x_68, 0, x_3);
return x_68;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_68, 0);
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_68);
lean_ctor_set(x_26, 1, x_72);
lean_ctor_set(x_26, 0, x_40);
x_74 = l_Lean_Widget_diffInteractiveGoal___closed__8;
lean_ctor_set(x_3, 4, x_74);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_3);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
uint8_t x_76; 
lean_dec(x_40);
lean_free_object(x_26);
lean_dec(x_38);
lean_free_object(x_3);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
x_76 = !lean_is_exclusive(x_68);
if (x_76 == 0)
{
return x_68;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_68, 0);
x_78 = lean_ctor_get(x_68, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_68);
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
lean_dec(x_40);
lean_free_object(x_26);
lean_dec(x_38);
lean_dec(x_37);
lean_free_object(x_3);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_80 = !lean_is_exclusive(x_65);
if (x_80 == 0)
{
return x_65;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_65, 0);
x_82 = lean_ctor_get(x_65, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_65);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_40);
lean_free_object(x_26);
lean_dec(x_38);
lean_dec(x_37);
lean_free_object(x_3);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_84 = !lean_is_exclusive(x_43);
if (x_84 == 0)
{
return x_43;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_43, 0);
x_86 = lean_ctor_get(x_43, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_43);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_free_object(x_26);
lean_dec(x_38);
lean_dec(x_37);
lean_free_object(x_3);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_88 = !lean_is_exclusive(x_39);
if (x_88 == 0)
{
return x_39;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_39, 0);
x_90 = lean_ctor_get(x_39, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_39);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_26, 0);
x_93 = lean_ctor_get(x_26, 1);
x_94 = lean_ctor_get(x_26, 2);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_26);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_95 = l_Lean_Widget_diffHypotheses(x_1, x_27, x_92, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = l_Lean_Expr_mvar___override(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_99 = lean_infer_type(x_98, x_4, x_5, x_6, x_7, x_97);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_100, x_4, x_5, x_6, x_7, x_101);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_st_ref_get(x_5, x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
lean_dec(x_106);
lean_inc(x_31);
x_109 = l_Lean_MetavarContext_findDecl_x3f(x_108, x_31);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_103);
lean_dec(x_96);
lean_dec(x_94);
lean_dec(x_93);
lean_free_object(x_3);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_29);
x_110 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_110, 0, x_31);
x_111 = l_Lean_Widget_diffInteractiveGoal___closed__6;
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
x_113 = l_Lean_Widget_diffInteractiveGoal___closed__7;
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Lean_throwError___at_Lean_Widget_diffInteractiveGoal___spec__1(x_114, x_4, x_5, x_6, x_7, x_107);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_116 = lean_ctor_get(x_109, 0);
lean_inc(x_116);
lean_dec(x_109);
x_117 = lean_ctor_get(x_116, 2);
lean_inc(x_117);
lean_dec(x_116);
x_118 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_117, x_4, x_5, x_6, x_7, x_107);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_121 = l_Lean_Widget_exprDiff(x_103, x_119, x_1, x_4, x_5, x_6, x_7, x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = l_Lean_Widget_addDiffTags(x_1, x_122, x_93, x_4, x_5, x_6, x_7, x_123);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_127 = x_124;
} else {
 lean_dec_ref(x_124);
 x_127 = lean_box(0);
}
x_128 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_128, 0, x_96);
lean_ctor_set(x_128, 1, x_125);
lean_ctor_set(x_128, 2, x_94);
x_129 = l_Lean_Widget_diffInteractiveGoal___closed__8;
lean_ctor_set(x_3, 4, x_129);
lean_ctor_set(x_3, 0, x_128);
if (lean_is_scalar(x_127)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_127;
}
lean_ctor_set(x_130, 0, x_3);
lean_ctor_set(x_130, 1, x_126);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_96);
lean_dec(x_94);
lean_free_object(x_3);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
x_131 = lean_ctor_get(x_124, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_124, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_133 = x_124;
} else {
 lean_dec_ref(x_124);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_96);
lean_dec(x_94);
lean_dec(x_93);
lean_free_object(x_3);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_135 = lean_ctor_get(x_121, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_121, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_137 = x_121;
} else {
 lean_dec_ref(x_121);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_96);
lean_dec(x_94);
lean_dec(x_93);
lean_free_object(x_3);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_139 = lean_ctor_get(x_99, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_99, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_141 = x_99;
} else {
 lean_dec_ref(x_99);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_94);
lean_dec(x_93);
lean_free_object(x_3);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_143 = lean_ctor_get(x_95, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_95, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_145 = x_95;
} else {
 lean_dec_ref(x_95);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_147 = lean_ctor_get(x_3, 1);
x_148 = lean_ctor_get(x_3, 2);
x_149 = lean_ctor_get(x_3, 3);
x_150 = lean_ctor_get(x_3, 5);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_3);
x_151 = lean_ctor_get(x_26, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_26, 1);
lean_inc(x_152);
x_153 = lean_ctor_get(x_26, 2);
lean_inc(x_153);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 x_154 = x_26;
} else {
 lean_dec_ref(x_26);
 x_154 = lean_box(0);
}
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_155 = l_Lean_Widget_diffHypotheses(x_1, x_27, x_151, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = l_Lean_Expr_mvar___override(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_159 = lean_infer_type(x_158, x_4, x_5, x_6, x_7, x_157);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_160, x_4, x_5, x_6, x_7, x_161);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_st_ref_get(x_5, x_164);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_ctor_get(x_166, 0);
lean_inc(x_168);
lean_dec(x_166);
lean_inc(x_149);
x_169 = l_Lean_MetavarContext_findDecl_x3f(x_168, x_149);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_163);
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_150);
lean_dec(x_148);
lean_dec(x_147);
x_170 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_170, 0, x_149);
x_171 = l_Lean_Widget_diffInteractiveGoal___closed__6;
x_172 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_170);
x_173 = l_Lean_Widget_diffInteractiveGoal___closed__7;
x_174 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
x_175 = l_Lean_throwError___at_Lean_Widget_diffInteractiveGoal___spec__1(x_174, x_4, x_5, x_6, x_7, x_167);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_176 = lean_ctor_get(x_169, 0);
lean_inc(x_176);
lean_dec(x_169);
x_177 = lean_ctor_get(x_176, 2);
lean_inc(x_177);
lean_dec(x_176);
x_178 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_177, x_4, x_5, x_6, x_7, x_167);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_181 = l_Lean_Widget_exprDiff(x_163, x_179, x_1, x_4, x_5, x_6, x_7, x_180);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = l_Lean_Widget_addDiffTags(x_1, x_182, x_152, x_4, x_5, x_6, x_7, x_183);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_187 = x_184;
} else {
 lean_dec_ref(x_184);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_188 = lean_alloc_ctor(0, 3, 0);
} else {
 x_188 = x_154;
}
lean_ctor_set(x_188, 0, x_156);
lean_ctor_set(x_188, 1, x_185);
lean_ctor_set(x_188, 2, x_153);
x_189 = l_Lean_Widget_diffInteractiveGoal___closed__8;
x_190 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_147);
lean_ctor_set(x_190, 2, x_148);
lean_ctor_set(x_190, 3, x_149);
lean_ctor_set(x_190, 4, x_189);
lean_ctor_set(x_190, 5, x_150);
if (lean_is_scalar(x_187)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_187;
}
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_186);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
x_192 = lean_ctor_get(x_184, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_184, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_194 = x_184;
} else {
 lean_dec_ref(x_184);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_193);
return x_195;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_196 = lean_ctor_get(x_181, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_181, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_198 = x_181;
} else {
 lean_dec_ref(x_181);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_200 = lean_ctor_get(x_159, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_159, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_202 = x_159;
} else {
 lean_dec_ref(x_159);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_201);
return x_203;
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_204 = lean_ctor_get(x_155, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_155, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_206 = x_155;
} else {
 lean_dec_ref(x_155);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_207, 1, x_205);
return x_207;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Widget_diffInteractiveGoal___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Widget_diffInteractiveGoal___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_diffInteractiveGoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Widget_diffInteractiveGoal(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_List_foldlM___at_Lean_Widget_diffInteractiveGoals___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Widget_diffInteractiveGoals___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_9);
x_11 = l_Lean_Expr_mvar___override(x_9);
x_12 = l_Lean_Meta_getMVars(x_11, x_3, x_4, x_5, x_6, x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_List_foldlM___at_Lean_Widget_diffInteractiveGoals___spec__1___closed__1;
x_16 = l_Lean_RBTree_fromArray___rarg(x_13, x_15);
x_17 = l_Lean_RBNode_insert___at_Lean_MVarIdMap_insert___spec__1___rarg(x_1, x_9, x_16);
x_1 = x_17;
x_2 = x_10;
x_7 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Widget_diffInteractiveGoals___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_foldr___at_Lean_Widget_diffInteractiveGoals___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_List_foldr___at_Lean_Widget_diffInteractiveGoals___spec__3(x_1, x_2, x_5);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
return x_6;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_1 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_find___at_Lean_Widget_diffInteractiveGoals___spec__2(x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_RBNode_findCore___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp___spec__4(x_7, x_4);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = 1;
return x_10;
}
}
}
else
{
lean_object* x_11; 
x_11 = l_Lean_RBNode_find___at_Lean_Widget_diffInteractiveGoals___spec__2(x_2, x_4);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_RBNode_findCore___at___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp___spec__4(x_13, x_3);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_14);
x_16 = 1;
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_box(x_1);
lean_inc(x_3);
x_14 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4___lambda__1___boxed), 4, 3);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
x_15 = l_List_find_x3f___rarg(x_14, x_4);
if (lean_obj_tag(x_15) == 0)
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (x_1 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_5, 4);
lean_inc(x_19);
lean_dec(x_5);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Widget_diffHypothesesBundle___spec__1___closed__1;
x_21 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_3);
lean_ctor_set(x_21, 4, x_19);
lean_ctor_set(x_21, 5, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_12);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_5, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_5, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_5, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_5, 5);
lean_inc(x_26);
lean_dec(x_5);
x_27 = l_Array_forInUnsafe_loop___at_Lean_Widget_diffHypothesesBundle___spec__1___closed__1;
x_28 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_3);
lean_ctor_set(x_28, 4, x_27);
lean_ctor_set(x_28, 5, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_12);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_3);
x_30 = lean_ctor_get(x_15, 0);
lean_inc(x_30);
lean_dec(x_15);
x_31 = l_Lean_Widget_diffInteractiveGoal(x_6, x_30, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4___lambda__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_7);
x_14 = 0;
x_15 = l_List_foldr___at_Lean_Widget_diffInteractiveGoals___spec__3(x_3, x_14, x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_16, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_5, 2);
lean_inc(x_20);
x_21 = lean_box(0);
x_22 = lean_ctor_get(x_5, 5);
lean_inc(x_22);
lean_dec(x_5);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_3);
lean_ctor_set(x_23, 4, x_21);
lean_ctor_set(x_23, 5, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_13);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_7, x_6);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_array_uget(x_8, x_7);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_8, x_7, x_17);
x_19 = lean_ctor_get(x_16, 3);
lean_inc(x_19);
x_20 = lean_box(x_3);
x_21 = lean_box(x_1);
lean_inc(x_4);
lean_inc(x_19);
lean_inc(x_5);
x_22 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4___lambda__3___boxed), 13, 6);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_5);
lean_closure_set(x_22, 2, x_19);
lean_closure_set(x_22, 3, x_4);
lean_closure_set(x_22, 4, x_16);
lean_closure_set(x_22, 5, x_21);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_23 = l_Lean_Widget_withGoalCtx___at_Lean_Widget_goalToInteractive___spec__8___rarg(x_19, x_22, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = 1;
x_27 = lean_usize_add(x_7, x_26);
x_28 = lean_array_uset(x_18, x_7, x_24);
x_7 = x_27;
x_8 = x_28;
x_13 = x_25;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_23);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4___at_Lean_Widget_diffInteractiveGoals___spec__5(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_array_uget(x_7, x_6);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_7, x_6, x_16);
x_18 = lean_ctor_get(x_15, 3);
lean_inc(x_18);
x_19 = lean_box(x_2);
x_20 = lean_box(x_1);
lean_inc(x_3);
lean_inc(x_18);
lean_inc(x_4);
x_21 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4___lambda__3___boxed), 13, 6);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_4);
lean_closure_set(x_21, 2, x_18);
lean_closure_set(x_21, 3, x_3);
lean_closure_set(x_21, 4, x_15);
lean_closure_set(x_21, 5, x_20);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_22 = l_Lean_Widget_withGoalCtx___at_Lean_Widget_goalToInteractive___spec__8___rarg(x_18, x_21, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = 1;
x_26 = lean_usize_add(x_6, x_25);
x_27 = lean_array_uset(x_17, x_6, x_23);
x_6 = x_26;
x_7 = x_27;
x_12 = x_24;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
static lean_object* _init_l_Lean_Widget_diffInteractiveGoals___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Widget_showTacticDiff;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_diffInteractiveGoals(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
x_10 = l_Lean_Widget_diffInteractiveGoals___closed__1;
x_11 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_box(0);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
if (x_1 == 0)
{
uint8_t x_35; 
x_35 = 0;
x_15 = x_35;
goto block_34;
}
else
{
uint8_t x_36; 
x_36 = 1;
x_15 = x_36;
goto block_34;
}
block_34:
{
lean_object* x_16; 
if (x_15 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_2, 4);
lean_inc(x_33);
lean_dec(x_2);
x_16 = x_33;
goto block_32;
}
else
{
lean_dec(x_2);
lean_inc(x_14);
x_16 = x_14;
goto block_32;
}
block_32:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_17 = l_List_foldlM___at_Lean_Widget_diffInteractiveGoals___spec__1(x_13, x_14, x_4, x_5, x_6, x_7, x_8);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_get_size(x_3);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = 0;
x_23 = l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4___at_Lean_Widget_diffInteractiveGoals___spec__5(x_1, x_15, x_16, x_18, x_21, x_22, x_3, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
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
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Widget_diffInteractiveGoals___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_foldlM___at_Lean_Widget_diffInteractiveGoals___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Widget_diffInteractiveGoals___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_Widget_diffInteractiveGoals___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at_Lean_Widget_diffInteractiveGoals___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___at_Lean_Widget_diffInteractiveGoals___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4___lambda__1(x_5, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4___lambda__2(x_13, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4___lambda__3(x_14, x_2, x_3, x_4, x_5, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_18 = l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4(x_14, x_2, x_15, x_4, x_5, x_16, x_17, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4___at_Lean_Widget_diffInteractiveGoals___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = l_Array_mapMUnsafe_map___at_Lean_Widget_diffInteractiveGoals___spec__4___at_Lean_Widget_diffInteractiveGoals___spec__5(x_13, x_14, x_3, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_diffInteractiveGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Widget_diffInteractiveGoals(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_PPGoal(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Widget_InteractiveCode(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Widget_InteractiveGoal(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Extra(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_InfoTree(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Widget_Diff(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_PPGoal(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget_InteractiveCode(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget_InteractiveGoal(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Extra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_InfoTree(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__1 = _init_l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__1();
lean_mark_persistent(l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__1);
l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__2 = _init_l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__2();
lean_mark_persistent(l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__2);
l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__3 = _init_l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__3();
lean_mark_persistent(l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__3);
l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__4 = _init_l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__4();
lean_mark_persistent(l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__4);
l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__5 = _init_l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__5();
lean_mark_persistent(l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__5);
l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__6 = _init_l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__6();
lean_mark_persistent(l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__6);
l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__7 = _init_l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__7();
lean_mark_persistent(l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__7);
l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__8 = _init_l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__8();
lean_mark_persistent(l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6____closed__8);
if (builtin) {res = l_Lean_Widget_initFn____x40_Lean_Widget_Diff___hyg_6_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Widget_showTacticDiff = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Widget_showTacticDiff);
lean_dec_ref(res);
}l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_noConfusion___rarg___closed__1 = _init_l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_noConfusion___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_noConfusion___rarg___closed__1);
l_Lean_Widget_ExprDiffTag_toString___closed__1 = _init_l_Lean_Widget_ExprDiffTag_toString___closed__1();
lean_mark_persistent(l_Lean_Widget_ExprDiffTag_toString___closed__1);
l_Lean_Widget_ExprDiffTag_toString___closed__2 = _init_l_Lean_Widget_ExprDiffTag_toString___closed__2();
lean_mark_persistent(l_Lean_Widget_ExprDiffTag_toString___closed__2);
l_Lean_Widget_ExprDiffTag_toString___closed__3 = _init_l_Lean_Widget_ExprDiffTag_toString___closed__3();
lean_mark_persistent(l_Lean_Widget_ExprDiffTag_toString___closed__3);
l_Lean_Widget_instToStringExprDiffTag___closed__1 = _init_l_Lean_Widget_instToStringExprDiffTag___closed__1();
lean_mark_persistent(l_Lean_Widget_instToStringExprDiffTag___closed__1);
l_Lean_Widget_instToStringExprDiffTag = _init_l_Lean_Widget_instToStringExprDiffTag();
lean_mark_persistent(l_Lean_Widget_instToStringExprDiffTag);
l_Lean_Widget_ExprDiff_changesBefore___default = _init_l_Lean_Widget_ExprDiff_changesBefore___default();
lean_mark_persistent(l_Lean_Widget_ExprDiff_changesBefore___default);
l_Lean_Widget_ExprDiff_changesAfter___default = _init_l_Lean_Widget_ExprDiff_changesAfter___default();
lean_mark_persistent(l_Lean_Widget_ExprDiff_changesAfter___default);
l_Lean_Widget_instEmptyCollectionExprDiff___closed__1 = _init_l_Lean_Widget_instEmptyCollectionExprDiff___closed__1();
lean_mark_persistent(l_Lean_Widget_instEmptyCollectionExprDiff___closed__1);
l_Lean_Widget_instEmptyCollectionExprDiff = _init_l_Lean_Widget_instEmptyCollectionExprDiff();
lean_mark_persistent(l_Lean_Widget_instEmptyCollectionExprDiff);
l_Lean_Widget_instAppendExprDiff___closed__1 = _init_l_Lean_Widget_instAppendExprDiff___closed__1();
lean_mark_persistent(l_Lean_Widget_instAppendExprDiff___closed__1);
l_Lean_Widget_instAppendExprDiff___closed__2 = _init_l_Lean_Widget_instAppendExprDiff___closed__2();
lean_mark_persistent(l_Lean_Widget_instAppendExprDiff___closed__2);
l_List_mapTR_loop___at_Lean_Widget_instToStringExprDiff___spec__3___closed__1 = _init_l_List_mapTR_loop___at_Lean_Widget_instToStringExprDiff___spec__3___closed__1();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Widget_instToStringExprDiff___spec__3___closed__1);
l_List_mapTR_loop___at_Lean_Widget_instToStringExprDiff___spec__3___closed__2 = _init_l_List_mapTR_loop___at_Lean_Widget_instToStringExprDiff___spec__3___closed__2();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Widget_instToStringExprDiff___spec__3___closed__2);
l_List_mapTR_loop___at_Lean_Widget_instToStringExprDiff___spec__3___closed__3 = _init_l_List_mapTR_loop___at_Lean_Widget_instToStringExprDiff___spec__3___closed__3();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Widget_instToStringExprDiff___spec__3___closed__3);
l_Lean_Widget_instToStringExprDiff___closed__1 = _init_l_Lean_Widget_instToStringExprDiff___closed__1();
lean_mark_persistent(l_Lean_Widget_instToStringExprDiff___closed__1);
l_Lean_Widget_instToStringExprDiff___closed__2 = _init_l_Lean_Widget_instToStringExprDiff___closed__2();
lean_mark_persistent(l_Lean_Widget_instToStringExprDiff___closed__2);
l_Lean_Widget_exprDiffCore_piDiff___lambda__3___closed__1 = _init_l_Lean_Widget_exprDiffCore_piDiff___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Widget_exprDiffCore_piDiff___lambda__3___closed__1);
l_Lean_Widget_exprDiffCore_piDiff___lambda__3___closed__2 = _init_l_Lean_Widget_exprDiffCore_piDiff___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Widget_exprDiffCore_piDiff___lambda__3___closed__2);
l_Lean_Widget_exprDiffCore___lambda__3___closed__1 = _init_l_Lean_Widget_exprDiffCore___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Widget_exprDiffCore___lambda__3___closed__1);
l_Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1 = _init_l_Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1();
lean_mark_persistent(l_Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1);
l_Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__2 = _init_l_Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__2();
lean_mark_persistent(l_Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Widget_diffHypothesesBundle___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Widget_diffHypothesesBundle___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Widget_diffHypothesesBundle___spec__1___closed__1);
l_Lean_Widget_diffHypothesesBundle___closed__1 = _init_l_Lean_Widget_diffHypothesesBundle___closed__1();
lean_mark_persistent(l_Lean_Widget_diffHypothesesBundle___closed__1);
l_Lean_Widget_diffInteractiveGoal___closed__1 = _init_l_Lean_Widget_diffInteractiveGoal___closed__1();
lean_mark_persistent(l_Lean_Widget_diffInteractiveGoal___closed__1);
l_Lean_Widget_diffInteractiveGoal___closed__2 = _init_l_Lean_Widget_diffInteractiveGoal___closed__2();
lean_mark_persistent(l_Lean_Widget_diffInteractiveGoal___closed__2);
l_Lean_Widget_diffInteractiveGoal___closed__3 = _init_l_Lean_Widget_diffInteractiveGoal___closed__3();
lean_mark_persistent(l_Lean_Widget_diffInteractiveGoal___closed__3);
l_Lean_Widget_diffInteractiveGoal___closed__4 = _init_l_Lean_Widget_diffInteractiveGoal___closed__4();
lean_mark_persistent(l_Lean_Widget_diffInteractiveGoal___closed__4);
l_Lean_Widget_diffInteractiveGoal___closed__5 = _init_l_Lean_Widget_diffInteractiveGoal___closed__5();
lean_mark_persistent(l_Lean_Widget_diffInteractiveGoal___closed__5);
l_Lean_Widget_diffInteractiveGoal___closed__6 = _init_l_Lean_Widget_diffInteractiveGoal___closed__6();
lean_mark_persistent(l_Lean_Widget_diffInteractiveGoal___closed__6);
l_Lean_Widget_diffInteractiveGoal___closed__7 = _init_l_Lean_Widget_diffInteractiveGoal___closed__7();
lean_mark_persistent(l_Lean_Widget_diffInteractiveGoal___closed__7);
l_Lean_Widget_diffInteractiveGoal___closed__8 = _init_l_Lean_Widget_diffInteractiveGoal___closed__8();
lean_mark_persistent(l_Lean_Widget_diffInteractiveGoal___closed__8);
l_List_foldlM___at_Lean_Widget_diffInteractiveGoals___spec__1___closed__1 = _init_l_List_foldlM___at_Lean_Widget_diffInteractiveGoals___spec__1___closed__1();
lean_mark_persistent(l_List_foldlM___at_Lean_Widget_diffInteractiveGoals___spec__1___closed__1);
l_Lean_Widget_diffInteractiveGoals___closed__1 = _init_l_Lean_Widget_diffInteractiveGoals___closed__1();
lean_mark_persistent(l_Lean_Widget_diffInteractiveGoals___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
