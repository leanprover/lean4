// Lean compiler output
// Module: Lean.Widget.Diff
// Imports: public import Lean.Widget.InteractiveGoal
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
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_SubExpr_Pos_pushNaryArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_SubExpr_Pos_pushNthBindingDomain(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_getFVarFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getForallBodyMaxDepth(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_pushNthBindingBody(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getForallBinderNames(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_pushBindingBody(lean_object*);
lean_object* l_Lean_SubExpr_Pos_pushBindingDomain(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_SubExpr_Pos_pushProj(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_findDecl_x3f(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_sanitizeNames(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_SubExpr_Pos_root;
lean_object* l_Lean_Widget_SubexprInfo_withDiffTag(uint8_t, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
lean_object* l_List_find_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarIdSet_ofArray(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_SubExpr_Pos_toString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "showTacticDiff"};
static const lean_object* l_Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(169, 112, 244, 47, 27, 57, 231, 91)}};
static const lean_object* l_Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "When true, interactive goals for tactics will be decorated with diffing information. "};
static const lean_object* l_Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Widget_initFn___closed__4_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Widget_initFn___closed__4_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Widget_initFn___closed__4_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Widget"};
static const lean_object* l_Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Widget_initFn___closed__6_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_initFn___closed__4_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Widget_initFn___closed__6_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_initFn___closed__6_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_ctor_object l_Lean_Widget_initFn___closed__6_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_initFn___closed__6_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(124, 145, 92, 165, 32, 54, 111, 74)}};
static const lean_object* l_Lean_Widget_initFn___closed__6_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Widget_initFn___closed__6_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_showTacticDiff;
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "change"};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__0 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__0_value;
static const lean_string_object l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "delete"};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__1 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__1_value;
static const lean_string_object l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "insert"};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__2 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiffTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiffTag___closed__0 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiffTag___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiffTag = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiffTag___closed__0_value;
static const lean_ctor_object l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0_value;
LEAN_EXPORT uint8_t l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__0 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__0_value;
static const lean_closure_object l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__0_value)} };
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__1 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__1_value;
static lean_once_cell_t l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff;
static const lean_string_object l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__0_value;
static const lean_closure_object l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__1_value;
static const lean_closure_object l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__2_value;
static const lean_closure_object l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__3 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__3_value;
static const lean_closure_object l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__4_value;
static const lean_closure_object l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__5 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__5_value;
static const lean_closure_object l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__6 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__6_value;
static const lean_ctor_object l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__0_value),((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__1_value)}};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__7 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__7_value;
static const lean_ctor_object l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__7_value),((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__2_value),((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__3_value),((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__4_value),((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__5_value)}};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__8 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__8_value;
static const lean_ctor_object l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__8_value),((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__6_value)}};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__9 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "before: "};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__0_value;
static const lean_string_object l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\nafter: "};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__1 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__0 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__0_value;
static const lean_closure_object l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__1 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__1_value;
static const lean_closure_object l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__1_value),((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__0_value)} };
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__2 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__2_value;
static const lean_closure_object l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__3 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__3_value;
static const lean_closure_object l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__2_value),((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__3_value)} };
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__4 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__4_value;
LEAN_EXPORT const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__4_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertAfterChange(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertAfterChange___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "should not happen"};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__0 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__0_value;
static lean_once_cell_t l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "internal error: empty fvar list!"};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__0 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__0_value;
static lean_once_cell_t l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__0 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__0_value;
static const lean_string_object l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Unknown goal "};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__1 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__1_value;
static lean_once_cell_t l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2;
static const lean_string_object l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Failed to find decl for "};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__3 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__3_value;
static lean_once_cell_t l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4;
static const lean_string_object l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__5 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__5_value;
static lean_once_cell_t l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__1(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unknown goal "};
static const lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_diffInteractiveGoals(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_diffInteractiveGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_33_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_decl_2_);
if (v_isSharedCheck_33_ == 0)
{
v___x_8_ = v_decl_2_;
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_descr_6_);
lean_inc(v_defValue_5_);
lean_dec(v_decl_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_alloc_ctor(1, 0, 1);
v___x_11_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_10_, 0, v___x_11_);
lean_inc(v_name_1_);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
lean_inc(v_name_1_);
v___x_13_ = lean_register_option(v_name_1_, v___x_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_23_; 
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_23_ == 0)
{
lean_object* v_unused_24_; 
v_unused_24_ = lean_ctor_get(v___x_13_, 0);
lean_dec(v_unused_24_);
v___x_15_ = v___x_13_;
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
else
{
lean_dec(v___x_13_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_defValue_5_);
lean_ctor_set(v___x_8_, 0, v_name_1_);
v___x_18_ = v___x_8_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_name_1_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_defValue_5_);
v___x_18_ = v_reuseFailAlloc_22_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___x_20_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_18_);
v___x_20_ = v___x_15_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
else
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
lean_del_object(v___x_8_);
lean_dec(v_defValue_5_);
lean_dec(v_name_1_);
v_a_25_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v___x_13_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_13_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_a_25_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_34_, lean_object* v_decl_35_, lean_object* v_ref_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_register___at___00Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__spec__0(v_name_34_, v_decl_35_, v_ref_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = ((lean_object*)(l_Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l_Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_));
v___x_56_ = ((lean_object*)(l_Lean_Widget_initFn___closed__6_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_));
v___x_57_ = l_Lean_Option_register___at___00Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__spec__0(v___x_54_, v___x_55_, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4____boxed(lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_();
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx(uint8_t v_x_60_){
_start:
{
switch(v_x_60_)
{
case 0:
{
lean_object* v___x_61_; 
v___x_61_ = lean_unsigned_to_nat(0u);
return v___x_61_;
}
case 1:
{
lean_object* v___x_62_; 
v___x_62_ = lean_unsigned_to_nat(1u);
return v___x_62_;
}
default: 
{
lean_object* v___x_63_; 
v___x_63_ = lean_unsigned_to_nat(2u);
return v___x_63_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx___boxed(lean_object* v_x_64_){
_start:
{
uint8_t v_x_boxed_65_; lean_object* v_res_66_; 
v_x_boxed_65_ = lean_unbox(v_x_64_);
v_res_66_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx(v_x_boxed_65_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toCtorIdx(uint8_t v_x_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx(v_x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toCtorIdx___boxed(lean_object* v_x_69_){
_start:
{
uint8_t v_x_4__boxed_70_; lean_object* v_res_71_; 
v_x_4__boxed_70_ = lean_unbox(v_x_69_);
v_res_71_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toCtorIdx(v_x_4__boxed_70_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___redArg(lean_object* v_k_72_){
_start:
{
lean_inc(v_k_72_);
return v_k_72_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___redArg___boxed(lean_object* v_k_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___redArg(v_k_73_);
lean_dec(v_k_73_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim(lean_object* v_motive_75_, lean_object* v_ctorIdx_76_, uint8_t v_t_77_, lean_object* v_h_78_, lean_object* v_k_79_){
_start:
{
lean_inc(v_k_79_);
return v_k_79_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___boxed(lean_object* v_motive_80_, lean_object* v_ctorIdx_81_, lean_object* v_t_82_, lean_object* v_h_83_, lean_object* v_k_84_){
_start:
{
uint8_t v_t_boxed_85_; lean_object* v_res_86_; 
v_t_boxed_85_ = lean_unbox(v_t_82_);
v_res_86_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim(v_motive_80_, v_ctorIdx_81_, v_t_boxed_85_, v_h_83_, v_k_84_);
lean_dec(v_k_84_);
lean_dec(v_ctorIdx_81_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___redArg(lean_object* v_change_87_){
_start:
{
lean_inc(v_change_87_);
return v_change_87_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___redArg___boxed(lean_object* v_change_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___redArg(v_change_88_);
lean_dec(v_change_88_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim(lean_object* v_motive_90_, uint8_t v_t_91_, lean_object* v_h_92_, lean_object* v_change_93_){
_start:
{
lean_inc(v_change_93_);
return v_change_93_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___boxed(lean_object* v_motive_94_, lean_object* v_t_95_, lean_object* v_h_96_, lean_object* v_change_97_){
_start:
{
uint8_t v_t_boxed_98_; lean_object* v_res_99_; 
v_t_boxed_98_ = lean_unbox(v_t_95_);
v_res_99_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim(v_motive_94_, v_t_boxed_98_, v_h_96_, v_change_97_);
lean_dec(v_change_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___redArg(lean_object* v_delete_100_){
_start:
{
lean_inc(v_delete_100_);
return v_delete_100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___redArg___boxed(lean_object* v_delete_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___redArg(v_delete_101_);
lean_dec(v_delete_101_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim(lean_object* v_motive_103_, uint8_t v_t_104_, lean_object* v_h_105_, lean_object* v_delete_106_){
_start:
{
lean_inc(v_delete_106_);
return v_delete_106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___boxed(lean_object* v_motive_107_, lean_object* v_t_108_, lean_object* v_h_109_, lean_object* v_delete_110_){
_start:
{
uint8_t v_t_boxed_111_; lean_object* v_res_112_; 
v_t_boxed_111_ = lean_unbox(v_t_108_);
v_res_112_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim(v_motive_107_, v_t_boxed_111_, v_h_109_, v_delete_110_);
lean_dec(v_delete_110_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___redArg(lean_object* v_insert_113_){
_start:
{
lean_inc(v_insert_113_);
return v_insert_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___redArg___boxed(lean_object* v_insert_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___redArg(v_insert_114_);
lean_dec(v_insert_114_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim(lean_object* v_motive_116_, uint8_t v_t_117_, lean_object* v_h_118_, lean_object* v_insert_119_){
_start:
{
lean_inc(v_insert_119_);
return v_insert_119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___boxed(lean_object* v_motive_120_, lean_object* v_t_121_, lean_object* v_h_122_, lean_object* v_insert_123_){
_start:
{
uint8_t v_t_boxed_124_; lean_object* v_res_125_; 
v_t_boxed_124_ = lean_unbox(v_t_121_);
v_res_125_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim(v_motive_120_, v_t_boxed_124_, v_h_122_, v_insert_123_);
lean_dec(v_insert_123_);
return v_res_125_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag(uint8_t v_x_126_, uint8_t v_x_127_){
_start:
{
if (v_x_126_ == 0)
{
switch(v_x_127_)
{
case 0:
{
uint8_t v___x_128_; 
v___x_128_ = 1;
return v___x_128_;
}
case 1:
{
uint8_t v___x_129_; 
v___x_129_ = 3;
return v___x_129_;
}
default: 
{
uint8_t v___x_130_; 
v___x_130_ = 5;
return v___x_130_;
}
}
}
else
{
switch(v_x_127_)
{
case 0:
{
uint8_t v___x_131_; 
v___x_131_ = 0;
return v___x_131_;
}
case 1:
{
uint8_t v___x_132_; 
v___x_132_ = 2;
return v___x_132_;
}
default: 
{
uint8_t v___x_133_; 
v___x_133_ = 4;
return v___x_133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag___boxed(lean_object* v_x_134_, lean_object* v_x_135_){
_start:
{
uint8_t v_x_49__boxed_136_; uint8_t v_x_50__boxed_137_; uint8_t v_res_138_; lean_object* v_r_139_; 
v_x_49__boxed_136_ = lean_unbox(v_x_134_);
v_x_50__boxed_137_ = lean_unbox(v_x_135_);
v_res_138_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag(v_x_49__boxed_136_, v_x_50__boxed_137_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString(uint8_t v_x_143_){
_start:
{
switch(v_x_143_)
{
case 0:
{
lean_object* v___x_144_; 
v___x_144_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__0));
return v___x_144_;
}
case 1:
{
lean_object* v___x_145_; 
v___x_145_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__1));
return v___x_145_;
}
default: 
{
lean_object* v___x_146_; 
v___x_146_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__2));
return v___x_146_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___boxed(lean_object* v_x_147_){
_start:
{
uint8_t v_x_31__boxed_148_; lean_object* v_res_149_; 
v_x_31__boxed_148_ = lean_unbox(v_x_147_);
v_res_149_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString(v_x_31__boxed_148_);
return v_res_149_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0(lean_object* v_x_155_, lean_object* v_y_156_){
_start:
{
uint8_t v___x_157_; 
v___x_157_ = lean_nat_dec_lt(v_x_155_, v_y_156_);
if (v___x_157_ == 0)
{
uint8_t v___x_158_; 
v___x_158_ = lean_nat_dec_eq(v_x_155_, v_y_156_);
if (v___x_158_ == 0)
{
uint8_t v___x_159_; 
v___x_159_ = 2;
return v___x_159_;
}
else
{
uint8_t v___x_160_; 
v___x_160_ = 1;
return v___x_160_;
}
}
else
{
uint8_t v___x_161_; 
v___x_161_ = 0;
return v___x_161_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0___boxed(lean_object* v_x_162_, lean_object* v_y_163_){
_start:
{
uint8_t v_res_164_; lean_object* v_r_165_; 
v_res_164_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0(v_x_162_, v_y_163_);
lean_dec(v_y_163_);
lean_dec(v_x_162_);
v_r_165_ = lean_box(v_res_164_);
return v_r_165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1(uint8_t v_b_u2082_166_, lean_object* v_x_167_){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = lean_box(v_b_u2082_166_);
v___x_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1___boxed(lean_object* v_b_u2082_170_, lean_object* v_x_171_){
_start:
{
uint8_t v_b_u2082_boxed_172_; lean_object* v_res_173_; 
v_b_u2082_boxed_172_ = lean_unbox(v_b_u2082_170_);
v_res_173_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1(v_b_u2082_boxed_172_, v_x_171_);
lean_dec(v_x_171_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2(lean_object* v___f_174_, lean_object* v_t_175_, lean_object* v_a_176_, uint8_t v_b_u2082_177_){
_start:
{
lean_object* v___x_178_; lean_object* v___f_179_; lean_object* v___x_180_; 
v___x_178_ = lean_box(v_b_u2082_177_);
v___f_179_ = lean_alloc_closure((void*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1___boxed), 2, 1);
lean_closure_set(v___f_179_, 0, v___x_178_);
v___x_180_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v___f_174_, v_a_176_, v___f_179_, v_t_175_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2___boxed(lean_object* v___f_181_, lean_object* v_t_182_, lean_object* v_a_183_, lean_object* v_b_u2082_184_){
_start:
{
uint8_t v_b_u2082_boxed_185_; lean_object* v_res_186_; 
v_b_u2082_boxed_185_ = lean_unbox(v_b_u2082_184_);
v_res_186_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2(v___f_181_, v_t_182_, v_a_183_, v_b_u2082_boxed_185_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__5(lean_object* v___f_187_, lean_object* v___f_188_, lean_object* v_a_189_, lean_object* v_b_190_){
_start:
{
lean_object* v_changesBefore_191_; lean_object* v_changesAfter_192_; lean_object* v_changesBefore_193_; lean_object* v_changesAfter_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_203_; 
v_changesBefore_191_ = lean_ctor_get(v_a_189_, 0);
lean_inc(v_changesBefore_191_);
v_changesAfter_192_ = lean_ctor_get(v_a_189_, 1);
lean_inc(v_changesAfter_192_);
lean_dec_ref(v_a_189_);
v_changesBefore_193_ = lean_ctor_get(v_b_190_, 0);
v_changesAfter_194_ = lean_ctor_get(v_b_190_, 1);
v_isSharedCheck_203_ = !lean_is_exclusive(v_b_190_);
if (v_isSharedCheck_203_ == 0)
{
v___x_196_ = v_b_190_;
v_isShared_197_ = v_isSharedCheck_203_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_changesAfter_194_);
lean_inc(v_changesBefore_193_);
lean_dec(v_b_190_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_203_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_198_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_187_, v_changesBefore_191_, v_changesBefore_193_);
v___x_199_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_188_, v_changesAfter_192_, v_changesAfter_194_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 1, v___x_199_);
lean_ctor_set(v___x_196_, 0, v___x_198_);
v___x_201_ = v___x_196_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_198_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v___x_199_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__2(void){
_start:
{
lean_object* v___f_207_; lean_object* v___f_208_; 
v___f_207_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__1));
v___f_208_ = lean_alloc_closure((void*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__5), 4, 2);
lean_closure_set(v___f_208_, 0, v___f_207_);
lean_closure_set(v___f_208_, 1, v___f_207_);
return v___f_208_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff(void){
_start:
{
lean_object* v___f_209_; 
v___f_209_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__2, &l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__2_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__2);
return v___f_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0(lean_object* v_x_213_){
_start:
{
lean_object* v_fst_214_; lean_object* v_snd_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v_fst_214_ = lean_ctor_get(v_x_213_, 0);
v_snd_215_ = lean_ctor_get(v_x_213_, 1);
v___x_216_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__0));
v___x_217_ = l_Lean_SubExpr_Pos_toString(v_fst_214_);
v___x_218_ = lean_string_append(v___x_216_, v___x_217_);
lean_dec_ref(v___x_217_);
v___x_219_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__1));
v___x_220_ = lean_string_append(v___x_218_, v___x_219_);
v___x_221_ = lean_unbox(v_snd_215_);
v___x_222_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString(v___x_221_);
v___x_223_ = lean_string_append(v___x_220_, v___x_222_);
lean_dec_ref(v___x_222_);
v___x_224_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__2));
v___x_225_ = lean_string_append(v___x_223_, v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___boxed(lean_object* v_x_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0(v_x_226_);
lean_dec_ref(v_x_226_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1(lean_object* v_x1_228_, uint8_t v_x2_229_, lean_object* v_x3_230_){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_231_ = lean_box(v_x2_229_);
v___x_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_232_, 0, v_x1_228_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set(v___x_233_, 1, v_x3_230_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1___boxed(lean_object* v_x1_234_, lean_object* v_x2_235_, lean_object* v_x3_236_){
_start:
{
uint8_t v_x2_243__boxed_237_; lean_object* v_res_238_; 
v_x2_243__boxed_237_ = lean_unbox(v_x2_235_);
v_res_238_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1(v_x1_234_, v_x2_243__boxed_237_, v_x3_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2(lean_object* v___f_258_, lean_object* v___f_259_, lean_object* v_p_260_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_261_ = lean_box(0);
v___x_262_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__9));
v___x_263_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_262_, v___f_258_, v___x_261_, v_p_260_);
v___x_264_ = l_List_mapTR_loop___redArg(v___f_259_, v___x_263_, v___x_261_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3(lean_object* v_f_267_, lean_object* v___f_268_, lean_object* v_x_269_){
_start:
{
lean_object* v_changesBefore_270_; lean_object* v_changesAfter_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v_changesBefore_270_ = lean_ctor_get(v_x_269_, 0);
lean_inc(v_changesBefore_270_);
v_changesAfter_271_ = lean_ctor_get(v_x_269_, 1);
lean_inc(v_changesAfter_271_);
lean_dec_ref(v_x_269_);
v___x_272_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__0));
lean_inc_ref(v_f_267_);
v___x_273_ = lean_apply_1(v_f_267_, v_changesBefore_270_);
lean_inc_ref(v___f_268_);
v___x_274_ = l_List_toString___redArg(v___f_268_, v___x_273_);
v___x_275_ = lean_string_append(v___x_272_, v___x_274_);
lean_dec_ref(v___x_274_);
v___x_276_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__1));
v___x_277_ = lean_string_append(v___x_275_, v___x_276_);
v___x_278_ = lean_apply_1(v_f_267_, v_changesAfter_271_);
v___x_279_ = l_List_toString___redArg(v___f_268_, v___x_278_);
v___x_280_ = lean_string_append(v___x_277_, v___x_279_);
lean_dec_ref(v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(lean_object* v_k_291_, lean_object* v_v_292_, lean_object* v_t_293_){
_start:
{
if (lean_obj_tag(v_t_293_) == 0)
{
lean_object* v_size_294_; lean_object* v_k_295_; lean_object* v_v_296_; lean_object* v_l_297_; lean_object* v_r_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_579_; 
v_size_294_ = lean_ctor_get(v_t_293_, 0);
v_k_295_ = lean_ctor_get(v_t_293_, 1);
v_v_296_ = lean_ctor_get(v_t_293_, 2);
v_l_297_ = lean_ctor_get(v_t_293_, 3);
v_r_298_ = lean_ctor_get(v_t_293_, 4);
v_isSharedCheck_579_ = !lean_is_exclusive(v_t_293_);
if (v_isSharedCheck_579_ == 0)
{
v___x_300_ = v_t_293_;
v_isShared_301_ = v_isSharedCheck_579_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_r_298_);
lean_inc(v_l_297_);
lean_inc(v_v_296_);
lean_inc(v_k_295_);
lean_inc(v_size_294_);
lean_dec(v_t_293_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_579_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
uint8_t v___x_302_; 
v___x_302_ = lean_nat_dec_lt(v_k_291_, v_k_295_);
if (v___x_302_ == 0)
{
uint8_t v___x_303_; 
v___x_303_ = lean_nat_dec_eq(v_k_291_, v_k_295_);
if (v___x_303_ == 0)
{
lean_object* v_impl_304_; lean_object* v___x_305_; 
lean_dec(v_size_294_);
v_impl_304_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_k_291_, v_v_292_, v_r_298_);
v___x_305_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_297_) == 0)
{
lean_object* v_size_306_; lean_object* v_size_307_; lean_object* v_k_308_; lean_object* v_v_309_; lean_object* v_l_310_; lean_object* v_r_311_; lean_object* v___x_312_; lean_object* v___x_313_; uint8_t v___x_314_; 
v_size_306_ = lean_ctor_get(v_l_297_, 0);
v_size_307_ = lean_ctor_get(v_impl_304_, 0);
lean_inc(v_size_307_);
v_k_308_ = lean_ctor_get(v_impl_304_, 1);
lean_inc(v_k_308_);
v_v_309_ = lean_ctor_get(v_impl_304_, 2);
lean_inc(v_v_309_);
v_l_310_ = lean_ctor_get(v_impl_304_, 3);
lean_inc(v_l_310_);
v_r_311_ = lean_ctor_get(v_impl_304_, 4);
lean_inc(v_r_311_);
v___x_312_ = lean_unsigned_to_nat(3u);
v___x_313_ = lean_nat_mul(v___x_312_, v_size_306_);
v___x_314_ = lean_nat_dec_lt(v___x_313_, v_size_307_);
lean_dec(v___x_313_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_318_; 
lean_dec(v_r_311_);
lean_dec(v_l_310_);
lean_dec(v_v_309_);
lean_dec(v_k_308_);
v___x_315_ = lean_nat_add(v___x_305_, v_size_306_);
v___x_316_ = lean_nat_add(v___x_315_, v_size_307_);
lean_dec(v_size_307_);
lean_dec(v___x_315_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 4, v_impl_304_);
lean_ctor_set(v___x_300_, 0, v___x_316_);
v___x_318_ = v___x_300_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_316_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_k_295_);
lean_ctor_set(v_reuseFailAlloc_319_, 2, v_v_296_);
lean_ctor_set(v_reuseFailAlloc_319_, 3, v_l_297_);
lean_ctor_set(v_reuseFailAlloc_319_, 4, v_impl_304_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
else
{
lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_383_; 
v_isSharedCheck_383_ = !lean_is_exclusive(v_impl_304_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; lean_object* v_unused_385_; lean_object* v_unused_386_; lean_object* v_unused_387_; lean_object* v_unused_388_; 
v_unused_384_ = lean_ctor_get(v_impl_304_, 4);
lean_dec(v_unused_384_);
v_unused_385_ = lean_ctor_get(v_impl_304_, 3);
lean_dec(v_unused_385_);
v_unused_386_ = lean_ctor_get(v_impl_304_, 2);
lean_dec(v_unused_386_);
v_unused_387_ = lean_ctor_get(v_impl_304_, 1);
lean_dec(v_unused_387_);
v_unused_388_ = lean_ctor_get(v_impl_304_, 0);
lean_dec(v_unused_388_);
v___x_321_ = v_impl_304_;
v_isShared_322_ = v_isSharedCheck_383_;
goto v_resetjp_320_;
}
else
{
lean_dec(v_impl_304_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_383_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v_size_323_; lean_object* v_k_324_; lean_object* v_v_325_; lean_object* v_l_326_; lean_object* v_r_327_; lean_object* v_size_328_; lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v_size_323_ = lean_ctor_get(v_l_310_, 0);
v_k_324_ = lean_ctor_get(v_l_310_, 1);
v_v_325_ = lean_ctor_get(v_l_310_, 2);
v_l_326_ = lean_ctor_get(v_l_310_, 3);
v_r_327_ = lean_ctor_get(v_l_310_, 4);
v_size_328_ = lean_ctor_get(v_r_311_, 0);
v___x_329_ = lean_unsigned_to_nat(2u);
v___x_330_ = lean_nat_mul(v___x_329_, v_size_328_);
v___x_331_ = lean_nat_dec_lt(v_size_323_, v___x_330_);
lean_dec(v___x_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_359_; 
lean_inc(v_r_327_);
lean_inc(v_l_326_);
lean_inc(v_v_325_);
lean_inc(v_k_324_);
v_isSharedCheck_359_ = !lean_is_exclusive(v_l_310_);
if (v_isSharedCheck_359_ == 0)
{
lean_object* v_unused_360_; lean_object* v_unused_361_; lean_object* v_unused_362_; lean_object* v_unused_363_; lean_object* v_unused_364_; 
v_unused_360_ = lean_ctor_get(v_l_310_, 4);
lean_dec(v_unused_360_);
v_unused_361_ = lean_ctor_get(v_l_310_, 3);
lean_dec(v_unused_361_);
v_unused_362_ = lean_ctor_get(v_l_310_, 2);
lean_dec(v_unused_362_);
v_unused_363_ = lean_ctor_get(v_l_310_, 1);
lean_dec(v_unused_363_);
v_unused_364_ = lean_ctor_get(v_l_310_, 0);
lean_dec(v_unused_364_);
v___x_333_ = v_l_310_;
v_isShared_334_ = v_isSharedCheck_359_;
goto v_resetjp_332_;
}
else
{
lean_dec(v_l_310_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_359_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_349_; 
v___x_335_ = lean_nat_add(v___x_305_, v_size_306_);
v___x_336_ = lean_nat_add(v___x_335_, v_size_307_);
lean_dec(v_size_307_);
if (lean_obj_tag(v_l_326_) == 0)
{
lean_object* v_size_357_; 
v_size_357_ = lean_ctor_get(v_l_326_, 0);
lean_inc(v_size_357_);
v___y_349_ = v_size_357_;
goto v___jp_348_;
}
else
{
lean_object* v___x_358_; 
v___x_358_ = lean_unsigned_to_nat(0u);
v___y_349_ = v___x_358_;
goto v___jp_348_;
}
v___jp_337_:
{
lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_341_ = lean_nat_add(v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec(v___y_339_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 4, v_r_311_);
lean_ctor_set(v___x_333_, 3, v_r_327_);
lean_ctor_set(v___x_333_, 2, v_v_309_);
lean_ctor_set(v___x_333_, 1, v_k_308_);
lean_ctor_set(v___x_333_, 0, v___x_341_);
v___x_343_ = v___x_333_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_k_308_);
lean_ctor_set(v_reuseFailAlloc_347_, 2, v_v_309_);
lean_ctor_set(v_reuseFailAlloc_347_, 3, v_r_327_);
lean_ctor_set(v_reuseFailAlloc_347_, 4, v_r_311_);
v___x_343_ = v_reuseFailAlloc_347_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_345_; 
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 4, v___x_343_);
lean_ctor_set(v___x_321_, 3, v___y_338_);
lean_ctor_set(v___x_321_, 2, v_v_325_);
lean_ctor_set(v___x_321_, 1, v_k_324_);
lean_ctor_set(v___x_321_, 0, v___x_336_);
v___x_345_ = v___x_321_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_k_324_);
lean_ctor_set(v_reuseFailAlloc_346_, 2, v_v_325_);
lean_ctor_set(v_reuseFailAlloc_346_, 3, v___y_338_);
lean_ctor_set(v_reuseFailAlloc_346_, 4, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
v___jp_348_:
{
lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_350_ = lean_nat_add(v___x_335_, v___y_349_);
lean_dec(v___y_349_);
lean_dec(v___x_335_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 4, v_l_326_);
lean_ctor_set(v___x_300_, 0, v___x_350_);
v___x_352_ = v___x_300_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_k_295_);
lean_ctor_set(v_reuseFailAlloc_356_, 2, v_v_296_);
lean_ctor_set(v_reuseFailAlloc_356_, 3, v_l_297_);
lean_ctor_set(v_reuseFailAlloc_356_, 4, v_l_326_);
v___x_352_ = v_reuseFailAlloc_356_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_353_; 
v___x_353_ = lean_nat_add(v___x_305_, v_size_328_);
if (lean_obj_tag(v_r_327_) == 0)
{
lean_object* v_size_354_; 
v_size_354_ = lean_ctor_get(v_r_327_, 0);
lean_inc(v_size_354_);
v___y_338_ = v___x_352_;
v___y_339_ = v___x_353_;
v___y_340_ = v_size_354_;
goto v___jp_337_;
}
else
{
lean_object* v___x_355_; 
v___x_355_ = lean_unsigned_to_nat(0u);
v___y_338_ = v___x_352_;
v___y_339_ = v___x_353_;
v___y_340_ = v___x_355_;
goto v___jp_337_;
}
}
}
}
}
else
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_369_; 
lean_del_object(v___x_300_);
v___x_365_ = lean_nat_add(v___x_305_, v_size_306_);
v___x_366_ = lean_nat_add(v___x_365_, v_size_307_);
lean_dec(v_size_307_);
v___x_367_ = lean_nat_add(v___x_365_, v_size_323_);
lean_dec(v___x_365_);
lean_inc_ref(v_l_297_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 4, v_l_310_);
lean_ctor_set(v___x_321_, 3, v_l_297_);
lean_ctor_set(v___x_321_, 2, v_v_296_);
lean_ctor_set(v___x_321_, 1, v_k_295_);
lean_ctor_set(v___x_321_, 0, v___x_367_);
v___x_369_ = v___x_321_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_k_295_);
lean_ctor_set(v_reuseFailAlloc_382_, 2, v_v_296_);
lean_ctor_set(v_reuseFailAlloc_382_, 3, v_l_297_);
lean_ctor_set(v_reuseFailAlloc_382_, 4, v_l_310_);
v___x_369_ = v_reuseFailAlloc_382_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
v_isSharedCheck_376_ = !lean_is_exclusive(v_l_297_);
if (v_isSharedCheck_376_ == 0)
{
lean_object* v_unused_377_; lean_object* v_unused_378_; lean_object* v_unused_379_; lean_object* v_unused_380_; lean_object* v_unused_381_; 
v_unused_377_ = lean_ctor_get(v_l_297_, 4);
lean_dec(v_unused_377_);
v_unused_378_ = lean_ctor_get(v_l_297_, 3);
lean_dec(v_unused_378_);
v_unused_379_ = lean_ctor_get(v_l_297_, 2);
lean_dec(v_unused_379_);
v_unused_380_ = lean_ctor_get(v_l_297_, 1);
lean_dec(v_unused_380_);
v_unused_381_ = lean_ctor_get(v_l_297_, 0);
lean_dec(v_unused_381_);
v___x_371_ = v_l_297_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_dec(v_l_297_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 4, v_r_311_);
lean_ctor_set(v___x_371_, 3, v___x_369_);
lean_ctor_set(v___x_371_, 2, v_v_309_);
lean_ctor_set(v___x_371_, 1, v_k_308_);
lean_ctor_set(v___x_371_, 0, v___x_366_);
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_k_308_);
lean_ctor_set(v_reuseFailAlloc_375_, 2, v_v_309_);
lean_ctor_set(v_reuseFailAlloc_375_, 3, v___x_369_);
lean_ctor_set(v_reuseFailAlloc_375_, 4, v_r_311_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_389_; 
v_l_389_ = lean_ctor_get(v_impl_304_, 3);
lean_inc(v_l_389_);
if (lean_obj_tag(v_l_389_) == 0)
{
lean_object* v_r_390_; lean_object* v_k_391_; lean_object* v_v_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_415_; 
v_r_390_ = lean_ctor_get(v_impl_304_, 4);
v_k_391_ = lean_ctor_get(v_impl_304_, 1);
v_v_392_ = lean_ctor_get(v_impl_304_, 2);
v_isSharedCheck_415_ = !lean_is_exclusive(v_impl_304_);
if (v_isSharedCheck_415_ == 0)
{
lean_object* v_unused_416_; lean_object* v_unused_417_; 
v_unused_416_ = lean_ctor_get(v_impl_304_, 3);
lean_dec(v_unused_416_);
v_unused_417_ = lean_ctor_get(v_impl_304_, 0);
lean_dec(v_unused_417_);
v___x_394_ = v_impl_304_;
v_isShared_395_ = v_isSharedCheck_415_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_r_390_);
lean_inc(v_v_392_);
lean_inc(v_k_391_);
lean_dec(v_impl_304_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_415_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v_k_396_; lean_object* v_v_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_411_; 
v_k_396_ = lean_ctor_get(v_l_389_, 1);
v_v_397_ = lean_ctor_get(v_l_389_, 2);
v_isSharedCheck_411_ = !lean_is_exclusive(v_l_389_);
if (v_isSharedCheck_411_ == 0)
{
lean_object* v_unused_412_; lean_object* v_unused_413_; lean_object* v_unused_414_; 
v_unused_412_ = lean_ctor_get(v_l_389_, 4);
lean_dec(v_unused_412_);
v_unused_413_ = lean_ctor_get(v_l_389_, 3);
lean_dec(v_unused_413_);
v_unused_414_ = lean_ctor_get(v_l_389_, 0);
lean_dec(v_unused_414_);
v___x_399_ = v_l_389_;
v_isShared_400_ = v_isSharedCheck_411_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_v_397_);
lean_inc(v_k_396_);
lean_dec(v_l_389_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_411_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_401_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_390_, 2);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 4, v_r_390_);
lean_ctor_set(v___x_399_, 3, v_r_390_);
lean_ctor_set(v___x_399_, 2, v_v_296_);
lean_ctor_set(v___x_399_, 1, v_k_295_);
lean_ctor_set(v___x_399_, 0, v___x_305_);
v___x_403_ = v___x_399_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_k_295_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v_v_296_);
lean_ctor_set(v_reuseFailAlloc_410_, 3, v_r_390_);
lean_ctor_set(v_reuseFailAlloc_410_, 4, v_r_390_);
v___x_403_ = v_reuseFailAlloc_410_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_405_; 
lean_inc(v_r_390_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 3, v_r_390_);
lean_ctor_set(v___x_394_, 0, v___x_305_);
v___x_405_ = v___x_394_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_k_391_);
lean_ctor_set(v_reuseFailAlloc_409_, 2, v_v_392_);
lean_ctor_set(v_reuseFailAlloc_409_, 3, v_r_390_);
lean_ctor_set(v_reuseFailAlloc_409_, 4, v_r_390_);
v___x_405_ = v_reuseFailAlloc_409_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_407_; 
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 4, v___x_405_);
lean_ctor_set(v___x_300_, 3, v___x_403_);
lean_ctor_set(v___x_300_, 2, v_v_397_);
lean_ctor_set(v___x_300_, 1, v_k_396_);
lean_ctor_set(v___x_300_, 0, v___x_401_);
v___x_407_ = v___x_300_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_401_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_k_396_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_v_397_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_408_, 4, v___x_405_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
}
}
else
{
lean_object* v_r_418_; 
v_r_418_ = lean_ctor_get(v_impl_304_, 4);
lean_inc(v_r_418_);
if (lean_obj_tag(v_r_418_) == 0)
{
lean_object* v_k_419_; lean_object* v_v_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_431_; 
v_k_419_ = lean_ctor_get(v_impl_304_, 1);
v_v_420_ = lean_ctor_get(v_impl_304_, 2);
v_isSharedCheck_431_ = !lean_is_exclusive(v_impl_304_);
if (v_isSharedCheck_431_ == 0)
{
lean_object* v_unused_432_; lean_object* v_unused_433_; lean_object* v_unused_434_; 
v_unused_432_ = lean_ctor_get(v_impl_304_, 4);
lean_dec(v_unused_432_);
v_unused_433_ = lean_ctor_get(v_impl_304_, 3);
lean_dec(v_unused_433_);
v_unused_434_ = lean_ctor_get(v_impl_304_, 0);
lean_dec(v_unused_434_);
v___x_422_ = v_impl_304_;
v_isShared_423_ = v_isSharedCheck_431_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_v_420_);
lean_inc(v_k_419_);
lean_dec(v_impl_304_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_431_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; lean_object* v___x_426_; 
v___x_424_ = lean_unsigned_to_nat(3u);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 4, v_l_389_);
lean_ctor_set(v___x_422_, 2, v_v_296_);
lean_ctor_set(v___x_422_, 1, v_k_295_);
lean_ctor_set(v___x_422_, 0, v___x_305_);
v___x_426_ = v___x_422_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_k_295_);
lean_ctor_set(v_reuseFailAlloc_430_, 2, v_v_296_);
lean_ctor_set(v_reuseFailAlloc_430_, 3, v_l_389_);
lean_ctor_set(v_reuseFailAlloc_430_, 4, v_l_389_);
v___x_426_ = v_reuseFailAlloc_430_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_428_; 
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 4, v_r_418_);
lean_ctor_set(v___x_300_, 3, v___x_426_);
lean_ctor_set(v___x_300_, 2, v_v_420_);
lean_ctor_set(v___x_300_, 1, v_k_419_);
lean_ctor_set(v___x_300_, 0, v___x_424_);
v___x_428_ = v___x_300_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_424_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_k_419_);
lean_ctor_set(v_reuseFailAlloc_429_, 2, v_v_420_);
lean_ctor_set(v_reuseFailAlloc_429_, 3, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_429_, 4, v_r_418_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
else
{
lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_435_ = lean_unsigned_to_nat(2u);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 4, v_impl_304_);
lean_ctor_set(v___x_300_, 3, v_r_418_);
lean_ctor_set(v___x_300_, 0, v___x_435_);
v___x_437_ = v___x_300_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_435_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_k_295_);
lean_ctor_set(v_reuseFailAlloc_438_, 2, v_v_296_);
lean_ctor_set(v_reuseFailAlloc_438_, 3, v_r_418_);
lean_ctor_set(v_reuseFailAlloc_438_, 4, v_impl_304_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
}
else
{
lean_object* v___x_440_; 
lean_dec(v_v_296_);
lean_dec(v_k_295_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 2, v_v_292_);
lean_ctor_set(v___x_300_, 1, v_k_291_);
v___x_440_ = v___x_300_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_size_294_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_k_291_);
lean_ctor_set(v_reuseFailAlloc_441_, 2, v_v_292_);
lean_ctor_set(v_reuseFailAlloc_441_, 3, v_l_297_);
lean_ctor_set(v_reuseFailAlloc_441_, 4, v_r_298_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
else
{
lean_object* v_impl_442_; lean_object* v___x_443_; 
lean_dec(v_size_294_);
v_impl_442_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_k_291_, v_v_292_, v_l_297_);
v___x_443_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_298_) == 0)
{
lean_object* v_size_444_; lean_object* v_size_445_; lean_object* v_k_446_; lean_object* v_v_447_; lean_object* v_l_448_; lean_object* v_r_449_; lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v_size_444_ = lean_ctor_get(v_r_298_, 0);
v_size_445_ = lean_ctor_get(v_impl_442_, 0);
lean_inc(v_size_445_);
v_k_446_ = lean_ctor_get(v_impl_442_, 1);
lean_inc(v_k_446_);
v_v_447_ = lean_ctor_get(v_impl_442_, 2);
lean_inc(v_v_447_);
v_l_448_ = lean_ctor_get(v_impl_442_, 3);
lean_inc(v_l_448_);
v_r_449_ = lean_ctor_get(v_impl_442_, 4);
lean_inc(v_r_449_);
v___x_450_ = lean_unsigned_to_nat(3u);
v___x_451_ = lean_nat_mul(v___x_450_, v_size_444_);
v___x_452_ = lean_nat_dec_lt(v___x_451_, v_size_445_);
lean_dec(v___x_451_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_456_; 
lean_dec(v_r_449_);
lean_dec(v_l_448_);
lean_dec(v_v_447_);
lean_dec(v_k_446_);
v___x_453_ = lean_nat_add(v___x_443_, v_size_445_);
lean_dec(v_size_445_);
v___x_454_ = lean_nat_add(v___x_453_, v_size_444_);
lean_dec(v___x_453_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 3, v_impl_442_);
lean_ctor_set(v___x_300_, 0, v___x_454_);
v___x_456_ = v___x_300_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_k_295_);
lean_ctor_set(v_reuseFailAlloc_457_, 2, v_v_296_);
lean_ctor_set(v_reuseFailAlloc_457_, 3, v_impl_442_);
lean_ctor_set(v_reuseFailAlloc_457_, 4, v_r_298_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
else
{
lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_523_; 
v_isSharedCheck_523_ = !lean_is_exclusive(v_impl_442_);
if (v_isSharedCheck_523_ == 0)
{
lean_object* v_unused_524_; lean_object* v_unused_525_; lean_object* v_unused_526_; lean_object* v_unused_527_; lean_object* v_unused_528_; 
v_unused_524_ = lean_ctor_get(v_impl_442_, 4);
lean_dec(v_unused_524_);
v_unused_525_ = lean_ctor_get(v_impl_442_, 3);
lean_dec(v_unused_525_);
v_unused_526_ = lean_ctor_get(v_impl_442_, 2);
lean_dec(v_unused_526_);
v_unused_527_ = lean_ctor_get(v_impl_442_, 1);
lean_dec(v_unused_527_);
v_unused_528_ = lean_ctor_get(v_impl_442_, 0);
lean_dec(v_unused_528_);
v___x_459_ = v_impl_442_;
v_isShared_460_ = v_isSharedCheck_523_;
goto v_resetjp_458_;
}
else
{
lean_dec(v_impl_442_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_523_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v_size_461_; lean_object* v_size_462_; lean_object* v_k_463_; lean_object* v_v_464_; lean_object* v_l_465_; lean_object* v_r_466_; lean_object* v___x_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
v_size_461_ = lean_ctor_get(v_l_448_, 0);
v_size_462_ = lean_ctor_get(v_r_449_, 0);
v_k_463_ = lean_ctor_get(v_r_449_, 1);
v_v_464_ = lean_ctor_get(v_r_449_, 2);
v_l_465_ = lean_ctor_get(v_r_449_, 3);
v_r_466_ = lean_ctor_get(v_r_449_, 4);
v___x_467_ = lean_unsigned_to_nat(2u);
v___x_468_ = lean_nat_mul(v___x_467_, v_size_461_);
v___x_469_ = lean_nat_dec_lt(v_size_462_, v___x_468_);
lean_dec(v___x_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_498_; 
lean_inc(v_r_466_);
lean_inc(v_l_465_);
lean_inc(v_v_464_);
lean_inc(v_k_463_);
v_isSharedCheck_498_ = !lean_is_exclusive(v_r_449_);
if (v_isSharedCheck_498_ == 0)
{
lean_object* v_unused_499_; lean_object* v_unused_500_; lean_object* v_unused_501_; lean_object* v_unused_502_; lean_object* v_unused_503_; 
v_unused_499_ = lean_ctor_get(v_r_449_, 4);
lean_dec(v_unused_499_);
v_unused_500_ = lean_ctor_get(v_r_449_, 3);
lean_dec(v_unused_500_);
v_unused_501_ = lean_ctor_get(v_r_449_, 2);
lean_dec(v_unused_501_);
v_unused_502_ = lean_ctor_get(v_r_449_, 1);
lean_dec(v_unused_502_);
v_unused_503_ = lean_ctor_get(v_r_449_, 0);
lean_dec(v_unused_503_);
v___x_471_ = v_r_449_;
v_isShared_472_ = v_isSharedCheck_498_;
goto v_resetjp_470_;
}
else
{
lean_dec(v_r_449_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_498_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___x_486_; lean_object* v___y_488_; 
v___x_473_ = lean_nat_add(v___x_443_, v_size_445_);
lean_dec(v_size_445_);
v___x_474_ = lean_nat_add(v___x_473_, v_size_444_);
lean_dec(v___x_473_);
v___x_486_ = lean_nat_add(v___x_443_, v_size_461_);
if (lean_obj_tag(v_l_465_) == 0)
{
lean_object* v_size_496_; 
v_size_496_ = lean_ctor_get(v_l_465_, 0);
lean_inc(v_size_496_);
v___y_488_ = v_size_496_;
goto v___jp_487_;
}
else
{
lean_object* v___x_497_; 
v___x_497_ = lean_unsigned_to_nat(0u);
v___y_488_ = v___x_497_;
goto v___jp_487_;
}
v___jp_475_:
{
lean_object* v___x_479_; lean_object* v___x_481_; 
v___x_479_ = lean_nat_add(v___y_477_, v___y_478_);
lean_dec(v___y_478_);
lean_dec(v___y_477_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 4, v_r_298_);
lean_ctor_set(v___x_471_, 3, v_r_466_);
lean_ctor_set(v___x_471_, 2, v_v_296_);
lean_ctor_set(v___x_471_, 1, v_k_295_);
lean_ctor_set(v___x_471_, 0, v___x_479_);
v___x_481_ = v___x_471_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v_k_295_);
lean_ctor_set(v_reuseFailAlloc_485_, 2, v_v_296_);
lean_ctor_set(v_reuseFailAlloc_485_, 3, v_r_466_);
lean_ctor_set(v_reuseFailAlloc_485_, 4, v_r_298_);
v___x_481_ = v_reuseFailAlloc_485_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
lean_object* v___x_483_; 
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 4, v___x_481_);
lean_ctor_set(v___x_459_, 3, v___y_476_);
lean_ctor_set(v___x_459_, 2, v_v_464_);
lean_ctor_set(v___x_459_, 1, v_k_463_);
lean_ctor_set(v___x_459_, 0, v___x_474_);
v___x_483_ = v___x_459_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_k_463_);
lean_ctor_set(v_reuseFailAlloc_484_, 2, v_v_464_);
lean_ctor_set(v_reuseFailAlloc_484_, 3, v___y_476_);
lean_ctor_set(v_reuseFailAlloc_484_, 4, v___x_481_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
v___jp_487_:
{
lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_489_ = lean_nat_add(v___x_486_, v___y_488_);
lean_dec(v___y_488_);
lean_dec(v___x_486_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 4, v_l_465_);
lean_ctor_set(v___x_300_, 3, v_l_448_);
lean_ctor_set(v___x_300_, 2, v_v_447_);
lean_ctor_set(v___x_300_, 1, v_k_446_);
lean_ctor_set(v___x_300_, 0, v___x_489_);
v___x_491_ = v___x_300_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_k_446_);
lean_ctor_set(v_reuseFailAlloc_495_, 2, v_v_447_);
lean_ctor_set(v_reuseFailAlloc_495_, 3, v_l_448_);
lean_ctor_set(v_reuseFailAlloc_495_, 4, v_l_465_);
v___x_491_ = v_reuseFailAlloc_495_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_492_; 
v___x_492_ = lean_nat_add(v___x_443_, v_size_444_);
if (lean_obj_tag(v_r_466_) == 0)
{
lean_object* v_size_493_; 
v_size_493_ = lean_ctor_get(v_r_466_, 0);
lean_inc(v_size_493_);
v___y_476_ = v___x_491_;
v___y_477_ = v___x_492_;
v___y_478_ = v_size_493_;
goto v___jp_475_;
}
else
{
lean_object* v___x_494_; 
v___x_494_ = lean_unsigned_to_nat(0u);
v___y_476_ = v___x_491_;
v___y_477_ = v___x_492_;
v___y_478_ = v___x_494_;
goto v___jp_475_;
}
}
}
}
}
else
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_509_; 
lean_del_object(v___x_300_);
v___x_504_ = lean_nat_add(v___x_443_, v_size_445_);
lean_dec(v_size_445_);
v___x_505_ = lean_nat_add(v___x_504_, v_size_444_);
lean_dec(v___x_504_);
v___x_506_ = lean_nat_add(v___x_443_, v_size_444_);
v___x_507_ = lean_nat_add(v___x_506_, v_size_462_);
lean_dec(v___x_506_);
lean_inc_ref(v_r_298_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 4, v_r_298_);
lean_ctor_set(v___x_459_, 3, v_r_449_);
lean_ctor_set(v___x_459_, 2, v_v_296_);
lean_ctor_set(v___x_459_, 1, v_k_295_);
lean_ctor_set(v___x_459_, 0, v___x_507_);
v___x_509_ = v___x_459_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_k_295_);
lean_ctor_set(v_reuseFailAlloc_522_, 2, v_v_296_);
lean_ctor_set(v_reuseFailAlloc_522_, 3, v_r_449_);
lean_ctor_set(v_reuseFailAlloc_522_, 4, v_r_298_);
v___x_509_ = v_reuseFailAlloc_522_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
v_isSharedCheck_516_ = !lean_is_exclusive(v_r_298_);
if (v_isSharedCheck_516_ == 0)
{
lean_object* v_unused_517_; lean_object* v_unused_518_; lean_object* v_unused_519_; lean_object* v_unused_520_; lean_object* v_unused_521_; 
v_unused_517_ = lean_ctor_get(v_r_298_, 4);
lean_dec(v_unused_517_);
v_unused_518_ = lean_ctor_get(v_r_298_, 3);
lean_dec(v_unused_518_);
v_unused_519_ = lean_ctor_get(v_r_298_, 2);
lean_dec(v_unused_519_);
v_unused_520_ = lean_ctor_get(v_r_298_, 1);
lean_dec(v_unused_520_);
v_unused_521_ = lean_ctor_get(v_r_298_, 0);
lean_dec(v_unused_521_);
v___x_511_ = v_r_298_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_dec(v_r_298_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 4, v___x_509_);
lean_ctor_set(v___x_511_, 3, v_l_448_);
lean_ctor_set(v___x_511_, 2, v_v_447_);
lean_ctor_set(v___x_511_, 1, v_k_446_);
lean_ctor_set(v___x_511_, 0, v___x_505_);
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_k_446_);
lean_ctor_set(v_reuseFailAlloc_515_, 2, v_v_447_);
lean_ctor_set(v_reuseFailAlloc_515_, 3, v_l_448_);
lean_ctor_set(v_reuseFailAlloc_515_, 4, v___x_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_529_; 
v_l_529_ = lean_ctor_get(v_impl_442_, 3);
lean_inc(v_l_529_);
if (lean_obj_tag(v_l_529_) == 0)
{
lean_object* v_r_530_; lean_object* v_k_531_; lean_object* v_v_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_543_; 
v_r_530_ = lean_ctor_get(v_impl_442_, 4);
v_k_531_ = lean_ctor_get(v_impl_442_, 1);
v_v_532_ = lean_ctor_get(v_impl_442_, 2);
v_isSharedCheck_543_ = !lean_is_exclusive(v_impl_442_);
if (v_isSharedCheck_543_ == 0)
{
lean_object* v_unused_544_; lean_object* v_unused_545_; 
v_unused_544_ = lean_ctor_get(v_impl_442_, 3);
lean_dec(v_unused_544_);
v_unused_545_ = lean_ctor_get(v_impl_442_, 0);
lean_dec(v_unused_545_);
v___x_534_ = v_impl_442_;
v_isShared_535_ = v_isSharedCheck_543_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_r_530_);
lean_inc(v_v_532_);
lean_inc(v_k_531_);
lean_dec(v_impl_442_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_543_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_536_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_530_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 3, v_r_530_);
lean_ctor_set(v___x_534_, 2, v_v_296_);
lean_ctor_set(v___x_534_, 1, v_k_295_);
lean_ctor_set(v___x_534_, 0, v___x_443_);
v___x_538_ = v___x_534_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_443_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_k_295_);
lean_ctor_set(v_reuseFailAlloc_542_, 2, v_v_296_);
lean_ctor_set(v_reuseFailAlloc_542_, 3, v_r_530_);
lean_ctor_set(v_reuseFailAlloc_542_, 4, v_r_530_);
v___x_538_ = v_reuseFailAlloc_542_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_540_; 
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 4, v___x_538_);
lean_ctor_set(v___x_300_, 3, v_l_529_);
lean_ctor_set(v___x_300_, 2, v_v_532_);
lean_ctor_set(v___x_300_, 1, v_k_531_);
lean_ctor_set(v___x_300_, 0, v___x_536_);
v___x_540_ = v___x_300_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_k_531_);
lean_ctor_set(v_reuseFailAlloc_541_, 2, v_v_532_);
lean_ctor_set(v_reuseFailAlloc_541_, 3, v_l_529_);
lean_ctor_set(v_reuseFailAlloc_541_, 4, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
else
{
lean_object* v_r_546_; 
v_r_546_ = lean_ctor_get(v_impl_442_, 4);
lean_inc(v_r_546_);
if (lean_obj_tag(v_r_546_) == 0)
{
lean_object* v_k_547_; lean_object* v_v_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_571_; 
v_k_547_ = lean_ctor_get(v_impl_442_, 1);
v_v_548_ = lean_ctor_get(v_impl_442_, 2);
v_isSharedCheck_571_ = !lean_is_exclusive(v_impl_442_);
if (v_isSharedCheck_571_ == 0)
{
lean_object* v_unused_572_; lean_object* v_unused_573_; lean_object* v_unused_574_; 
v_unused_572_ = lean_ctor_get(v_impl_442_, 4);
lean_dec(v_unused_572_);
v_unused_573_ = lean_ctor_get(v_impl_442_, 3);
lean_dec(v_unused_573_);
v_unused_574_ = lean_ctor_get(v_impl_442_, 0);
lean_dec(v_unused_574_);
v___x_550_ = v_impl_442_;
v_isShared_551_ = v_isSharedCheck_571_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_v_548_);
lean_inc(v_k_547_);
lean_dec(v_impl_442_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_571_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v_k_552_; lean_object* v_v_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_567_; 
v_k_552_ = lean_ctor_get(v_r_546_, 1);
v_v_553_ = lean_ctor_get(v_r_546_, 2);
v_isSharedCheck_567_ = !lean_is_exclusive(v_r_546_);
if (v_isSharedCheck_567_ == 0)
{
lean_object* v_unused_568_; lean_object* v_unused_569_; lean_object* v_unused_570_; 
v_unused_568_ = lean_ctor_get(v_r_546_, 4);
lean_dec(v_unused_568_);
v_unused_569_ = lean_ctor_get(v_r_546_, 3);
lean_dec(v_unused_569_);
v_unused_570_ = lean_ctor_get(v_r_546_, 0);
lean_dec(v_unused_570_);
v___x_555_ = v_r_546_;
v_isShared_556_ = v_isSharedCheck_567_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_v_553_);
lean_inc(v_k_552_);
lean_dec(v_r_546_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_567_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_557_ = lean_unsigned_to_nat(3u);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 4, v_l_529_);
lean_ctor_set(v___x_555_, 3, v_l_529_);
lean_ctor_set(v___x_555_, 2, v_v_548_);
lean_ctor_set(v___x_555_, 1, v_k_547_);
lean_ctor_set(v___x_555_, 0, v___x_443_);
v___x_559_ = v___x_555_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_443_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_k_547_);
lean_ctor_set(v_reuseFailAlloc_566_, 2, v_v_548_);
lean_ctor_set(v_reuseFailAlloc_566_, 3, v_l_529_);
lean_ctor_set(v_reuseFailAlloc_566_, 4, v_l_529_);
v___x_559_ = v_reuseFailAlloc_566_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_561_; 
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 4, v_l_529_);
lean_ctor_set(v___x_550_, 2, v_v_296_);
lean_ctor_set(v___x_550_, 1, v_k_295_);
lean_ctor_set(v___x_550_, 0, v___x_443_);
v___x_561_ = v___x_550_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_443_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_k_295_);
lean_ctor_set(v_reuseFailAlloc_565_, 2, v_v_296_);
lean_ctor_set(v_reuseFailAlloc_565_, 3, v_l_529_);
lean_ctor_set(v_reuseFailAlloc_565_, 4, v_l_529_);
v___x_561_ = v_reuseFailAlloc_565_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_object* v___x_563_; 
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 4, v___x_561_);
lean_ctor_set(v___x_300_, 3, v___x_559_);
lean_ctor_set(v___x_300_, 2, v_v_553_);
lean_ctor_set(v___x_300_, 1, v_k_552_);
lean_ctor_set(v___x_300_, 0, v___x_557_);
v___x_563_ = v___x_300_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_k_552_);
lean_ctor_set(v_reuseFailAlloc_564_, 2, v_v_553_);
lean_ctor_set(v_reuseFailAlloc_564_, 3, v___x_559_);
lean_ctor_set(v_reuseFailAlloc_564_, 4, v___x_561_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
}
}
else
{
lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_575_ = lean_unsigned_to_nat(2u);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 4, v_r_546_);
lean_ctor_set(v___x_300_, 3, v_impl_442_);
lean_ctor_set(v___x_300_, 0, v___x_575_);
v___x_577_ = v___x_300_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_k_295_);
lean_ctor_set(v_reuseFailAlloc_578_, 2, v_v_296_);
lean_ctor_set(v_reuseFailAlloc_578_, 3, v_impl_442_);
lean_ctor_set(v_reuseFailAlloc_578_, 4, v_r_546_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_unsigned_to_nat(1u);
v___x_581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v_k_291_);
lean_ctor_set(v___x_581_, 2, v_v_292_);
lean_ctor_set(v___x_581_, 3, v_t_293_);
lean_ctor_set(v___x_581_, 4, v_t_293_);
return v___x_581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange(lean_object* v_p_582_, uint8_t v_d_583_, lean_object* v_00_u03b4_584_){
_start:
{
lean_object* v_changesBefore_585_; lean_object* v_changesAfter_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_595_; 
v_changesBefore_585_ = lean_ctor_get(v_00_u03b4_584_, 0);
v_changesAfter_586_ = lean_ctor_get(v_00_u03b4_584_, 1);
v_isSharedCheck_595_ = !lean_is_exclusive(v_00_u03b4_584_);
if (v_isSharedCheck_595_ == 0)
{
v___x_588_ = v_00_u03b4_584_;
v_isShared_589_ = v_isSharedCheck_595_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_changesAfter_586_);
lean_inc(v_changesBefore_585_);
lean_dec(v_00_u03b4_584_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_595_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_590_ = lean_box(v_d_583_);
v___x_591_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_p_582_, v___x_590_, v_changesBefore_585_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v___x_591_);
v___x_593_ = v___x_588_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_changesAfter_586_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange___boxed(lean_object* v_p_596_, lean_object* v_d_597_, lean_object* v_00_u03b4_598_){
_start:
{
uint8_t v_d_boxed_599_; lean_object* v_res_600_; 
v_d_boxed_599_ = lean_unbox(v_d_597_);
v_res_600_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange(v_p_596_, v_d_boxed_599_, v_00_u03b4_598_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0(lean_object* v_00_u03b2_601_, lean_object* v_k_602_, lean_object* v_v_603_, lean_object* v_t_604_, lean_object* v_hl_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_k_602_, v_v_603_, v_t_604_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertAfterChange(lean_object* v_p_607_, uint8_t v_d_608_, lean_object* v_00_u03b4_609_){
_start:
{
lean_object* v_changesBefore_610_; lean_object* v_changesAfter_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_620_; 
v_changesBefore_610_ = lean_ctor_get(v_00_u03b4_609_, 0);
v_changesAfter_611_ = lean_ctor_get(v_00_u03b4_609_, 1);
v_isSharedCheck_620_ = !lean_is_exclusive(v_00_u03b4_609_);
if (v_isSharedCheck_620_ == 0)
{
v___x_613_ = v_00_u03b4_609_;
v_isShared_614_ = v_isSharedCheck_620_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_changesAfter_611_);
lean_inc(v_changesBefore_610_);
lean_dec(v_00_u03b4_609_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_620_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_618_; 
v___x_615_ = lean_box(v_d_608_);
v___x_616_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_p_607_, v___x_615_, v_changesAfter_611_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 1, v___x_616_);
v___x_618_ = v___x_613_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_changesBefore_610_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v___x_616_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertAfterChange___boxed(lean_object* v_p_621_, lean_object* v_d_622_, lean_object* v_00_u03b4_623_){
_start:
{
uint8_t v_d_boxed_624_; lean_object* v_res_625_; 
v_d_boxed_624_ = lean_unbox(v_d_622_);
v_res_625_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertAfterChange(v_p_621_, v_d_boxed_624_, v_00_u03b4_623_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(lean_object* v_before_626_, lean_object* v_after_627_, uint8_t v_d_628_){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_629_ = lean_box(1);
v___x_630_ = lean_box(v_d_628_);
v___x_631_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_before_626_, v___x_630_, v___x_629_);
v___x_632_ = lean_box(v_d_628_);
v___x_633_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_after_627_, v___x_632_, v___x_629_);
v___x_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_631_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos___boxed(lean_object* v_before_635_, lean_object* v_after_636_, lean_object* v_d_637_){
_start:
{
uint8_t v_d_boxed_638_; lean_object* v_res_639_; 
v_d_boxed_638_ = lean_unbox(v_d_637_);
v_res_639_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v_before_635_, v_after_636_, v_d_boxed_638_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(lean_object* v_before_640_, lean_object* v_after_641_, uint8_t v_d_642_){
_start:
{
lean_object* v_pos_643_; lean_object* v_pos_644_; lean_object* v___x_645_; 
v_pos_643_ = lean_ctor_get(v_before_640_, 1);
lean_inc(v_pos_643_);
lean_dec_ref(v_before_640_);
v_pos_644_ = lean_ctor_get(v_after_641_, 1);
lean_inc(v_pos_644_);
lean_dec_ref(v_after_641_);
v___x_645_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v_pos_643_, v_pos_644_, v_d_642_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange___boxed(lean_object* v_before_646_, lean_object* v_after_647_, lean_object* v_d_648_){
_start:
{
uint8_t v_d_boxed_649_; lean_object* v_res_650_; 
v_d_boxed_649_ = lean_unbox(v_d_648_);
v_res_650_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_646_, v_after_647_, v_d_boxed_649_);
return v_res_650_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(lean_object* v_d_651_){
_start:
{
lean_object* v_changesAfter_652_; 
v_changesAfter_652_ = lean_ctor_get(v_d_651_, 1);
if (lean_obj_tag(v_changesAfter_652_) == 0)
{
uint8_t v___x_653_; 
v___x_653_ = 0;
return v___x_653_;
}
else
{
lean_object* v_changesBefore_654_; 
v_changesBefore_654_ = lean_ctor_get(v_d_651_, 0);
if (lean_obj_tag(v_changesBefore_654_) == 0)
{
uint8_t v___x_655_; 
v___x_655_ = 0;
return v___x_655_;
}
else
{
uint8_t v___x_656_; 
v___x_656_ = 1;
return v___x_656_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty___boxed(lean_object* v_d_657_){
_start:
{
uint8_t v_res_658_; lean_object* v_r_659_; 
v_res_658_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_d_657_);
lean_dec_ref(v_d_657_);
v_r_659_ = lean_box(v_res_658_);
return v_r_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0(lean_object* v_k_660_, lean_object* v_b_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v___x_667_; 
lean_inc(v___y_665_);
lean_inc_ref(v___y_664_);
lean_inc(v___y_663_);
lean_inc_ref(v___y_662_);
v___x_667_ = lean_apply_6(v_k_660_, v_b_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, lean_box(0));
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0___boxed(lean_object* v_k_668_, lean_object* v_b_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0(v_k_668_, v_b_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(lean_object* v_name_676_, uint8_t v_bi_677_, lean_object* v_type_678_, lean_object* v_k_679_, uint8_t v_kind_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v___f_686_; lean_object* v___x_687_; 
v___f_686_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_686_, 0, v_k_679_);
v___x_687_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_676_, v_bi_677_, v_type_678_, v___f_686_, v_kind_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_687_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
v_a_696_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_687_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_687_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___boxed(lean_object* v_name_704_, lean_object* v_bi_705_, lean_object* v_type_706_, lean_object* v_k_707_, lean_object* v_kind_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
uint8_t v_bi_boxed_714_; uint8_t v_kind_boxed_715_; lean_object* v_res_716_; 
v_bi_boxed_714_ = lean_unbox(v_bi_705_);
v_kind_boxed_715_ = lean_unbox(v_kind_708_);
v_res_716_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_name_704_, v_bi_boxed_714_, v_type_706_, v_k_707_, v_kind_boxed_715_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6(lean_object* v_00_u03b1_717_, lean_object* v_name_718_, uint8_t v_bi_719_, lean_object* v_type_720_, lean_object* v_k_721_, uint8_t v_kind_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_name_718_, v_bi_719_, v_type_720_, v_k_721_, v_kind_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___boxed(lean_object* v_00_u03b1_729_, lean_object* v_name_730_, lean_object* v_bi_731_, lean_object* v_type_732_, lean_object* v_k_733_, lean_object* v_kind_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
uint8_t v_bi_boxed_740_; uint8_t v_kind_boxed_741_; lean_object* v_res_742_; 
v_bi_boxed_740_ = lean_unbox(v_bi_731_);
v_kind_boxed_741_ = lean_unbox(v_kind_734_);
v_res_742_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6(v_00_u03b1_729_, v_name_730_, v_bi_boxed_740_, v_type_732_, v_k_733_, v_kind_boxed_741_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(lean_object* v_msgData_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v___x_749_; lean_object* v_env_750_; lean_object* v___x_751_; lean_object* v_mctx_752_; lean_object* v_lctx_753_; lean_object* v_options_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_749_ = lean_st_ref_get(v___y_747_);
v_env_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc_ref(v_env_750_);
lean_dec(v___x_749_);
v___x_751_ = lean_st_ref_get(v___y_745_);
v_mctx_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc_ref(v_mctx_752_);
lean_dec(v___x_751_);
v_lctx_753_ = lean_ctor_get(v___y_744_, 2);
v_options_754_ = lean_ctor_get(v___y_746_, 2);
lean_inc_ref(v_options_754_);
lean_inc_ref(v_lctx_753_);
v___x_755_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_755_, 0, v_env_750_);
lean_ctor_set(v___x_755_, 1, v_mctx_752_);
lean_ctor_set(v___x_755_, 2, v_lctx_753_);
lean_ctor_set(v___x_755_, 3, v_options_754_);
v___x_756_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
lean_ctor_set(v___x_756_, 1, v_msgData_743_);
v___x_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4___boxed(lean_object* v_msgData_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(v_msgData_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(lean_object* v_msg_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_ref_771_; lean_object* v___x_772_; lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_781_; 
v_ref_771_ = lean_ctor_get(v___y_768_, 5);
v___x_772_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(v_msg_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
v_a_773_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_781_ == 0)
{
v___x_775_ = v___x_772_;
v_isShared_776_ = v_isSharedCheck_781_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_772_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_781_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_777_; lean_object* v___x_779_; 
lean_inc(v_ref_771_);
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v_ref_771_);
lean_ctor_set(v___x_777_, 1, v_a_773_);
if (v_isShared_776_ == 0)
{
lean_ctor_set_tag(v___x_775_, 1);
lean_ctor_set(v___x_775_, 0, v___x_777_);
v___x_779_ = v___x_775_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_777_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg___boxed(lean_object* v_msg_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v_msg_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(lean_object* v_x_789_, lean_object* v_x_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
if (lean_obj_tag(v_x_789_) == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = l_List_reverse___redArg(v_x_790_);
v___x_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
return v___x_797_;
}
else
{
lean_object* v_head_798_; lean_object* v_tail_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_817_; 
v_head_798_ = lean_ctor_get(v_x_789_, 0);
v_tail_799_ = lean_ctor_get(v_x_789_, 1);
v_isSharedCheck_817_ = !lean_is_exclusive(v_x_789_);
if (v_isSharedCheck_817_ == 0)
{
v___x_801_ = v_x_789_;
v_isShared_802_ = v_isSharedCheck_817_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_tail_799_);
lean_inc(v_head_798_);
lean_dec(v_x_789_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_817_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_Meta_getFVarFromUserName(v_head_798_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v___x_806_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref(v___x_803_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 1, v_x_790_);
lean_ctor_set(v___x_801_, 0, v_a_804_);
v___x_806_ = v___x_801_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_804_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_x_790_);
v___x_806_ = v_reuseFailAlloc_808_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
v_x_789_ = v_tail_799_;
v_x_790_ = v___x_806_;
goto _start;
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_del_object(v___x_801_);
lean_dec(v_tail_799_);
lean_dec(v_x_790_);
v_a_809_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_803_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_803_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2___boxed(lean_object* v_x_818_, lean_object* v_x_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(v_x_818_, v_x_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(lean_object* v_upperBound_826_, lean_object* v_before_827_, lean_object* v_a_828_, lean_object* v_b_829_){
_start:
{
uint8_t v___x_831_; 
v___x_831_ = lean_nat_dec_lt(v_a_828_, v_upperBound_826_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; 
lean_dec(v_a_828_);
lean_dec_ref(v_before_827_);
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v_b_829_);
return v___x_832_;
}
else
{
lean_object* v_pos_833_; lean_object* v___x_834_; uint8_t v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v_pos_833_ = lean_ctor_get(v_before_827_, 1);
lean_inc(v_pos_833_);
lean_inc(v_a_828_);
v___x_834_ = l_Lean_SubExpr_Pos_pushNthBindingDomain(v_a_828_, v_pos_833_);
v___x_835_ = 1;
v___x_836_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange(v___x_834_, v___x_835_, v_b_829_);
v___x_837_ = lean_unsigned_to_nat(1u);
v___x_838_ = lean_nat_add(v_a_828_, v___x_837_);
lean_dec(v_a_828_);
v_a_828_ = v___x_838_;
v_b_829_ = v___x_836_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg___boxed(lean_object* v_upperBound_840_, lean_object* v_before_841_, lean_object* v_a_842_, lean_object* v_b_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v_upperBound_840_, v_before_841_, v_a_842_, v_b_843_);
lean_dec(v_upperBound_840_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0(lean_object* v_x_846_, lean_object* v_x_847_){
_start:
{
if (lean_obj_tag(v_x_846_) == 0)
{
lean_object* v___x_848_; 
v___x_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_848_, 0, v_x_847_);
return v___x_848_;
}
else
{
if (lean_obj_tag(v_x_847_) == 0)
{
lean_object* v___x_849_; 
v___x_849_ = lean_box(0);
return v___x_849_;
}
else
{
lean_object* v_head_850_; lean_object* v_tail_851_; lean_object* v_head_852_; lean_object* v_tail_853_; uint8_t v___x_854_; 
v_head_850_ = lean_ctor_get(v_x_846_, 0);
v_tail_851_ = lean_ctor_get(v_x_846_, 1);
v_head_852_ = lean_ctor_get(v_x_847_, 0);
lean_inc(v_head_852_);
v_tail_853_ = lean_ctor_get(v_x_847_, 1);
lean_inc(v_tail_853_);
lean_dec_ref(v_x_847_);
v___x_854_ = lean_name_eq(v_head_850_, v_head_852_);
lean_dec(v_head_852_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; 
lean_dec(v_tail_853_);
v___x_855_ = lean_box(0);
return v___x_855_;
}
else
{
v_x_846_ = v_tail_851_;
v_x_847_ = v_tail_853_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0___boxed(lean_object* v_x_857_, lean_object* v_x_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0(v_x_857_, v_x_858_);
lean_dec(v_x_857_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0(lean_object* v_l_u2081_860_, lean_object* v_l_u2082_861_){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_862_ = l_List_reverse___redArg(v_l_u2081_860_);
v___x_863_ = l_List_reverse___redArg(v_l_u2082_861_);
v___x_864_ = l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0(v___x_862_, v___x_863_);
lean_dec(v___x_862_);
if (lean_obj_tag(v___x_864_) == 0)
{
return v___x_864_;
}
else
{
lean_object* v_val_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_873_; 
v_val_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_873_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_873_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_val_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_873_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_869_ = l_List_reverse___redArg(v_val_865_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_869_);
v___x_871_ = v___x_867_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(uint8_t v_b_u2082_874_, lean_object* v_k_875_, lean_object* v_t_876_){
_start:
{
if (lean_obj_tag(v_t_876_) == 0)
{
lean_object* v_size_877_; lean_object* v_k_878_; lean_object* v_v_879_; lean_object* v_l_880_; lean_object* v_r_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_895_; 
v_size_877_ = lean_ctor_get(v_t_876_, 0);
v_k_878_ = lean_ctor_get(v_t_876_, 1);
v_v_879_ = lean_ctor_get(v_t_876_, 2);
v_l_880_ = lean_ctor_get(v_t_876_, 3);
v_r_881_ = lean_ctor_get(v_t_876_, 4);
v_isSharedCheck_895_ = !lean_is_exclusive(v_t_876_);
if (v_isSharedCheck_895_ == 0)
{
v___x_883_ = v_t_876_;
v_isShared_884_ = v_isSharedCheck_895_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_r_881_);
lean_inc(v_l_880_);
lean_inc(v_v_879_);
lean_inc(v_k_878_);
lean_inc(v_size_877_);
lean_dec(v_t_876_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_895_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
uint8_t v___x_885_; 
v___x_885_ = lean_nat_dec_lt(v_k_875_, v_k_878_);
if (v___x_885_ == 0)
{
uint8_t v___x_886_; 
v___x_886_ = lean_nat_dec_eq(v_k_875_, v_k_878_);
if (v___x_886_ == 0)
{
lean_object* v_impl_887_; lean_object* v___x_888_; 
lean_del_object(v___x_883_);
lean_dec(v_size_877_);
v_impl_887_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_874_, v_k_875_, v_r_881_);
v___x_888_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_878_, v_v_879_, v_l_880_, v_impl_887_);
return v___x_888_;
}
else
{
lean_object* v___x_889_; lean_object* v___x_891_; 
lean_dec(v_v_879_);
lean_dec(v_k_878_);
v___x_889_ = lean_box(v_b_u2082_874_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 2, v___x_889_);
lean_ctor_set(v___x_883_, 1, v_k_875_);
v___x_891_ = v___x_883_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_size_877_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_k_875_);
lean_ctor_set(v_reuseFailAlloc_892_, 2, v___x_889_);
lean_ctor_set(v_reuseFailAlloc_892_, 3, v_l_880_);
lean_ctor_set(v_reuseFailAlloc_892_, 4, v_r_881_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
else
{
lean_object* v_impl_893_; lean_object* v___x_894_; 
lean_del_object(v___x_883_);
lean_dec(v_size_877_);
v_impl_893_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_874_, v_k_875_, v_l_880_);
v___x_894_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_878_, v_v_879_, v_impl_893_, v_r_881_);
return v___x_894_;
}
}
}
else
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_896_ = lean_unsigned_to_nat(1u);
v___x_897_ = lean_box(v_b_u2082_874_);
v___x_898_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set(v___x_898_, 1, v_k_875_);
lean_ctor_set(v___x_898_, 2, v___x_897_);
lean_ctor_set(v___x_898_, 3, v_t_876_);
lean_ctor_set(v___x_898_, 4, v_t_876_);
return v___x_898_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg___boxed(lean_object* v_b_u2082_899_, lean_object* v_k_900_, lean_object* v_t_901_){
_start:
{
uint8_t v_b_u2082_boxed_902_; lean_object* v_res_903_; 
v_b_u2082_boxed_902_ = lean_unbox(v_b_u2082_899_);
v_res_903_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_boxed_902_, v_k_900_, v_t_901_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(lean_object* v_init_904_, lean_object* v_x_905_){
_start:
{
if (lean_obj_tag(v_x_905_) == 0)
{
lean_object* v_k_906_; lean_object* v_v_907_; lean_object* v_l_908_; lean_object* v_r_909_; lean_object* v___x_910_; uint8_t v___x_911_; lean_object* v___x_912_; 
v_k_906_ = lean_ctor_get(v_x_905_, 1);
lean_inc(v_k_906_);
v_v_907_ = lean_ctor_get(v_x_905_, 2);
lean_inc(v_v_907_);
v_l_908_ = lean_ctor_get(v_x_905_, 3);
lean_inc(v_l_908_);
v_r_909_ = lean_ctor_get(v_x_905_, 4);
lean_inc(v_r_909_);
lean_dec_ref(v_x_905_);
v___x_910_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_init_904_, v_l_908_);
v___x_911_ = lean_unbox(v_v_907_);
lean_dec(v_v_907_);
v___x_912_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v___x_911_, v_k_906_, v___x_910_);
v_init_904_ = v___x_912_;
v_x_905_ = v_r_909_;
goto _start;
}
else
{
return v_init_904_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(lean_object* v_as_914_, size_t v_i_915_, size_t v_stop_916_, lean_object* v_b_917_){
_start:
{
uint8_t v___x_918_; 
v___x_918_ = lean_usize_dec_eq(v_i_915_, v_stop_916_);
if (v___x_918_ == 0)
{
lean_object* v_changesBefore_919_; lean_object* v_changesAfter_920_; lean_object* v___x_921_; lean_object* v_changesBefore_922_; lean_object* v_changesAfter_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_935_; 
v_changesBefore_919_ = lean_ctor_get(v_b_917_, 0);
lean_inc(v_changesBefore_919_);
v_changesAfter_920_ = lean_ctor_get(v_b_917_, 1);
lean_inc(v_changesAfter_920_);
lean_dec_ref(v_b_917_);
v___x_921_ = lean_array_uget(v_as_914_, v_i_915_);
v_changesBefore_922_ = lean_ctor_get(v___x_921_, 0);
v_changesAfter_923_ = lean_ctor_get(v___x_921_, 1);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_935_ == 0)
{
v___x_925_ = v___x_921_;
v_isShared_926_ = v_isSharedCheck_935_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_changesAfter_923_);
lean_inc(v_changesBefore_922_);
lean_dec(v___x_921_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_935_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_927_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesBefore_919_, v_changesBefore_922_);
v___x_928_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesAfter_920_, v_changesAfter_923_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 1, v___x_928_);
lean_ctor_set(v___x_925_, 0, v___x_927_);
v___x_930_ = v___x_925_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_927_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v___x_928_);
v___x_930_ = v_reuseFailAlloc_934_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
size_t v___x_931_; size_t v___x_932_; 
v___x_931_ = ((size_t)1ULL);
v___x_932_ = lean_usize_add(v_i_915_, v___x_931_);
v_i_915_ = v___x_932_;
v_b_917_ = v___x_930_;
goto _start;
}
}
}
else
{
return v_b_917_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10___boxed(lean_object* v_as_936_, lean_object* v_i_937_, lean_object* v_stop_938_, lean_object* v_b_939_){
_start:
{
size_t v_i_boxed_940_; size_t v_stop_boxed_941_; lean_object* v_res_942_; 
v_i_boxed_940_ = lean_unbox_usize(v_i_937_);
lean_dec(v_i_937_);
v_stop_boxed_941_ = lean_unbox_usize(v_stop_938_);
lean_dec(v_stop_938_);
v_res_942_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_as_936_, v_i_boxed_940_, v_stop_boxed_941_, v_b_939_);
lean_dec_ref(v_as_936_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(lean_object* v_x_943_, lean_object* v_x_944_, lean_object* v_x_945_){
_start:
{
if (lean_obj_tag(v_x_943_) == 5)
{
lean_object* v_fn_946_; lean_object* v_arg_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v_fn_946_ = lean_ctor_get(v_x_943_, 0);
lean_inc_ref(v_fn_946_);
v_arg_947_ = lean_ctor_get(v_x_943_, 1);
lean_inc_ref(v_arg_947_);
lean_dec_ref(v_x_943_);
v___x_948_ = lean_array_set(v_x_944_, v_x_945_, v_arg_947_);
v___x_949_ = lean_unsigned_to_nat(1u);
v___x_950_ = lean_nat_sub(v_x_945_, v___x_949_);
lean_dec(v_x_945_);
v_x_943_ = v_fn_946_;
v_x_944_ = v___x_948_;
v_x_945_ = v___x_950_;
goto _start;
}
else
{
lean_object* v___x_952_; 
lean_dec(v_x_945_);
v___x_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_952_, 0, v_x_943_);
lean_ctor_set(v___x_952_, 1, v_x_944_);
return v___x_952_;
}
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0(void){
_start:
{
lean_object* v___x_953_; lean_object* v_dummy_954_; 
v___x_953_ = lean_box(0);
v_dummy_954_ = l_Lean_Expr_sort___override(v___x_953_);
return v_dummy_954_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(lean_object* v_snd_955_, lean_object* v_before_956_, lean_object* v_after_957_, lean_object* v_as_958_, lean_object* v_i_959_, lean_object* v_j_960_, lean_object* v_bs_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v_zero_967_; uint8_t v_isZero_968_; 
v_zero_967_ = lean_unsigned_to_nat(0u);
v_isZero_968_ = lean_nat_dec_eq(v_i_959_, v_zero_967_);
if (v_isZero_968_ == 1)
{
lean_object* v___x_969_; 
lean_dec(v_j_960_);
lean_dec(v_i_959_);
v___x_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_969_, 0, v_bs_961_);
return v___x_969_;
}
else
{
lean_object* v___x_970_; lean_object* v_fst_971_; lean_object* v_snd_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_1000_; 
v___x_970_ = lean_array_fget(v_as_958_, v_j_960_);
v_fst_971_ = lean_ctor_get(v___x_970_, 0);
v_snd_972_ = lean_ctor_get(v___x_970_, 1);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_974_ = v___x_970_;
v_isShared_975_ = v_isSharedCheck_1000_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_snd_972_);
lean_inc(v_fst_971_);
lean_dec(v___x_970_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_1000_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v_pos_976_; lean_object* v_pos_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_981_; 
v_pos_976_ = lean_ctor_get(v_before_956_, 1);
v_pos_977_ = lean_ctor_get(v_after_957_, 1);
v___x_978_ = lean_array_get_size(v_snd_955_);
v___x_979_ = l_Lean_SubExpr_Pos_pushNaryArg(v___x_978_, v_j_960_, v_pos_976_);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 1, v___x_979_);
v___x_981_ = v___x_974_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_fst_971_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v___x_979_);
v___x_981_ = v_reuseFailAlloc_999_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_982_ = l_Lean_SubExpr_Pos_pushNaryArg(v___x_978_, v_j_960_, v_pos_977_);
v___x_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_983_, 0, v_snd_972_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_981_, v___x_983_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v_one_986_; lean_object* v_n_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref(v___x_984_);
v_one_986_ = lean_unsigned_to_nat(1u);
v_n_987_ = lean_nat_sub(v_i_959_, v_one_986_);
lean_dec(v_i_959_);
v___x_988_ = lean_nat_add(v_j_960_, v_one_986_);
lean_dec(v_j_960_);
v___x_989_ = lean_array_push(v_bs_961_, v_a_985_);
v_i_959_ = v_n_987_;
v_j_960_ = v___x_988_;
v_bs_961_ = v___x_989_;
goto _start;
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec_ref(v_bs_961_);
lean_dec(v_j_960_);
lean_dec(v_i_959_);
v_a_991_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_984_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_984_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__0));
v___x_1003_ = l_Lean_stringToMessageData(v___x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0___boxed(lean_object* v_body_1004_, lean_object* v_pos_1005_, lean_object* v_body_1006_, lean_object* v_pos_1007_, lean_object* v_x_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0(v_body_1004_, v_pos_1005_, v_body_1006_, v_pos_1007_, v_x_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec_ref(v_x_1008_);
lean_dec(v_pos_1007_);
lean_dec_ref(v_body_1006_);
lean_dec(v_pos_1005_);
lean_dec_ref(v_body_1004_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(lean_object* v_before_1015_, lean_object* v_after_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_){
_start:
{
lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v_a_1028_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; uint8_t v___y_1039_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v_a_1058_; lean_object* v_expr_1061_; lean_object* v_pos_1062_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; 
v_expr_1061_ = lean_ctor_get(v_before_1015_, 0);
v_pos_1062_ = lean_ctor_get(v_before_1015_, 1);
if (lean_obj_tag(v_expr_1061_) == 7)
{
lean_object* v_binderName_1099_; lean_object* v_binderType_1100_; lean_object* v_body_1101_; uint8_t v_binderInfo_1102_; lean_object* v_expr_1103_; lean_object* v_pos_1104_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; 
v_binderName_1099_ = lean_ctor_get(v_expr_1061_, 0);
v_binderType_1100_ = lean_ctor_get(v_expr_1061_, 1);
v_body_1101_ = lean_ctor_get(v_expr_1061_, 2);
v_binderInfo_1102_ = lean_ctor_get_uint8(v_expr_1061_, sizeof(void*)*3 + 8);
v_expr_1103_ = lean_ctor_get(v_after_1016_, 0);
v_pos_1104_ = lean_ctor_get(v_after_1016_, 1);
if (lean_obj_tag(v_expr_1103_) == 7)
{
lean_object* v_binderName_1130_; lean_object* v_binderType_1131_; lean_object* v_body_1132_; uint8_t v_binderInfo_1133_; lean_object* v___f_1134_; uint8_t v___y_1136_; uint8_t v___x_1186_; 
v_binderName_1130_ = lean_ctor_get(v_expr_1103_, 0);
v_binderType_1131_ = lean_ctor_get(v_expr_1103_, 1);
v_body_1132_ = lean_ctor_get(v_expr_1103_, 2);
v_binderInfo_1133_ = lean_ctor_get_uint8(v_expr_1103_, sizeof(void*)*3 + 8);
lean_inc(v_pos_1104_);
lean_inc_ref(v_body_1132_);
lean_inc(v_pos_1062_);
lean_inc_ref(v_body_1101_);
v___f_1134_ = lean_alloc_closure((void*)(l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1134_, 0, v_body_1101_);
lean_closure_set(v___f_1134_, 1, v_pos_1062_);
lean_closure_set(v___f_1134_, 2, v_body_1132_);
lean_closure_set(v___f_1134_, 3, v_pos_1104_);
v___x_1186_ = lean_name_eq(v_binderName_1099_, v_binderName_1130_);
if (v___x_1186_ == 0)
{
v___y_1136_ = v___x_1186_;
goto v___jp_1135_;
}
else
{
uint8_t v___x_1187_; 
v___x_1187_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1102_, v_binderInfo_1133_);
v___y_1136_ = v___x_1187_;
goto v___jp_1135_;
}
v___jp_1135_:
{
if (v___y_1136_ == 0)
{
lean_dec_ref(v___f_1134_);
v___y_1106_ = v_a_1017_;
v___y_1107_ = v_a_1018_;
v___y_1108_ = v_a_1019_;
v___y_1109_ = v_a_1020_;
goto v___jp_1105_;
}
else
{
lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1183_; 
lean_inc_ref(v_binderType_1131_);
lean_inc(v_pos_1104_);
lean_inc_ref(v_binderType_1100_);
lean_inc(v_binderName_1099_);
lean_inc(v_pos_1062_);
v_isSharedCheck_1183_ = !lean_is_exclusive(v_before_1015_);
if (v_isSharedCheck_1183_ == 0)
{
lean_object* v_unused_1184_; lean_object* v_unused_1185_; 
v_unused_1184_ = lean_ctor_get(v_before_1015_, 1);
lean_dec(v_unused_1184_);
v_unused_1185_ = lean_ctor_get(v_before_1015_, 0);
lean_dec(v_unused_1185_);
v___x_1138_ = v_before_1015_;
v_isShared_1139_ = v_isSharedCheck_1183_;
goto v_resetjp_1137_;
}
else
{
lean_dec(v_before_1015_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1183_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1180_; 
v_isSharedCheck_1180_ = !lean_is_exclusive(v_after_1016_);
if (v_isSharedCheck_1180_ == 0)
{
lean_object* v_unused_1181_; lean_object* v_unused_1182_; 
v_unused_1181_ = lean_ctor_get(v_after_1016_, 1);
lean_dec(v_unused_1181_);
v_unused_1182_ = lean_ctor_get(v_after_1016_, 0);
lean_dec(v_unused_1182_);
v___x_1141_ = v_after_1016_;
v_isShared_1142_ = v_isSharedCheck_1180_;
goto v_resetjp_1140_;
}
else
{
lean_dec(v_after_1016_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1180_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1143_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1062_);
lean_inc_ref(v_binderType_1100_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 1, v___x_1143_);
lean_ctor_set(v___x_1141_, 0, v_binderType_1100_);
v___x_1145_ = v___x_1141_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_binderType_1100_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1146_; lean_object* v___x_1148_; 
v___x_1146_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1104_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 1, v___x_1146_);
lean_ctor_set(v___x_1138_, 0, v_binderType_1131_);
v___x_1148_ = v___x_1138_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_binderType_1131_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v___x_1146_);
v___x_1148_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
lean_object* v___x_1149_; 
v___x_1149_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1145_, v___x_1148_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1177_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1177_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1177_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
uint8_t v___x_1154_; 
v___x_1154_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_a_1150_);
if (v___x_1154_ == 0)
{
lean_object* v_changesBefore_1155_; lean_object* v_changesAfter_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; uint8_t v___x_1159_; lean_object* v___x_1160_; lean_object* v_changesBefore_1161_; lean_object* v_changesAfter_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1174_; 
lean_dec_ref(v___f_1134_);
lean_dec_ref(v_binderType_1100_);
lean_dec(v_binderName_1099_);
v_changesBefore_1155_ = lean_ctor_get(v_a_1150_, 0);
lean_inc(v_changesBefore_1155_);
v_changesAfter_1156_ = lean_ctor_get(v_a_1150_, 1);
lean_inc(v_changesAfter_1156_);
lean_dec(v_a_1150_);
v___x_1157_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1062_);
lean_dec(v_pos_1062_);
v___x_1158_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1104_);
lean_dec(v_pos_1104_);
v___x_1159_ = 0;
v___x_1160_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v___x_1157_, v___x_1158_, v___x_1159_);
v_changesBefore_1161_ = lean_ctor_get(v___x_1160_, 0);
v_changesAfter_1162_ = lean_ctor_get(v___x_1160_, 1);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1164_ = v___x_1160_;
v_isShared_1165_ = v_isSharedCheck_1174_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_changesAfter_1162_);
lean_inc(v_changesBefore_1161_);
lean_dec(v___x_1160_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1174_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1166_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesBefore_1155_, v_changesBefore_1161_);
v___x_1167_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesAfter_1156_, v_changesAfter_1162_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 1, v___x_1167_);
lean_ctor_set(v___x_1164_, 0, v___x_1166_);
v___x_1169_ = v___x_1164_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1171_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1169_);
v___x_1171_ = v___x_1152_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1169_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
else
{
uint8_t v___x_1175_; lean_object* v___x_1176_; 
lean_del_object(v___x_1152_);
lean_dec(v_a_1150_);
lean_dec(v_pos_1104_);
lean_dec(v_pos_1062_);
v___x_1175_ = 0;
v___x_1176_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_binderName_1099_, v_binderInfo_1102_, v_binderType_1100_, v___f_1134_, v___x_1175_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
return v___x_1176_;
}
}
}
else
{
lean_dec_ref(v___f_1134_);
lean_dec(v_pos_1104_);
lean_dec_ref(v_binderType_1100_);
lean_dec(v_binderName_1099_);
lean_dec(v_pos_1062_);
return v___x_1149_;
}
}
}
}
}
}
}
}
else
{
v___y_1106_ = v_a_1017_;
v___y_1107_ = v_a_1018_;
v___y_1108_ = v_a_1019_;
v___y_1109_ = v_a_1020_;
goto v___jp_1105_;
}
v___jp_1105_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1110_ = l_Lean_Expr_getForallBinderNames(v_expr_1103_);
v___x_1111_ = l_Lean_Expr_getForallBinderNames(v_expr_1061_);
v___x_1112_ = l_List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0(v___x_1110_, v___x_1111_);
if (lean_obj_tag(v___x_1112_) == 1)
{
lean_object* v_val_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v_val_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_val_1113_);
lean_dec_ref(v___x_1112_);
v___x_1114_ = l_List_lengthTR___redArg(v_val_1113_);
v___x_1115_ = lean_unsigned_to_nat(0u);
v___x_1116_ = lean_nat_dec_eq(v___x_1114_, v___x_1115_);
lean_dec(v___x_1114_);
if (v___x_1116_ == 0)
{
v___y_1064_ = v_val_1113_;
v___y_1065_ = v___y_1106_;
v___y_1066_ = v___y_1107_;
v___y_1067_ = v___y_1108_;
v___y_1068_ = v___y_1109_;
goto v___jp_1063_;
}
else
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1, &l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1);
v___x_1118_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_1117_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_dec_ref(v___x_1118_);
v___y_1064_ = v_val_1113_;
v___y_1065_ = v___y_1106_;
v___y_1066_ = v___y_1107_;
v___y_1067_ = v___y_1108_;
v___y_1068_ = v___y_1109_;
goto v___jp_1063_;
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec(v_val_1113_);
lean_dec_ref(v_after_1016_);
lean_dec_ref(v_before_1015_);
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1118_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1118_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
}
else
{
uint8_t v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
lean_dec(v___x_1112_);
v___x_1127_ = 0;
v___x_1128_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1015_, v_after_1016_, v___x_1127_);
v___x_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
return v___x_1129_;
}
}
}
else
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_dec_ref(v_after_1016_);
lean_dec_ref(v_before_1015_);
v___x_1188_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
return v___x_1189_;
}
v___jp_1022_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = lean_unsigned_to_nat(0u);
v___x_1030_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v___y_1023_, v_before_1015_, v___x_1029_, v_a_1028_);
lean_dec(v___y_1023_);
return v___x_1030_;
}
v___jp_1031_:
{
if (v___y_1039_ == 0)
{
lean_object* v___x_1040_; 
lean_dec_ref(v___y_1036_);
v___x_1040_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1035_, v___y_1034_, v___y_1037_);
lean_dec_ref(v___y_1035_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v___x_1041_; 
lean_dec_ref(v___x_1040_);
v___x_1041_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___y_1023_ = v___y_1032_;
v___y_1024_ = v___y_1034_;
v___y_1025_ = v___y_1033_;
v___y_1026_ = v___y_1037_;
v___y_1027_ = v___y_1038_;
v_a_1028_ = v___x_1041_;
goto v___jp_1022_;
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec(v___y_1032_);
lean_dec_ref(v_before_1015_);
v_a_1042_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1040_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1040_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
else
{
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1032_);
lean_dec_ref(v_before_1015_);
return v___y_1036_;
}
}
v___jp_1050_:
{
uint8_t v___x_1059_; 
v___x_1059_ = l_Lean_Exception_isInterrupt(v_a_1058_);
if (v___x_1059_ == 0)
{
uint8_t v___x_1060_; 
v___x_1060_ = l_Lean_Exception_isRuntime(v_a_1058_);
v___y_1032_ = v___y_1051_;
v___y_1033_ = v___y_1054_;
v___y_1034_ = v___y_1053_;
v___y_1035_ = v___y_1052_;
v___y_1036_ = v___y_1057_;
v___y_1037_ = v___y_1055_;
v___y_1038_ = v___y_1056_;
v___y_1039_ = v___x_1060_;
goto v___jp_1031_;
}
else
{
lean_dec_ref(v_a_1058_);
v___y_1032_ = v___y_1051_;
v___y_1033_ = v___y_1054_;
v___y_1034_ = v___y_1053_;
v___y_1035_ = v___y_1052_;
v___y_1036_ = v___y_1057_;
v___y_1037_ = v___y_1055_;
v___y_1038_ = v___y_1056_;
v___y_1039_ = v___x_1059_;
goto v___jp_1031_;
}
}
v___jp_1063_:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_Meta_saveState___redArg(v___y_1066_, v___y_1068_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
lean_dec_ref(v___x_1069_);
v___x_1071_ = l_List_lengthTR___redArg(v___y_1064_);
v___x_1072_ = lean_box(0);
v___x_1073_ = l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(v___y_1064_, v___x_1072_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v_body_u2080_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_a_1074_);
lean_dec_ref(v___x_1073_);
lean_inc(v___x_1071_);
v_body_u2080_1075_ = l_Lean_Expr_getForallBodyMaxDepth(v___x_1071_, v_expr_1061_);
v___x_1076_ = lean_array_mk(v_a_1074_);
v___x_1077_ = lean_expr_instantiate_rev(v_body_u2080_1075_, v___x_1076_);
lean_dec_ref(v___x_1076_);
lean_dec_ref(v_body_u2080_1075_);
lean_inc(v_pos_1062_);
lean_inc(v___x_1071_);
v___x_1078_ = l_Lean_SubExpr_Pos_pushNthBindingBody(v___x_1071_, v_pos_1062_);
v___x_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1079_, v_after_1016_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; 
lean_dec(v_a_1070_);
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
lean_dec_ref(v___x_1080_);
v___y_1023_ = v___x_1071_;
v___y_1024_ = v___y_1066_;
v___y_1025_ = v___y_1065_;
v___y_1026_ = v___y_1068_;
v___y_1027_ = v___y_1067_;
v_a_1028_ = v_a_1081_;
goto v___jp_1022_;
}
else
{
lean_object* v_a_1082_; 
v_a_1082_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1082_);
v___y_1051_ = v___x_1071_;
v___y_1052_ = v_a_1070_;
v___y_1053_ = v___y_1066_;
v___y_1054_ = v___y_1065_;
v___y_1055_ = v___y_1068_;
v___y_1056_ = v___y_1067_;
v___y_1057_ = v___x_1080_;
v_a_1058_ = v_a_1082_;
goto v___jp_1050_;
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
lean_dec_ref(v_after_1016_);
v_a_1083_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1073_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1073_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
lean_inc(v_a_1083_);
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
v___y_1051_ = v___x_1071_;
v___y_1052_ = v_a_1070_;
v___y_1053_ = v___y_1066_;
v___y_1054_ = v___y_1065_;
v___y_1055_ = v___y_1068_;
v___y_1056_ = v___y_1067_;
v___y_1057_ = v___x_1088_;
v_a_1058_ = v_a_1083_;
goto v___jp_1050_;
}
}
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_dec(v___y_1064_);
lean_dec_ref(v_after_1016_);
lean_dec_ref(v_before_1015_);
v_a_1091_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1069_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1069_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(lean_object* v_before_1190_, lean_object* v_after_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v_expr_1213_; lean_object* v_pos_1214_; lean_object* v_expr_1215_; lean_object* v_pos_1216_; lean_object* v_e_u2081_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; uint8_t v___x_1225_; 
v_expr_1213_ = lean_ctor_get(v_before_1190_, 0);
v_pos_1214_ = lean_ctor_get(v_before_1190_, 1);
v_expr_1215_ = lean_ctor_get(v_after_1191_, 0);
v_pos_1216_ = lean_ctor_get(v_after_1191_, 1);
v___x_1225_ = lean_expr_eqv(v_expr_1213_, v_expr_1215_);
if (v___x_1225_ == 0)
{
switch(lean_obj_tag(v_expr_1213_))
{
case 10:
{
lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1234_; 
lean_inc_ref(v_expr_1213_);
lean_inc(v_pos_1214_);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_before_1190_);
if (v_isSharedCheck_1234_ == 0)
{
lean_object* v_unused_1235_; lean_object* v_unused_1236_; 
v_unused_1235_ = lean_ctor_get(v_before_1190_, 1);
lean_dec(v_unused_1235_);
v_unused_1236_ = lean_ctor_get(v_before_1190_, 0);
lean_dec(v_unused_1236_);
v___x_1227_ = v_before_1190_;
v_isShared_1228_ = v_isSharedCheck_1234_;
goto v_resetjp_1226_;
}
else
{
lean_dec(v_before_1190_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1234_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v_expr_1229_; lean_object* v___x_1231_; 
v_expr_1229_ = lean_ctor_get(v_expr_1213_, 1);
lean_inc_ref(v_expr_1229_);
lean_dec_ref(v_expr_1213_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v_expr_1229_);
v___x_1231_ = v___x_1227_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_expr_1229_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_pos_1214_);
v___x_1231_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
v_before_1190_ = v___x_1231_;
goto _start;
}
}
}
case 5:
{
switch(lean_obj_tag(v_expr_1215_))
{
case 10:
{
lean_object* v_expr_1237_; 
lean_inc_ref(v_expr_1215_);
lean_inc(v_pos_1216_);
lean_dec_ref(v_after_1191_);
v_expr_1237_ = lean_ctor_get(v_expr_1215_, 1);
lean_inc_ref(v_expr_1237_);
lean_dec_ref(v_expr_1215_);
v_e_u2081_1218_ = v_expr_1237_;
v___y_1219_ = v_a_1192_;
v___y_1220_ = v_a_1193_;
v___y_1221_ = v_a_1194_;
v___y_1222_ = v_a_1195_;
goto v___jp_1217_;
}
case 5:
{
lean_object* v_dummy_1238_; lean_object* v_nargs_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v_fst_1244_; lean_object* v_snd_1245_; lean_object* v_nargs_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v_fst_1250_; lean_object* v_snd_1251_; uint8_t v___x_1252_; 
v_dummy_1238_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0, &l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0);
v_nargs_1239_ = l_Lean_Expr_getAppNumArgs(v_expr_1215_);
lean_inc(v_nargs_1239_);
v___x_1240_ = lean_mk_array(v_nargs_1239_, v_dummy_1238_);
v___x_1241_ = lean_unsigned_to_nat(1u);
v___x_1242_ = lean_nat_sub(v_nargs_1239_, v___x_1241_);
lean_dec(v_nargs_1239_);
lean_inc_ref(v_expr_1215_);
v___x_1243_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(v_expr_1215_, v___x_1240_, v___x_1242_);
v_fst_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_fst_1244_);
v_snd_1245_ = lean_ctor_get(v___x_1243_, 1);
lean_inc(v_snd_1245_);
lean_dec_ref(v___x_1243_);
v_nargs_1246_ = l_Lean_Expr_getAppNumArgs(v_expr_1213_);
lean_inc(v_nargs_1246_);
v___x_1247_ = lean_mk_array(v_nargs_1246_, v_dummy_1238_);
v___x_1248_ = lean_nat_sub(v_nargs_1246_, v___x_1241_);
lean_dec(v_nargs_1246_);
lean_inc_ref(v_expr_1213_);
v___x_1249_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(v_expr_1213_, v___x_1247_, v___x_1248_);
v_fst_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_fst_1250_);
v_snd_1251_ = lean_ctor_get(v___x_1249_, 1);
lean_inc(v_snd_1251_);
lean_dec_ref(v___x_1249_);
v___x_1252_ = lean_expr_eqv(v_fst_1244_, v_fst_1250_);
lean_dec(v_fst_1250_);
lean_dec(v_fst_1244_);
if (v___x_1252_ == 0)
{
lean_dec(v_snd_1251_);
lean_dec(v_snd_1245_);
goto v___jp_1205_;
}
else
{
if (v___x_1225_ == 0)
{
lean_object* v___x_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; 
v___x_1253_ = lean_array_get_size(v_snd_1245_);
v___x_1254_ = lean_array_get_size(v_snd_1251_);
v___x_1255_ = lean_nat_dec_eq(v___x_1253_, v___x_1254_);
if (v___x_1255_ == 0)
{
lean_dec(v_snd_1251_);
lean_dec(v_snd_1245_);
goto v___jp_1205_;
}
else
{
lean_object* v_args_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v_args_1256_ = l_Array_zip___redArg(v_snd_1245_, v_snd_1251_);
lean_dec(v_snd_1251_);
v___x_1257_ = lean_array_get_size(v_args_1256_);
v___x_1258_ = lean_unsigned_to_nat(0u);
v___x_1259_ = lean_mk_empty_array_with_capacity(v___x_1257_);
v___x_1260_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_1245_, v_before_1190_, v_after_1191_, v_args_1256_, v___x_1257_, v___x_1258_, v___x_1259_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
lean_dec_ref(v_args_1256_);
lean_dec_ref(v_after_1191_);
lean_dec_ref(v_before_1190_);
lean_dec(v_snd_1245_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1287_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1263_ = v___x_1260_;
v_isShared_1264_ = v_isSharedCheck_1287_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1287_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1265_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___x_1266_ = lean_array_get_size(v_a_1261_);
v___x_1267_ = lean_nat_dec_lt(v___x_1258_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1269_; 
lean_dec(v_a_1261_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1265_);
v___x_1269_ = v___x_1263_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1265_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
else
{
uint8_t v___x_1271_; 
v___x_1271_ = lean_nat_dec_le(v___x_1266_, v___x_1266_);
if (v___x_1271_ == 0)
{
if (v___x_1267_ == 0)
{
lean_object* v___x_1273_; 
lean_dec(v_a_1261_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1265_);
v___x_1273_ = v___x_1263_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1265_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
else
{
size_t v___x_1275_; size_t v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1279_; 
v___x_1275_ = ((size_t)0ULL);
v___x_1276_ = lean_usize_of_nat(v___x_1266_);
v___x_1277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_a_1261_, v___x_1275_, v___x_1276_, v___x_1265_);
lean_dec(v_a_1261_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1277_);
v___x_1279_ = v___x_1263_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1277_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
else
{
size_t v___x_1281_; size_t v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1285_; 
v___x_1281_ = ((size_t)0ULL);
v___x_1282_ = lean_usize_of_nat(v___x_1266_);
v___x_1283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_a_1261_, v___x_1281_, v___x_1282_, v___x_1265_);
lean_dec(v_a_1261_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1283_);
v___x_1285_ = v___x_1263_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1283_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
v_a_1288_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1260_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1260_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
else
{
lean_dec(v_snd_1251_);
lean_dec(v_snd_1245_);
goto v___jp_1205_;
}
}
}
default: 
{
goto v___jp_1209_;
}
}
}
case 7:
{
if (lean_obj_tag(v_expr_1215_) == 10)
{
lean_object* v_expr_1296_; 
lean_inc_ref(v_expr_1215_);
lean_inc(v_pos_1216_);
lean_dec_ref(v_after_1191_);
v_expr_1296_ = lean_ctor_get(v_expr_1215_, 1);
lean_inc_ref(v_expr_1296_);
lean_dec_ref(v_expr_1215_);
v_e_u2081_1218_ = v_expr_1296_;
v___y_1219_ = v_a_1192_;
v___y_1220_ = v_a_1193_;
v___y_1221_ = v_a_1194_;
v___y_1222_ = v_a_1195_;
goto v___jp_1217_;
}
else
{
lean_object* v___x_1297_; 
v___x_1297_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(v_before_1190_, v_after_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
return v___x_1297_;
}
}
case 6:
{
switch(lean_obj_tag(v_expr_1215_))
{
case 10:
{
lean_object* v_expr_1298_; 
lean_inc_ref(v_expr_1215_);
lean_inc(v_pos_1216_);
lean_dec_ref(v_after_1191_);
v_expr_1298_ = lean_ctor_get(v_expr_1215_, 1);
lean_inc_ref(v_expr_1298_);
lean_dec_ref(v_expr_1215_);
v_e_u2081_1218_ = v_expr_1298_;
v___y_1219_ = v_a_1192_;
v___y_1220_ = v_a_1193_;
v___y_1221_ = v_a_1194_;
v___y_1222_ = v_a_1195_;
goto v___jp_1217_;
}
case 6:
{
lean_object* v_binderName_1299_; lean_object* v_binderType_1300_; lean_object* v_body_1301_; uint8_t v_binderInfo_1302_; lean_object* v_binderName_1303_; lean_object* v_binderType_1304_; lean_object* v_body_1305_; uint8_t v_binderInfo_1306_; uint8_t v___x_1307_; 
v_binderName_1299_ = lean_ctor_get(v_expr_1213_, 0);
v_binderType_1300_ = lean_ctor_get(v_expr_1213_, 1);
v_body_1301_ = lean_ctor_get(v_expr_1213_, 2);
v_binderInfo_1302_ = lean_ctor_get_uint8(v_expr_1213_, sizeof(void*)*3 + 8);
v_binderName_1303_ = lean_ctor_get(v_expr_1215_, 0);
v_binderType_1304_ = lean_ctor_get(v_expr_1215_, 1);
v_body_1305_ = lean_ctor_get(v_expr_1215_, 2);
v_binderInfo_1306_ = lean_ctor_get_uint8(v_expr_1215_, sizeof(void*)*3 + 8);
v___x_1307_ = lean_name_eq(v_binderName_1299_, v_binderName_1303_);
if (v___x_1307_ == 0)
{
goto v___jp_1201_;
}
else
{
if (v___x_1225_ == 0)
{
uint8_t v___x_1308_; 
v___x_1308_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1302_, v_binderInfo_1306_);
if (v___x_1308_ == 0)
{
goto v___jp_1201_;
}
else
{
lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1358_; 
lean_inc_ref(v_body_1305_);
lean_inc_ref(v_binderType_1304_);
lean_inc_ref(v_body_1301_);
lean_inc_ref(v_binderType_1300_);
lean_inc(v_pos_1216_);
lean_inc(v_pos_1214_);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_before_1190_);
if (v_isSharedCheck_1358_ == 0)
{
lean_object* v_unused_1359_; lean_object* v_unused_1360_; 
v_unused_1359_ = lean_ctor_get(v_before_1190_, 1);
lean_dec(v_unused_1359_);
v_unused_1360_ = lean_ctor_get(v_before_1190_, 0);
lean_dec(v_unused_1360_);
v___x_1310_ = v_before_1190_;
v_isShared_1311_ = v_isSharedCheck_1358_;
goto v_resetjp_1309_;
}
else
{
lean_dec(v_before_1190_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1358_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1355_; 
v_isSharedCheck_1355_ = !lean_is_exclusive(v_after_1191_);
if (v_isSharedCheck_1355_ == 0)
{
lean_object* v_unused_1356_; lean_object* v_unused_1357_; 
v_unused_1356_ = lean_ctor_get(v_after_1191_, 1);
lean_dec(v_unused_1356_);
v_unused_1357_ = lean_ctor_get(v_after_1191_, 0);
lean_dec(v_unused_1357_);
v___x_1313_ = v_after_1191_;
v_isShared_1314_ = v_isSharedCheck_1355_;
goto v_resetjp_1312_;
}
else
{
lean_dec(v_after_1191_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1355_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1315_; lean_object* v___x_1317_; 
v___x_1315_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1214_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 1, v___x_1315_);
lean_ctor_set(v___x_1313_, 0, v_binderType_1300_);
v___x_1317_ = v___x_1313_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_binderType_1300_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v___x_1315_);
v___x_1317_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v___x_1318_; lean_object* v___x_1320_; 
v___x_1318_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1216_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 1, v___x_1318_);
lean_ctor_set(v___x_1310_, 0, v_binderType_1304_);
v___x_1320_ = v___x_1310_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_binderType_1304_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v___x_1318_);
v___x_1320_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
lean_object* v___x_1321_; 
v___x_1321_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1317_, v___x_1320_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1352_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1324_ = v___x_1321_;
v_isShared_1325_ = v_isSharedCheck_1352_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1321_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1352_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
uint8_t v___x_1326_; 
v___x_1326_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_a_1322_);
if (v___x_1326_ == 0)
{
lean_object* v_changesBefore_1327_; lean_object* v_changesAfter_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; lean_object* v___x_1332_; lean_object* v_changesBefore_1333_; lean_object* v_changesAfter_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1346_; 
lean_dec_ref(v_body_1305_);
lean_dec_ref(v_body_1301_);
v_changesBefore_1327_ = lean_ctor_get(v_a_1322_, 0);
lean_inc(v_changesBefore_1327_);
v_changesAfter_1328_ = lean_ctor_get(v_a_1322_, 1);
lean_inc(v_changesAfter_1328_);
lean_dec(v_a_1322_);
v___x_1329_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1214_);
lean_dec(v_pos_1214_);
v___x_1330_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1216_);
lean_dec(v_pos_1216_);
v___x_1331_ = 0;
v___x_1332_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v___x_1329_, v___x_1330_, v___x_1331_);
v_changesBefore_1333_ = lean_ctor_get(v___x_1332_, 0);
v_changesAfter_1334_ = lean_ctor_get(v___x_1332_, 1);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1336_ = v___x_1332_;
v_isShared_1337_ = v_isSharedCheck_1346_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_changesAfter_1334_);
lean_inc(v_changesBefore_1333_);
lean_dec(v___x_1332_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1346_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___x_1338_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesBefore_1327_, v_changesBefore_1333_);
v___x_1339_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesAfter_1328_, v_changesAfter_1334_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 1, v___x_1339_);
lean_ctor_set(v___x_1336_, 0, v___x_1338_);
v___x_1341_ = v___x_1336_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1338_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
lean_object* v___x_1343_; 
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v___x_1341_);
v___x_1343_ = v___x_1324_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
else
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_del_object(v___x_1324_);
lean_dec(v_a_1322_);
v___x_1347_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1214_);
lean_dec(v_pos_1214_);
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v_body_1301_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
v___x_1349_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1216_);
lean_dec(v_pos_1216_);
v___x_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1350_, 0, v_body_1305_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
v_before_1190_ = v___x_1348_;
v_after_1191_ = v___x_1350_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_body_1305_);
lean_dec_ref(v_body_1301_);
lean_dec(v_pos_1216_);
lean_dec(v_pos_1214_);
return v___x_1321_;
}
}
}
}
}
}
}
else
{
goto v___jp_1201_;
}
}
}
default: 
{
goto v___jp_1209_;
}
}
}
case 11:
{
switch(lean_obj_tag(v_expr_1215_))
{
case 10:
{
lean_object* v_expr_1361_; 
lean_inc_ref(v_expr_1215_);
lean_inc(v_pos_1216_);
lean_dec_ref(v_after_1191_);
v_expr_1361_ = lean_ctor_get(v_expr_1215_, 1);
lean_inc_ref(v_expr_1361_);
lean_dec_ref(v_expr_1215_);
v_e_u2081_1218_ = v_expr_1361_;
v___y_1219_ = v_a_1192_;
v___y_1220_ = v_a_1193_;
v___y_1221_ = v_a_1194_;
v___y_1222_ = v_a_1195_;
goto v___jp_1217_;
}
case 11:
{
lean_object* v_typeName_1362_; lean_object* v_idx_1363_; lean_object* v_struct_1364_; lean_object* v_typeName_1365_; lean_object* v_idx_1366_; lean_object* v_struct_1367_; uint8_t v___x_1368_; 
v_typeName_1362_ = lean_ctor_get(v_expr_1213_, 0);
v_idx_1363_ = lean_ctor_get(v_expr_1213_, 1);
v_struct_1364_ = lean_ctor_get(v_expr_1213_, 2);
v_typeName_1365_ = lean_ctor_get(v_expr_1215_, 0);
v_idx_1366_ = lean_ctor_get(v_expr_1215_, 1);
v_struct_1367_ = lean_ctor_get(v_expr_1215_, 2);
v___x_1368_ = lean_name_eq(v_typeName_1362_, v_typeName_1365_);
if (v___x_1368_ == 0)
{
goto v___jp_1197_;
}
else
{
if (v___x_1225_ == 0)
{
uint8_t v___x_1369_; 
v___x_1369_ = lean_nat_dec_eq(v_idx_1363_, v_idx_1366_);
if (v___x_1369_ == 0)
{
goto v___jp_1197_;
}
else
{
lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1388_; 
lean_inc_ref(v_struct_1367_);
lean_inc_ref(v_struct_1364_);
lean_inc(v_pos_1216_);
lean_inc(v_pos_1214_);
v_isSharedCheck_1388_ = !lean_is_exclusive(v_before_1190_);
if (v_isSharedCheck_1388_ == 0)
{
lean_object* v_unused_1389_; lean_object* v_unused_1390_; 
v_unused_1389_ = lean_ctor_get(v_before_1190_, 1);
lean_dec(v_unused_1389_);
v_unused_1390_ = lean_ctor_get(v_before_1190_, 0);
lean_dec(v_unused_1390_);
v___x_1371_ = v_before_1190_;
v_isShared_1372_ = v_isSharedCheck_1388_;
goto v_resetjp_1370_;
}
else
{
lean_dec(v_before_1190_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1388_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1385_; 
v_isSharedCheck_1385_ = !lean_is_exclusive(v_after_1191_);
if (v_isSharedCheck_1385_ == 0)
{
lean_object* v_unused_1386_; lean_object* v_unused_1387_; 
v_unused_1386_ = lean_ctor_get(v_after_1191_, 1);
lean_dec(v_unused_1386_);
v_unused_1387_ = lean_ctor_get(v_after_1191_, 0);
lean_dec(v_unused_1387_);
v___x_1374_ = v_after_1191_;
v_isShared_1375_ = v_isSharedCheck_1385_;
goto v_resetjp_1373_;
}
else
{
lean_dec(v_after_1191_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1385_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v___x_1378_; 
v___x_1376_ = l_Lean_SubExpr_Pos_pushProj(v_pos_1214_);
lean_dec(v_pos_1214_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 1, v___x_1376_);
lean_ctor_set(v___x_1374_, 0, v_struct_1364_);
v___x_1378_ = v___x_1374_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_struct_1364_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
lean_object* v___x_1379_; lean_object* v___x_1381_; 
v___x_1379_ = l_Lean_SubExpr_Pos_pushProj(v_pos_1216_);
lean_dec(v_pos_1216_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 1, v___x_1379_);
lean_ctor_set(v___x_1371_, 0, v_struct_1367_);
v___x_1381_ = v___x_1371_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_struct_1367_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
v_before_1190_ = v___x_1378_;
v_after_1191_ = v___x_1381_;
goto _start;
}
}
}
}
}
}
else
{
goto v___jp_1197_;
}
}
}
default: 
{
goto v___jp_1209_;
}
}
}
default: 
{
if (lean_obj_tag(v_expr_1215_) == 10)
{
lean_object* v_expr_1391_; 
lean_inc_ref(v_expr_1215_);
lean_inc(v_pos_1216_);
lean_dec_ref(v_after_1191_);
v_expr_1391_ = lean_ctor_get(v_expr_1215_, 1);
lean_inc_ref(v_expr_1391_);
lean_dec_ref(v_expr_1215_);
v_e_u2081_1218_ = v_expr_1391_;
v___y_1219_ = v_a_1192_;
v___y_1220_ = v_a_1193_;
v___y_1221_ = v_a_1194_;
v___y_1222_ = v_a_1195_;
goto v___jp_1217_;
}
else
{
goto v___jp_1209_;
}
}
}
}
else
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
lean_dec_ref(v_after_1191_);
lean_dec_ref(v_before_1190_);
v___x_1392_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___x_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
return v___x_1393_;
}
v___jp_1197_:
{
uint8_t v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1198_ = 0;
v___x_1199_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1190_, v_after_1191_, v___x_1198_);
v___x_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
return v___x_1200_;
}
v___jp_1201_:
{
uint8_t v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1202_ = 0;
v___x_1203_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1190_, v_after_1191_, v___x_1202_);
v___x_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
return v___x_1204_;
}
v___jp_1205_:
{
uint8_t v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = 0;
v___x_1207_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1190_, v_after_1191_, v___x_1206_);
v___x_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
return v___x_1208_;
}
v___jp_1209_:
{
uint8_t v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1210_ = 0;
v___x_1211_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1190_, v_after_1191_, v___x_1210_);
v___x_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
return v___x_1212_;
}
v___jp_1217_:
{
lean_object* v___x_1223_; 
v___x_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1223_, 0, v_e_u2081_1218_);
lean_ctor_set(v___x_1223_, 1, v_pos_1216_);
v_after_1191_ = v___x_1223_;
v_a_1192_ = v___y_1219_;
v_a_1193_ = v___y_1220_;
v_a_1194_ = v___y_1221_;
v_a_1195_ = v___y_1222_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0(lean_object* v_body_1394_, lean_object* v_pos_1395_, lean_object* v_body_1396_, lean_object* v_pos_1397_, lean_object* v_x_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1404_ = lean_expr_instantiate1(v_body_1394_, v_x_1398_);
v___x_1405_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1395_);
v___x_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1404_);
lean_ctor_set(v___x_1406_, 1, v___x_1405_);
v___x_1407_ = lean_expr_instantiate1(v_body_1396_, v_x_1398_);
v___x_1408_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1397_);
v___x_1409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1407_);
lean_ctor_set(v___x_1409_, 1, v___x_1408_);
v___x_1410_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1406_, v___x_1409_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg___boxed(lean_object* v_snd_1411_, lean_object* v_before_1412_, lean_object* v_after_1413_, lean_object* v_as_1414_, lean_object* v_i_1415_, lean_object* v_j_1416_, lean_object* v_bs_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_1411_, v_before_1412_, v_after_1413_, v_as_1414_, v_i_1415_, v_j_1416_, v_bs_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec_ref(v_as_1414_);
lean_dec_ref(v_after_1413_);
lean_dec_ref(v_before_1412_);
lean_dec_ref(v_snd_1411_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___boxed(lean_object* v_before_1424_, lean_object* v_after_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(v_before_1424_, v_after_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_);
lean_dec(v_a_1429_);
lean_dec_ref(v_a_1428_);
lean_dec(v_a_1427_);
lean_dec_ref(v_a_1426_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___boxed(lean_object* v_before_1432_, lean_object* v_after_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v_before_1432_, v_after_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_);
lean_dec(v_a_1437_);
lean_dec_ref(v_a_1436_);
lean_dec(v_a_1435_);
lean_dec_ref(v_a_1434_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1(lean_object* v_upperBound_1440_, lean_object* v_before_1441_, lean_object* v_inst_1442_, lean_object* v_R_1443_, lean_object* v_a_1444_, lean_object* v_b_1445_, lean_object* v_c_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v_upperBound_1440_, v_before_1441_, v_a_1444_, v_b_1445_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___boxed(lean_object* v_upperBound_1453_, lean_object* v_before_1454_, lean_object* v_inst_1455_, lean_object* v_R_1456_, lean_object* v_a_1457_, lean_object* v_b_1458_, lean_object* v_c_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1(v_upperBound_1453_, v_before_1454_, v_inst_1455_, v_R_1456_, v_a_1457_, v_b_1458_, v_c_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v_upperBound_1453_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3(lean_object* v_00_u03b1_1466_, lean_object* v_msg_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v_msg_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___boxed(lean_object* v_00_u03b1_1474_, lean_object* v_msg_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3(v_00_u03b1_1474_, v_msg_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4(uint8_t v_b_u2082_1482_, lean_object* v_k_1483_, lean_object* v_t_1484_, lean_object* v_hl_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_1482_, v_k_1483_, v_t_1484_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___boxed(lean_object* v_b_u2082_1487_, lean_object* v_k_1488_, lean_object* v_t_1489_, lean_object* v_hl_1490_){
_start:
{
uint8_t v_b_u2082_boxed_1491_; lean_object* v_res_1492_; 
v_b_u2082_boxed_1491_ = lean_unbox(v_b_u2082_1487_);
v_res_1492_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4(v_b_u2082_boxed_1491_, v_k_1488_, v_t_1489_, v_hl_1490_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5(lean_object* v_init_1493_, lean_object* v_t_1494_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_init_1493_, v_t_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9(lean_object* v_snd_1496_, lean_object* v_before_1497_, lean_object* v_after_1498_, lean_object* v_as_1499_, lean_object* v_i_1500_, lean_object* v_j_1501_, lean_object* v_inv_1502_, lean_object* v_bs_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_1496_, v_before_1497_, v_after_1498_, v_as_1499_, v_i_1500_, v_j_1501_, v_bs_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___boxed(lean_object* v_snd_1510_, lean_object* v_before_1511_, lean_object* v_after_1512_, lean_object* v_as_1513_, lean_object* v_i_1514_, lean_object* v_j_1515_, lean_object* v_inv_1516_, lean_object* v_bs_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9(v_snd_1510_, v_before_1511_, v_after_1512_, v_as_1513_, v_i_1514_, v_j_1515_, v_inv_1516_, v_bs_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec_ref(v_as_1513_);
lean_dec_ref(v_after_1512_);
lean_dec_ref(v_before_1511_);
lean_dec_ref(v_snd_1510_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(lean_object* v_e_u2080_1524_, lean_object* v_e_u2081_1525_, uint8_t v_useAfter_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v___x_1532_; lean_object* v_s_u2080_1533_; lean_object* v_s_u2081_1534_; 
v___x_1532_ = l_Lean_SubExpr_Pos_root;
v_s_u2080_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_u2080_1533_, 0, v_e_u2080_1524_);
lean_ctor_set(v_s_u2080_1533_, 1, v___x_1532_);
v_s_u2081_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_u2081_1534_, 0, v_e_u2081_1525_);
lean_ctor_set(v_s_u2081_1534_, 1, v___x_1532_);
if (v_useAfter_1526_ == 0)
{
lean_object* v___x_1535_; 
v___x_1535_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v_s_u2081_1534_, v_s_u2080_1533_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_);
return v___x_1535_;
}
else
{
lean_object* v___x_1536_; 
v___x_1536_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v_s_u2080_1533_, v_s_u2081_1534_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_);
return v___x_1536_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff___boxed(lean_object* v_e_u2080_1537_, lean_object* v_e_u2081_1538_, lean_object* v_useAfter_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
uint8_t v_useAfter_boxed_1545_; lean_object* v_res_1546_; 
v_useAfter_boxed_1545_ = lean_unbox(v_useAfter_1539_);
v_res_1546_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(v_e_u2080_1537_, v_e_u2081_1538_, v_useAfter_boxed_1545_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_);
lean_dec(v_a_1543_);
lean_dec_ref(v_a_1542_);
lean_dec(v_a_1541_);
lean_dec_ref(v_a_1540_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0(uint8_t v_useAfter_1547_, lean_object* v_info_1548_, uint8_t v_d_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
uint8_t v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1555_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag(v_useAfter_1547_, v_d_1549_);
v___x_1556_ = l_Lean_Widget_SubexprInfo_withDiffTag(v___x_1555_, v_info_1548_);
v___x_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0___boxed(lean_object* v_useAfter_1558_, lean_object* v_info_1559_, lean_object* v_d_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
uint8_t v_useAfter_boxed_1566_; uint8_t v_d_boxed_1567_; lean_object* v_res_1568_; 
v_useAfter_boxed_1566_ = lean_unbox(v_useAfter_1558_);
v_d_boxed_1567_ = lean_unbox(v_d_1560_);
v_res_1568_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0(v_useAfter_boxed_1566_, v_info_1559_, v_d_boxed_1567_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(lean_object* v_f_1569_, lean_object* v_x_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
switch(lean_obj_tag(v_x_1570_))
{
case 0:
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1584_; 
lean_dec_ref(v_f_1569_);
v_a_1576_ = lean_ctor_get(v_x_1570_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_x_1570_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1578_ = v_x_1570_;
v_isShared_1579_ = v_isSharedCheck_1584_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v_x_1570_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1584_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
return v___x_1582_;
}
}
}
case 1:
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1611_; 
v_a_1585_ = lean_ctor_get(v_x_1570_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v_x_1570_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1587_ = v_x_1570_;
v_isShared_1588_ = v_isSharedCheck_1611_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v_x_1570_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1611_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
size_t v_sz_1589_; size_t v___x_1590_; lean_object* v___x_1591_; 
v_sz_1589_ = lean_array_size(v_a_1585_);
v___x_1590_ = ((size_t)0ULL);
v___x_1591_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_1569_, v_sz_1589_, v___x_1590_, v_a_1585_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1602_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1594_ = v___x_1591_;
v_isShared_1595_ = v_isSharedCheck_1602_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1591_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1602_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v_a_1592_);
v___x_1597_ = v___x_1587_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1599_; 
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 0, v___x_1597_);
v___x_1599_ = v___x_1594_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1597_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_del_object(v___x_1587_);
v_a_1603_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1591_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1591_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
default: 
{
lean_object* v_a_1612_; lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1639_; 
v_a_1612_ = lean_ctor_get(v_x_1570_, 0);
v_a_1613_ = lean_ctor_get(v_x_1570_, 1);
v_isSharedCheck_1639_ = !lean_is_exclusive(v_x_1570_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1615_ = v_x_1570_;
v_isShared_1616_ = v_isSharedCheck_1639_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_inc(v_a_1612_);
lean_dec(v_x_1570_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1639_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1617_; 
lean_inc_ref(v_f_1569_);
lean_inc(v___y_1574_);
lean_inc_ref(v___y_1573_);
lean_inc(v___y_1572_);
lean_inc_ref(v___y_1571_);
v___x_1617_ = lean_apply_6(v_f_1569_, v_a_1612_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, lean_box(0));
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1619_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1618_);
lean_dec_ref(v___x_1617_);
v___x_1619_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1569_, v_a_1613_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1630_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1622_ = v___x_1619_;
v_isShared_1623_ = v_isSharedCheck_1630_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1619_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1630_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 1, v_a_1620_);
lean_ctor_set(v___x_1615_, 0, v_a_1618_);
v___x_1625_ = v___x_1615_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1618_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
lean_object* v___x_1627_; 
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 0, v___x_1625_);
v___x_1627_ = v___x_1622_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1625_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
else
{
lean_dec(v_a_1618_);
lean_del_object(v___x_1615_);
return v___x_1619_;
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_del_object(v___x_1615_);
lean_dec_ref(v_a_1613_);
lean_dec_ref(v_f_1569_);
v_a_1631_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1617_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1617_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(lean_object* v_f_1640_, size_t v_sz_1641_, size_t v_i_1642_, lean_object* v_bs_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
uint8_t v___x_1649_; 
v___x_1649_ = lean_usize_dec_lt(v_i_1642_, v_sz_1641_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; 
lean_dec_ref(v_f_1640_);
v___x_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1650_, 0, v_bs_1643_);
return v___x_1650_;
}
else
{
lean_object* v_v_1651_; lean_object* v___x_1652_; 
v_v_1651_ = lean_array_uget_borrowed(v_bs_1643_, v_i_1642_);
lean_inc(v_v_1651_);
lean_inc_ref(v_f_1640_);
v___x_1652_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1640_, v_v_1651_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1654_; lean_object* v_bs_x27_1655_; size_t v___x_1656_; size_t v___x_1657_; lean_object* v___x_1658_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref(v___x_1652_);
v___x_1654_ = lean_unsigned_to_nat(0u);
v_bs_x27_1655_ = lean_array_uset(v_bs_1643_, v_i_1642_, v___x_1654_);
v___x_1656_ = ((size_t)1ULL);
v___x_1657_ = lean_usize_add(v_i_1642_, v___x_1656_);
v___x_1658_ = lean_array_uset(v_bs_x27_1655_, v_i_1642_, v_a_1653_);
v_i_1642_ = v___x_1657_;
v_bs_1643_ = v___x_1658_;
goto _start;
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec_ref(v_bs_1643_);
lean_dec_ref(v_f_1640_);
v_a_1660_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1652_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1652_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_1668_, lean_object* v_sz_1669_, lean_object* v_i_1670_, lean_object* v_bs_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
size_t v_sz_boxed_1677_; size_t v_i_boxed_1678_; lean_object* v_res_1679_; 
v_sz_boxed_1677_ = lean_unbox_usize(v_sz_1669_);
lean_dec(v_sz_1669_);
v_i_boxed_1678_ = lean_unbox_usize(v_i_1670_);
lean_dec(v_i_1670_);
v_res_1679_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_1668_, v_sz_boxed_1677_, v_i_boxed_1678_, v_bs_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg___boxed(lean_object* v_f_1680_, lean_object* v_x_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1680_, v_x_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(lean_object* v_t_1688_, lean_object* v_k_1689_){
_start:
{
if (lean_obj_tag(v_t_1688_) == 0)
{
lean_object* v_k_1690_; lean_object* v_v_1691_; lean_object* v_l_1692_; lean_object* v_r_1693_; uint8_t v___x_1694_; 
v_k_1690_ = lean_ctor_get(v_t_1688_, 1);
v_v_1691_ = lean_ctor_get(v_t_1688_, 2);
v_l_1692_ = lean_ctor_get(v_t_1688_, 3);
v_r_1693_ = lean_ctor_get(v_t_1688_, 4);
v___x_1694_ = lean_nat_dec_lt(v_k_1689_, v_k_1690_);
if (v___x_1694_ == 0)
{
uint8_t v___x_1695_; 
v___x_1695_ = lean_nat_dec_eq(v_k_1689_, v_k_1690_);
if (v___x_1695_ == 0)
{
v_t_1688_ = v_r_1693_;
goto _start;
}
else
{
lean_object* v___x_1697_; 
lean_inc(v_v_1691_);
v___x_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1697_, 0, v_v_1691_);
return v___x_1697_;
}
}
else
{
v_t_1688_ = v_l_1692_;
goto _start;
}
}
else
{
lean_object* v___x_1699_; 
v___x_1699_ = lean_box(0);
return v___x_1699_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg___boxed(lean_object* v_t_1700_, lean_object* v_k_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_t_1700_, v_k_1701_);
lean_dec(v_k_1701_);
lean_dec(v_t_1700_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0(lean_object* v_pm_1703_, lean_object* v_merger_1704_, lean_object* v_info_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v_subexprPos_1711_; lean_object* v___x_1712_; 
v_subexprPos_1711_ = lean_ctor_get(v_info_1705_, 1);
v___x_1712_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_pm_1703_, v_subexprPos_1711_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v___x_1713_; 
lean_dec_ref(v_merger_1704_);
v___x_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1713_, 0, v_info_1705_);
return v___x_1713_;
}
else
{
lean_object* v_val_1714_; lean_object* v___x_1715_; 
v_val_1714_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_val_1714_);
lean_dec_ref(v___x_1712_);
lean_inc(v___y_1709_);
lean_inc_ref(v___y_1708_);
lean_inc(v___y_1707_);
lean_inc_ref(v___y_1706_);
v___x_1715_ = lean_apply_7(v_merger_1704_, v_info_1705_, v_val_1714_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, lean_box(0));
return v___x_1715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0___boxed(lean_object* v_pm_1716_, lean_object* v_merger_1717_, lean_object* v_info_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0(v_pm_1716_, v_merger_1717_, v_info_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v_pm_1716_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(lean_object* v_merger_1725_, lean_object* v_pm_1726_, lean_object* v_tt_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
if (lean_obj_tag(v_pm_1726_) == 0)
{
lean_object* v___f_1733_; lean_object* v___x_1734_; 
v___f_1733_ = lean_alloc_closure((void*)(l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1733_, 0, v_pm_1726_);
lean_closure_set(v___f_1733_, 1, v_merger_1725_);
v___x_1734_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v___f_1733_, v_tt_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
return v___x_1734_;
}
else
{
lean_object* v___x_1735_; 
lean_dec_ref(v_merger_1725_);
v___x_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1735_, 0, v_tt_1727_);
return v___x_1735_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___boxed(lean_object* v_merger_1736_, lean_object* v_pm_1737_, lean_object* v_tt_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v_merger_1736_, v_pm_1737_, v_tt_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(uint8_t v_useAfter_1745_, lean_object* v_diff_1746_, lean_object* v_info_u2081_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v___x_1753_; lean_object* v___f_1754_; 
v___x_1753_ = lean_box(v_useAfter_1745_);
v___f_1754_ = lean_alloc_closure((void*)(l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1754_, 0, v___x_1753_);
if (v_useAfter_1745_ == 0)
{
lean_object* v_changesBefore_1755_; lean_object* v___x_1756_; 
v_changesBefore_1755_ = lean_ctor_get(v_diff_1746_, 0);
lean_inc(v_changesBefore_1755_);
lean_dec_ref(v_diff_1746_);
v___x_1756_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v___f_1754_, v_changesBefore_1755_, v_info_u2081_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
return v___x_1756_;
}
else
{
lean_object* v_changesAfter_1757_; lean_object* v___x_1758_; 
v_changesAfter_1757_ = lean_ctor_get(v_diff_1746_, 1);
lean_inc(v_changesAfter_1757_);
lean_dec_ref(v_diff_1746_);
v___x_1758_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v___f_1754_, v_changesAfter_1757_, v_info_u2081_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
return v___x_1758_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___boxed(lean_object* v_useAfter_1759_, lean_object* v_diff_1760_, lean_object* v_info_u2081_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_){
_start:
{
uint8_t v_useAfter_boxed_1767_; lean_object* v_res_1768_; 
v_useAfter_boxed_1767_ = lean_unbox(v_useAfter_1759_);
v_res_1768_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(v_useAfter_boxed_1767_, v_diff_1760_, v_info_u2081_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_);
lean_dec(v_a_1765_);
lean_dec_ref(v_a_1764_);
lean_dec(v_a_1763_);
lean_dec_ref(v_a_1762_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0(lean_object* v_00_u03b1_1769_, lean_object* v_merger_1770_, lean_object* v_pm_1771_, lean_object* v_tt_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v_merger_1770_, v_pm_1771_, v_tt_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___boxed(lean_object* v_00_u03b1_1779_, lean_object* v_merger_1780_, lean_object* v_pm_1781_, lean_object* v_tt_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0(v_00_u03b1_1779_, v_merger_1780_, v_pm_1781_, v_tt_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0(lean_object* v_00_u03b4_1789_, lean_object* v_t_1790_, lean_object* v_k_1791_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_t_1790_, v_k_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___boxed(lean_object* v_00_u03b4_1793_, lean_object* v_t_1794_, lean_object* v_k_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0(v_00_u03b4_1793_, v_t_1794_, v_k_1795_);
lean_dec(v_k_1795_);
lean_dec(v_t_1794_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1(lean_object* v_00_u03b1_1797_, lean_object* v_00_u03b2_1798_, lean_object* v_f_1799_, lean_object* v_x_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1799_, v_x_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1807_, lean_object* v_00_u03b2_1808_, lean_object* v_f_1809_, lean_object* v_x_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1(v_00_u03b1_1807_, v_00_u03b2_1808_, v_f_1809_, v_x_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1817_, lean_object* v_00_u03b2_1818_, lean_object* v_f_1819_, size_t v_sz_1820_, size_t v_i_1821_, lean_object* v_bs_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_1819_, v_sz_1820_, v_i_1821_, v_bs_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1829_, lean_object* v_00_u03b2_1830_, lean_object* v_f_1831_, lean_object* v_sz_1832_, lean_object* v_i_1833_, lean_object* v_bs_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
size_t v_sz_boxed_1840_; size_t v_i_boxed_1841_; lean_object* v_res_1842_; 
v_sz_boxed_1840_ = lean_unbox_usize(v_sz_1832_);
lean_dec(v_sz_1832_);
v_i_boxed_1841_ = lean_unbox_usize(v_i_1833_);
lean_dec(v_i_1833_);
v_res_1842_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2(v_00_u03b1_1829_, v_00_u03b2_1830_, v_f_1831_, v_sz_boxed_1840_, v_i_boxed_1841_, v_bs_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
return v_res_1842_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1(void){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__0));
v___x_1845_ = l_Lean_stringToMessageData(v___x_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(uint8_t v_useAfter_1846_, lean_object* v_t_u2080_1847_, lean_object* v_h_u2081_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v_names_1854_; lean_object* v_fvarIds_1855_; lean_object* v_type_1856_; lean_object* v_val_x3f_1857_; lean_object* v_isInstance_x3f_1858_; lean_object* v_isType_x3f_1859_; lean_object* v_isInserted_x3f_1860_; lean_object* v_isRemoved_x3f_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1912_; 
v_names_1854_ = lean_ctor_get(v_h_u2081_1848_, 0);
v_fvarIds_1855_ = lean_ctor_get(v_h_u2081_1848_, 1);
v_type_1856_ = lean_ctor_get(v_h_u2081_1848_, 2);
v_val_x3f_1857_ = lean_ctor_get(v_h_u2081_1848_, 3);
v_isInstance_x3f_1858_ = lean_ctor_get(v_h_u2081_1848_, 4);
v_isType_x3f_1859_ = lean_ctor_get(v_h_u2081_1848_, 5);
v_isInserted_x3f_1860_ = lean_ctor_get(v_h_u2081_1848_, 6);
v_isRemoved_x3f_1861_ = lean_ctor_get(v_h_u2081_1848_, 7);
v_isSharedCheck_1912_ = !lean_is_exclusive(v_h_u2081_1848_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1863_ = v_h_u2081_1848_;
v_isShared_1864_ = v_isSharedCheck_1912_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_isRemoved_x3f_1861_);
lean_inc(v_isInserted_x3f_1860_);
lean_inc(v_isType_x3f_1859_);
lean_inc(v_isInstance_x3f_1858_);
lean_inc(v_val_x3f_1857_);
lean_inc(v_type_1856_);
lean_inc(v_fvarIds_1855_);
lean_inc(v_names_1854_);
lean_dec(v_h_u2081_1848_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1912_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; 
v___x_1865_ = lean_unsigned_to_nat(0u);
v___x_1866_ = lean_array_get_size(v_fvarIds_1855_);
v___x_1867_ = lean_nat_dec_lt(v___x_1865_, v___x_1866_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
lean_del_object(v___x_1863_);
lean_dec(v_isRemoved_x3f_1861_);
lean_dec(v_isInserted_x3f_1860_);
lean_dec(v_isType_x3f_1859_);
lean_dec(v_isInstance_x3f_1858_);
lean_dec(v_val_x3f_1857_);
lean_dec_ref(v_type_1856_);
lean_dec_ref(v_fvarIds_1855_);
lean_dec_ref(v_names_1854_);
lean_dec_ref(v_t_u2080_1847_);
v___x_1868_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1);
v___x_1869_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_1868_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_);
return v___x_1869_;
}
else
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1870_ = lean_array_fget_borrowed(v_fvarIds_1855_, v___x_1865_);
lean_inc(v___x_1870_);
v___x_1871_ = l_Lean_Expr_fvar___override(v___x_1870_);
lean_inc(v_a_1852_);
lean_inc_ref(v_a_1851_);
lean_inc(v_a_1850_);
lean_inc_ref(v_a_1849_);
v___x_1872_ = lean_infer_type(v___x_1871_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1874_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref(v___x_1872_);
v___x_1874_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(v_t_u2080_1847_, v_a_1873_, v_useAfter_1846_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; lean_object* v___x_1876_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_a_1875_);
lean_dec_ref(v___x_1874_);
v___x_1876_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(v_useAfter_1846_, v_a_1875_, v_type_1856_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1887_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1879_ = v___x_1876_;
v_isShared_1880_ = v_isSharedCheck_1887_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1876_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1887_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 2, v_a_1877_);
v___x_1882_ = v___x_1863_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_names_1854_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v_fvarIds_1855_);
lean_ctor_set(v_reuseFailAlloc_1886_, 2, v_a_1877_);
lean_ctor_set(v_reuseFailAlloc_1886_, 3, v_val_x3f_1857_);
lean_ctor_set(v_reuseFailAlloc_1886_, 4, v_isInstance_x3f_1858_);
lean_ctor_set(v_reuseFailAlloc_1886_, 5, v_isType_x3f_1859_);
lean_ctor_set(v_reuseFailAlloc_1886_, 6, v_isInserted_x3f_1860_);
lean_ctor_set(v_reuseFailAlloc_1886_, 7, v_isRemoved_x3f_1861_);
v___x_1882_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
lean_object* v___x_1884_; 
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v___x_1882_);
v___x_1884_ = v___x_1879_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1882_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_del_object(v___x_1863_);
lean_dec(v_isRemoved_x3f_1861_);
lean_dec(v_isInserted_x3f_1860_);
lean_dec(v_isType_x3f_1859_);
lean_dec(v_isInstance_x3f_1858_);
lean_dec(v_val_x3f_1857_);
lean_dec_ref(v_fvarIds_1855_);
lean_dec_ref(v_names_1854_);
v_a_1888_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1876_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1876_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
else
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1903_; 
lean_del_object(v___x_1863_);
lean_dec(v_isRemoved_x3f_1861_);
lean_dec(v_isInserted_x3f_1860_);
lean_dec(v_isType_x3f_1859_);
lean_dec(v_isInstance_x3f_1858_);
lean_dec(v_val_x3f_1857_);
lean_dec_ref(v_type_1856_);
lean_dec_ref(v_fvarIds_1855_);
lean_dec_ref(v_names_1854_);
v_a_1896_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1898_ = v___x_1874_;
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1874_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1899_ == 0)
{
v___x_1901_ = v___x_1898_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1896_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_del_object(v___x_1863_);
lean_dec(v_isRemoved_x3f_1861_);
lean_dec(v_isInserted_x3f_1860_);
lean_dec(v_isType_x3f_1859_);
lean_dec(v_isInstance_x3f_1858_);
lean_dec(v_val_x3f_1857_);
lean_dec_ref(v_type_1856_);
lean_dec_ref(v_fvarIds_1855_);
lean_dec_ref(v_names_1854_);
lean_dec_ref(v_t_u2080_1847_);
v_a_1904_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1872_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1872_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___boxed(lean_object* v_useAfter_1913_, lean_object* v_t_u2080_1914_, lean_object* v_h_u2081_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_){
_start:
{
uint8_t v_useAfter_boxed_1921_; lean_object* v_res_1922_; 
v_useAfter_boxed_1921_ = lean_unbox(v_useAfter_1913_);
v_res_1922_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(v_useAfter_boxed_1921_, v_t_u2080_1914_, v_h_u2081_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_);
lean_dec(v_a_1919_);
lean_dec_ref(v_a_1918_);
lean_dec(v_a_1917_);
lean_dec_ref(v_a_1916_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(lean_object* v_ctx_u2080_1926_, uint8_t v_useAfter_1927_, lean_object* v_h_u2081_1928_, lean_object* v___x_1929_, lean_object* v___x_1930_, lean_object* v_as_1931_, size_t v_sz_1932_, size_t v_i_1933_, lean_object* v_b_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
uint8_t v___x_1940_; 
v___x_1940_ = lean_usize_dec_lt(v_i_1933_, v_sz_1932_);
if (v___x_1940_ == 0)
{
lean_object* v___x_1941_; 
lean_dec_ref(v___x_1930_);
lean_dec_ref(v___x_1929_);
lean_dec_ref(v_h_u2081_1928_);
lean_dec_ref(v_ctx_u2080_1926_);
v___x_1941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1941_, 0, v_b_1934_);
return v___x_1941_;
}
else
{
lean_object* v_a_1942_; lean_object* v_fst_1943_; lean_object* v_snd_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_2030_; 
lean_dec_ref(v_b_1934_);
v_a_1942_ = lean_array_uget(v_as_1931_, v_i_1933_);
v_fst_1943_ = lean_ctor_get(v_a_1942_, 0);
v_snd_1944_ = lean_ctor_get(v_a_1942_, 1);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_a_1942_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_1946_ = v_a_1942_;
v_isShared_1947_ = v_isSharedCheck_2030_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_snd_1944_);
lean_inc(v_fst_1943_);
lean_dec(v_a_1942_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_2030_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1948_; uint8_t v___x_1949_; 
v___x_1948_ = lean_box(0);
lean_inc_ref(v_ctx_u2080_1926_);
v___x_1949_ = l_Lean_LocalContext_contains(v_ctx_u2080_1926_, v_snd_1944_);
lean_dec(v_snd_1944_);
if (v___x_1949_ == 0)
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1950_ = lean_box(0);
v___x_1951_ = l_Lean_Name_str___override(v___x_1950_, v_fst_1943_);
v___x_1952_ = l_Lean_LocalContext_findFromUserName_x3f(v_ctx_u2080_1926_, v___x_1951_);
lean_dec(v___x_1951_);
lean_dec_ref(v_ctx_u2080_1926_);
if (lean_obj_tag(v___x_1952_) == 1)
{
lean_object* v_val_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1981_; 
lean_dec_ref(v___x_1930_);
lean_dec_ref(v___x_1929_);
v_val_1953_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1955_ = v___x_1952_;
v_isShared_1956_ = v_isSharedCheck_1981_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_val_1953_);
lean_dec(v___x_1952_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1981_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = l_Lean_LocalDecl_type(v_val_1953_);
lean_dec(v_val_1953_);
v___x_1958_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(v_useAfter_1927_, v___x_1957_, v_h_u2081_1928_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1972_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1961_ = v___x_1958_;
v_isShared_1962_ = v_isSharedCheck_1972_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1958_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1972_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 0, v_a_1959_);
v___x_1964_ = v___x_1955_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
lean_object* v___x_1966_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 1, v___x_1948_);
lean_ctor_set(v___x_1946_, 0, v___x_1964_);
v___x_1966_ = v___x_1946_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1964_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v___x_1948_);
v___x_1966_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
lean_object* v___x_1968_; 
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 0, v___x_1966_);
v___x_1968_ = v___x_1961_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1966_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
}
else
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
lean_del_object(v___x_1955_);
lean_del_object(v___x_1946_);
v_a_1973_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1958_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1958_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
}
else
{
lean_dec(v___x_1952_);
if (v_useAfter_1927_ == 0)
{
lean_object* v_type_1982_; lean_object* v_val_x3f_1983_; lean_object* v_isInstance_x3f_1984_; lean_object* v_isType_x3f_1985_; lean_object* v_isInserted_x3f_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_2000_; 
v_type_1982_ = lean_ctor_get(v_h_u2081_1928_, 2);
v_val_x3f_1983_ = lean_ctor_get(v_h_u2081_1928_, 3);
v_isInstance_x3f_1984_ = lean_ctor_get(v_h_u2081_1928_, 4);
v_isType_x3f_1985_ = lean_ctor_get(v_h_u2081_1928_, 5);
v_isInserted_x3f_1986_ = lean_ctor_get(v_h_u2081_1928_, 6);
v_isSharedCheck_2000_ = !lean_is_exclusive(v_h_u2081_1928_);
if (v_isSharedCheck_2000_ == 0)
{
lean_object* v_unused_2001_; lean_object* v_unused_2002_; lean_object* v_unused_2003_; 
v_unused_2001_ = lean_ctor_get(v_h_u2081_1928_, 7);
lean_dec(v_unused_2001_);
v_unused_2002_ = lean_ctor_get(v_h_u2081_1928_, 1);
lean_dec(v_unused_2002_);
v_unused_2003_ = lean_ctor_get(v_h_u2081_1928_, 0);
lean_dec(v_unused_2003_);
v___x_1988_ = v_h_u2081_1928_;
v_isShared_1989_ = v_isSharedCheck_2000_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_isInserted_x3f_1986_);
lean_inc(v_isType_x3f_1985_);
lean_inc(v_isInstance_x3f_1984_);
lean_inc(v_val_x3f_1983_);
lean_inc(v_type_1982_);
lean_dec(v_h_u2081_1928_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_2000_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1993_; 
v___x_1990_ = lean_box(v___x_1940_);
v___x_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1990_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 7, v___x_1991_);
lean_ctor_set(v___x_1988_, 1, v___x_1930_);
lean_ctor_set(v___x_1988_, 0, v___x_1929_);
v___x_1993_ = v___x_1988_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1929_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v___x_1930_);
lean_ctor_set(v_reuseFailAlloc_1999_, 2, v_type_1982_);
lean_ctor_set(v_reuseFailAlloc_1999_, 3, v_val_x3f_1983_);
lean_ctor_set(v_reuseFailAlloc_1999_, 4, v_isInstance_x3f_1984_);
lean_ctor_set(v_reuseFailAlloc_1999_, 5, v_isType_x3f_1985_);
lean_ctor_set(v_reuseFailAlloc_1999_, 6, v_isInserted_x3f_1986_);
lean_ctor_set(v_reuseFailAlloc_1999_, 7, v___x_1991_);
v___x_1993_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
lean_object* v___x_1994_; lean_object* v___x_1996_; 
v___x_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1993_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 1, v___x_1948_);
lean_ctor_set(v___x_1946_, 0, v___x_1994_);
v___x_1996_ = v___x_1946_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1994_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v___x_1948_);
v___x_1996_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
lean_object* v___x_1997_; 
v___x_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
return v___x_1997_;
}
}
}
}
else
{
lean_object* v_type_2004_; lean_object* v_val_x3f_2005_; lean_object* v_isInstance_x3f_2006_; lean_object* v_isType_x3f_2007_; lean_object* v_isRemoved_x3f_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2022_; 
v_type_2004_ = lean_ctor_get(v_h_u2081_1928_, 2);
v_val_x3f_2005_ = lean_ctor_get(v_h_u2081_1928_, 3);
v_isInstance_x3f_2006_ = lean_ctor_get(v_h_u2081_1928_, 4);
v_isType_x3f_2007_ = lean_ctor_get(v_h_u2081_1928_, 5);
v_isRemoved_x3f_2008_ = lean_ctor_get(v_h_u2081_1928_, 7);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_h_u2081_1928_);
if (v_isSharedCheck_2022_ == 0)
{
lean_object* v_unused_2023_; lean_object* v_unused_2024_; lean_object* v_unused_2025_; 
v_unused_2023_ = lean_ctor_get(v_h_u2081_1928_, 6);
lean_dec(v_unused_2023_);
v_unused_2024_ = lean_ctor_get(v_h_u2081_1928_, 1);
lean_dec(v_unused_2024_);
v_unused_2025_ = lean_ctor_get(v_h_u2081_1928_, 0);
lean_dec(v_unused_2025_);
v___x_2010_ = v_h_u2081_1928_;
v_isShared_2011_ = v_isSharedCheck_2022_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_isRemoved_x3f_2008_);
lean_inc(v_isType_x3f_2007_);
lean_inc(v_isInstance_x3f_2006_);
lean_inc(v_val_x3f_2005_);
lean_inc(v_type_2004_);
lean_dec(v_h_u2081_1928_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2022_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2015_; 
v___x_2012_ = lean_box(v___x_1940_);
v___x_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2012_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 6, v___x_2013_);
lean_ctor_set(v___x_2010_, 1, v___x_1930_);
lean_ctor_set(v___x_2010_, 0, v___x_1929_);
v___x_2015_ = v___x_2010_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_1929_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v___x_1930_);
lean_ctor_set(v_reuseFailAlloc_2021_, 2, v_type_2004_);
lean_ctor_set(v_reuseFailAlloc_2021_, 3, v_val_x3f_2005_);
lean_ctor_set(v_reuseFailAlloc_2021_, 4, v_isInstance_x3f_2006_);
lean_ctor_set(v_reuseFailAlloc_2021_, 5, v_isType_x3f_2007_);
lean_ctor_set(v_reuseFailAlloc_2021_, 6, v___x_2013_);
lean_ctor_set(v_reuseFailAlloc_2021_, 7, v_isRemoved_x3f_2008_);
v___x_2015_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
lean_object* v___x_2016_; lean_object* v___x_2018_; 
v___x_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2015_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 1, v___x_1948_);
lean_ctor_set(v___x_1946_, 0, v___x_2016_);
v___x_2018_ = v___x_1946_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2016_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v___x_1948_);
v___x_2018_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
lean_object* v___x_2019_; 
v___x_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
return v___x_2019_;
}
}
}
}
}
}
else
{
lean_object* v___x_2026_; size_t v___x_2027_; size_t v___x_2028_; 
lean_del_object(v___x_1946_);
lean_dec(v_fst_1943_);
v___x_2026_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___closed__0));
v___x_2027_ = ((size_t)1ULL);
v___x_2028_ = lean_usize_add(v_i_1933_, v___x_2027_);
v_i_1933_ = v___x_2028_;
v_b_1934_ = v___x_2026_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___boxed(lean_object* v_ctx_u2080_2031_, lean_object* v_useAfter_2032_, lean_object* v_h_u2081_2033_, lean_object* v___x_2034_, lean_object* v___x_2035_, lean_object* v_as_2036_, lean_object* v_sz_2037_, lean_object* v_i_2038_, lean_object* v_b_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
uint8_t v_useAfter_boxed_2045_; size_t v_sz_boxed_2046_; size_t v_i_boxed_2047_; lean_object* v_res_2048_; 
v_useAfter_boxed_2045_ = lean_unbox(v_useAfter_2032_);
v_sz_boxed_2046_ = lean_unbox_usize(v_sz_2037_);
lean_dec(v_sz_2037_);
v_i_boxed_2047_ = lean_unbox_usize(v_i_2038_);
lean_dec(v_i_2038_);
v_res_2048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(v_ctx_u2080_2031_, v_useAfter_boxed_2045_, v_h_u2081_2033_, v___x_2034_, v___x_2035_, v_as_2036_, v_sz_boxed_2046_, v_i_boxed_2047_, v_b_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec_ref(v_as_2036_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(uint8_t v_useAfter_2049_, lean_object* v_ctx_u2080_2050_, lean_object* v_h_u2081_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_){
_start:
{
lean_object* v_names_2057_; lean_object* v_fvarIds_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; size_t v_sz_2061_; size_t v___x_2062_; lean_object* v___x_2063_; 
v_names_2057_ = lean_ctor_get(v_h_u2081_2051_, 0);
v_fvarIds_2058_ = lean_ctor_get(v_h_u2081_2051_, 1);
v___x_2059_ = l_Array_zip___redArg(v_names_2057_, v_fvarIds_2058_);
v___x_2060_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___closed__0));
v_sz_2061_ = lean_array_size(v___x_2059_);
v___x_2062_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_2058_);
lean_inc_ref(v_names_2057_);
lean_inc_ref(v_h_u2081_2051_);
v___x_2063_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(v_ctx_u2080_2050_, v_useAfter_2049_, v_h_u2081_2051_, v_names_2057_, v_fvarIds_2058_, v___x_2059_, v_sz_2061_, v___x_2062_, v___x_2060_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_);
lean_dec_ref(v___x_2059_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2076_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2066_ = v___x_2063_;
v_isShared_2067_ = v_isSharedCheck_2076_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2063_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2076_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v_fst_2068_; 
v_fst_2068_ = lean_ctor_get(v_a_2064_, 0);
lean_inc(v_fst_2068_);
lean_dec(v_a_2064_);
if (lean_obj_tag(v_fst_2068_) == 0)
{
lean_object* v___x_2070_; 
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 0, v_h_u2081_2051_);
v___x_2070_ = v___x_2066_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_h_u2081_2051_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
else
{
lean_object* v_val_2072_; lean_object* v___x_2074_; 
lean_dec_ref(v_h_u2081_2051_);
v_val_2072_ = lean_ctor_get(v_fst_2068_, 0);
lean_inc(v_val_2072_);
lean_dec_ref(v_fst_2068_);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 0, v_val_2072_);
v___x_2074_ = v___x_2066_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_val_2072_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
lean_dec_ref(v_h_u2081_2051_);
v_a_2077_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2063_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2063_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle___boxed(lean_object* v_useAfter_2085_, lean_object* v_ctx_u2080_2086_, lean_object* v_h_u2081_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_){
_start:
{
uint8_t v_useAfter_boxed_2093_; lean_object* v_res_2094_; 
v_useAfter_boxed_2093_ = lean_unbox(v_useAfter_2085_);
v_res_2094_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(v_useAfter_boxed_2093_, v_ctx_u2080_2086_, v_h_u2081_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_);
lean_dec(v_a_2091_);
lean_dec_ref(v_a_2090_);
lean_dec(v_a_2089_);
lean_dec_ref(v_a_2088_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(uint8_t v_useAfter_2095_, lean_object* v_lctx_u2080_2096_, size_t v_sz_2097_, size_t v_i_2098_, lean_object* v_bs_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
uint8_t v___x_2105_; 
v___x_2105_ = lean_usize_dec_lt(v_i_2098_, v_sz_2097_);
if (v___x_2105_ == 0)
{
lean_object* v___x_2106_; 
lean_dec_ref(v_lctx_u2080_2096_);
v___x_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2106_, 0, v_bs_2099_);
return v___x_2106_;
}
else
{
lean_object* v_v_2107_; lean_object* v___x_2108_; 
v_v_2107_ = lean_array_uget_borrowed(v_bs_2099_, v_i_2098_);
lean_inc(v_v_2107_);
lean_inc_ref(v_lctx_u2080_2096_);
v___x_2108_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(v_useAfter_2095_, v_lctx_u2080_2096_, v_v_2107_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; lean_object* v___x_2110_; lean_object* v_bs_x27_2111_; size_t v___x_2112_; size_t v___x_2113_; lean_object* v___x_2114_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref(v___x_2108_);
v___x_2110_ = lean_unsigned_to_nat(0u);
v_bs_x27_2111_ = lean_array_uset(v_bs_2099_, v_i_2098_, v___x_2110_);
v___x_2112_ = ((size_t)1ULL);
v___x_2113_ = lean_usize_add(v_i_2098_, v___x_2112_);
v___x_2114_ = lean_array_uset(v_bs_x27_2111_, v_i_2098_, v_a_2109_);
v_i_2098_ = v___x_2113_;
v_bs_2099_ = v___x_2114_;
goto _start;
}
else
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
lean_dec_ref(v_bs_2099_);
lean_dec_ref(v_lctx_u2080_2096_);
v_a_2116_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___x_2108_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2108_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_a_2116_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0___boxed(lean_object* v_useAfter_2124_, lean_object* v_lctx_u2080_2125_, lean_object* v_sz_2126_, lean_object* v_i_2127_, lean_object* v_bs_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
uint8_t v_useAfter_boxed_2134_; size_t v_sz_boxed_2135_; size_t v_i_boxed_2136_; lean_object* v_res_2137_; 
v_useAfter_boxed_2134_ = lean_unbox(v_useAfter_2124_);
v_sz_boxed_2135_ = lean_unbox_usize(v_sz_2126_);
lean_dec(v_sz_2126_);
v_i_boxed_2136_ = lean_unbox_usize(v_i_2127_);
lean_dec(v_i_2127_);
v_res_2137_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(v_useAfter_boxed_2134_, v_lctx_u2080_2125_, v_sz_boxed_2135_, v_i_boxed_2136_, v_bs_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(uint8_t v_useAfter_2138_, lean_object* v_lctx_u2080_2139_, lean_object* v_hs_u2081_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_){
_start:
{
size_t v_sz_2146_; size_t v___x_2147_; lean_object* v___x_2148_; 
v_sz_2146_ = lean_array_size(v_hs_u2081_2140_);
v___x_2147_ = ((size_t)0ULL);
v___x_2148_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(v_useAfter_2138_, v_lctx_u2080_2139_, v_sz_2146_, v___x_2147_, v_hs_u2081_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses___boxed(lean_object* v_useAfter_2149_, lean_object* v_lctx_u2080_2150_, lean_object* v_hs_u2081_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_){
_start:
{
uint8_t v_useAfter_boxed_2157_; lean_object* v_res_2158_; 
v_useAfter_boxed_2157_ = lean_unbox(v_useAfter_2149_);
v_res_2158_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(v_useAfter_boxed_2157_, v_lctx_u2080_2150_, v_hs_u2081_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
lean_dec(v_a_2155_);
lean_dec_ref(v_a_2154_);
lean_dec(v_a_2153_);
lean_dec_ref(v_a_2152_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal_spec__0___redArg(lean_object* v_e_2159_, lean_object* v___y_2160_){
_start:
{
uint8_t v___x_2162_; 
v___x_2162_ = l_Lean_Expr_hasMVar(v_e_2159_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2163_; 
v___x_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2163_, 0, v_e_2159_);
return v___x_2163_;
}
else
{
lean_object* v___x_2164_; lean_object* v_mctx_2165_; lean_object* v___x_2166_; lean_object* v_fst_2167_; lean_object* v_snd_2168_; lean_object* v___x_2169_; lean_object* v_cache_2170_; lean_object* v_zetaDeltaFVarIds_2171_; lean_object* v_postponed_2172_; lean_object* v_diag_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2182_; 
v___x_2164_ = lean_st_ref_get(v___y_2160_);
v_mctx_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc_ref(v_mctx_2165_);
lean_dec(v___x_2164_);
v___x_2166_ = l_Lean_instantiateMVarsCore(v_mctx_2165_, v_e_2159_);
v_fst_2167_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_fst_2167_);
v_snd_2168_ = lean_ctor_get(v___x_2166_, 1);
lean_inc(v_snd_2168_);
lean_dec_ref(v___x_2166_);
v___x_2169_ = lean_st_ref_take(v___y_2160_);
v_cache_2170_ = lean_ctor_get(v___x_2169_, 1);
v_zetaDeltaFVarIds_2171_ = lean_ctor_get(v___x_2169_, 2);
v_postponed_2172_ = lean_ctor_get(v___x_2169_, 3);
v_diag_2173_ = lean_ctor_get(v___x_2169_, 4);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2182_ == 0)
{
lean_object* v_unused_2183_; 
v_unused_2183_ = lean_ctor_get(v___x_2169_, 0);
lean_dec(v_unused_2183_);
v___x_2175_ = v___x_2169_;
v_isShared_2176_ = v_isSharedCheck_2182_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_diag_2173_);
lean_inc(v_postponed_2172_);
lean_inc(v_zetaDeltaFVarIds_2171_);
lean_inc(v_cache_2170_);
lean_dec(v___x_2169_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2182_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 0, v_snd_2168_);
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_snd_2168_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_cache_2170_);
lean_ctor_set(v_reuseFailAlloc_2181_, 2, v_zetaDeltaFVarIds_2171_);
lean_ctor_set(v_reuseFailAlloc_2181_, 3, v_postponed_2172_);
lean_ctor_set(v_reuseFailAlloc_2181_, 4, v_diag_2173_);
v___x_2178_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2179_ = lean_st_ref_set(v___y_2160_, v___x_2178_);
v___x_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2180_, 0, v_fst_2167_);
return v___x_2180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal_spec__0___redArg___boxed(lean_object* v_e_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal_spec__0___redArg(v_e_2184_, v___y_2185_);
lean_dec(v___y_2185_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal_spec__0(lean_object* v_e_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal_spec__0___redArg(v_e_2188_, v___y_2190_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal_spec__0___boxed(lean_object* v_e_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal_spec__0(v_e_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
return v_res_2201_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2(void){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2206_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__1));
v___x_2207_ = l_Lean_stringToMessageData(v___x_2206_);
return v___x_2207_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4(void){
_start:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2209_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__3));
v___x_2210_ = l_Lean_stringToMessageData(v___x_2209_);
return v___x_2210_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6(void){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__5));
v___x_2213_ = l_Lean_stringToMessageData(v___x_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(uint8_t v_useAfter_2214_, lean_object* v_g_u2080_2215_, lean_object* v_i_u2081_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_){
_start:
{
lean_object* v___x_2222_; lean_object* v_mctx_2223_; lean_object* v___x_2224_; 
v___x_2222_ = lean_st_ref_get(v_a_2218_);
v_mctx_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc_ref(v_mctx_2223_);
lean_dec(v___x_2222_);
v___x_2224_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2223_, v_g_u2080_2215_);
if (lean_obj_tag(v___x_2224_) == 1)
{
lean_object* v_val_2225_; lean_object* v_options_2226_; lean_object* v_lctx_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v_toInteractiveGoalCore_2231_; lean_object* v_fst_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2329_; 
v_val_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_val_2225_);
lean_dec_ref(v___x_2224_);
v_options_2226_ = lean_ctor_get(v_a_2219_, 2);
v_lctx_2227_ = lean_ctor_get(v_val_2225_, 1);
lean_inc_ref(v_lctx_2227_);
lean_dec(v_val_2225_);
v___x_2228_ = lean_box(1);
lean_inc_ref(v_options_2226_);
v___x_2229_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2229_, 0, v_options_2226_);
lean_ctor_set(v___x_2229_, 1, v___x_2228_);
lean_ctor_set(v___x_2229_, 2, v___x_2228_);
v___x_2230_ = l_Lean_LocalContext_sanitizeNames(v_lctx_2227_, v___x_2229_);
v_toInteractiveGoalCore_2231_ = lean_ctor_get(v_i_u2081_2216_, 0);
lean_inc_ref(v_toInteractiveGoalCore_2231_);
v_fst_2232_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2329_ == 0)
{
lean_object* v_unused_2330_; 
v_unused_2330_ = lean_ctor_get(v___x_2230_, 1);
lean_dec(v_unused_2330_);
v___x_2234_ = v___x_2230_;
v_isShared_2235_ = v_isSharedCheck_2329_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_fst_2232_);
lean_dec(v___x_2230_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2329_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v_userName_x3f_2236_; lean_object* v_goalPrefix_2237_; lean_object* v_mvarId_2238_; lean_object* v_isRemoved_x3f_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2326_; 
v_userName_x3f_2236_ = lean_ctor_get(v_i_u2081_2216_, 1);
v_goalPrefix_2237_ = lean_ctor_get(v_i_u2081_2216_, 2);
v_mvarId_2238_ = lean_ctor_get(v_i_u2081_2216_, 3);
v_isRemoved_x3f_2239_ = lean_ctor_get(v_i_u2081_2216_, 5);
v_isSharedCheck_2326_ = !lean_is_exclusive(v_i_u2081_2216_);
if (v_isSharedCheck_2326_ == 0)
{
lean_object* v_unused_2327_; lean_object* v_unused_2328_; 
v_unused_2327_ = lean_ctor_get(v_i_u2081_2216_, 4);
lean_dec(v_unused_2327_);
v_unused_2328_ = lean_ctor_get(v_i_u2081_2216_, 0);
lean_dec(v_unused_2328_);
v___x_2241_ = v_i_u2081_2216_;
v_isShared_2242_ = v_isSharedCheck_2326_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_isRemoved_x3f_2239_);
lean_inc(v_mvarId_2238_);
lean_inc(v_goalPrefix_2237_);
lean_inc(v_userName_x3f_2236_);
lean_dec(v_i_u2081_2216_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2326_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v_hyps_2243_; lean_object* v_type_2244_; lean_object* v_ctx_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2325_; 
v_hyps_2243_ = lean_ctor_get(v_toInteractiveGoalCore_2231_, 0);
v_type_2244_ = lean_ctor_get(v_toInteractiveGoalCore_2231_, 1);
v_ctx_2245_ = lean_ctor_get(v_toInteractiveGoalCore_2231_, 2);
v_isSharedCheck_2325_ = !lean_is_exclusive(v_toInteractiveGoalCore_2231_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2247_ = v_toInteractiveGoalCore_2231_;
v_isShared_2248_ = v_isSharedCheck_2325_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_ctx_2245_);
lean_inc(v_type_2244_);
lean_inc(v_hyps_2243_);
lean_dec(v_toInteractiveGoalCore_2231_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2325_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2249_; 
v___x_2249_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(v_useAfter_2214_, v_fst_2232_, v_hyps_2243_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_a_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_a_2250_);
lean_dec_ref(v___x_2249_);
v___x_2251_ = l_Lean_Expr_mvar___override(v_g_u2080_2215_);
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
v___x_2252_ = lean_infer_type(v___x_2251_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_a_2253_; lean_object* v___x_2254_; lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2308_; 
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_a_2253_);
lean_dec_ref(v___x_2252_);
v___x_2254_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal_spec__0___redArg(v_a_2253_, v_a_2218_);
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2257_ = v___x_2254_;
v_isShared_2258_ = v_isSharedCheck_2308_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2254_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2308_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2259_; lean_object* v_mctx_2260_; lean_object* v___x_2261_; 
v___x_2259_ = lean_st_ref_get(v_a_2218_);
v_mctx_2260_ = lean_ctor_get(v___x_2259_, 0);
lean_inc_ref(v_mctx_2260_);
lean_dec(v___x_2259_);
v___x_2261_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2260_, v_mvarId_2238_);
if (lean_obj_tag(v___x_2261_) == 1)
{
lean_object* v_val_2262_; lean_object* v_type_2263_; lean_object* v___x_2264_; lean_object* v_a_2265_; lean_object* v___x_2266_; 
lean_del_object(v___x_2257_);
lean_del_object(v___x_2234_);
v_val_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_val_2262_);
lean_dec_ref(v___x_2261_);
v_type_2263_ = lean_ctor_get(v_val_2262_, 2);
lean_inc_ref(v_type_2263_);
lean_dec(v_val_2262_);
v___x_2264_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal_spec__0___redArg(v_type_2263_, v_a_2218_);
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc(v_a_2265_);
lean_dec_ref(v___x_2264_);
v___x_2266_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(v_a_2255_, v_a_2265_, v_useAfter_2214_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; lean_object* v___x_2268_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_a_2267_);
lean_dec_ref(v___x_2266_);
v___x_2268_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(v_useAfter_2214_, v_a_2267_, v_type_2244_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2283_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2271_ = v___x_2268_;
v_isShared_2272_ = v_isSharedCheck_2283_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2268_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2283_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 1, v_a_2269_);
lean_ctor_set(v___x_2247_, 0, v_a_2250_);
v___x_2274_ = v___x_2247_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2250_);
lean_ctor_set(v_reuseFailAlloc_2282_, 1, v_a_2269_);
lean_ctor_set(v_reuseFailAlloc_2282_, 2, v_ctx_2245_);
v___x_2274_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
lean_object* v___x_2275_; lean_object* v___x_2277_; 
v___x_2275_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__0));
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 4, v___x_2275_);
lean_ctor_set(v___x_2241_, 0, v___x_2274_);
v___x_2277_ = v___x_2241_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2274_);
lean_ctor_set(v_reuseFailAlloc_2281_, 1, v_userName_x3f_2236_);
lean_ctor_set(v_reuseFailAlloc_2281_, 2, v_goalPrefix_2237_);
lean_ctor_set(v_reuseFailAlloc_2281_, 3, v_mvarId_2238_);
lean_ctor_set(v_reuseFailAlloc_2281_, 4, v___x_2275_);
lean_ctor_set(v_reuseFailAlloc_2281_, 5, v_isRemoved_x3f_2239_);
v___x_2277_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
lean_object* v___x_2279_; 
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 0, v___x_2277_);
v___x_2279_ = v___x_2271_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2277_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_dec(v_a_2250_);
lean_del_object(v___x_2247_);
lean_dec_ref(v_ctx_2245_);
lean_del_object(v___x_2241_);
lean_dec(v_isRemoved_x3f_2239_);
lean_dec(v_mvarId_2238_);
lean_dec_ref(v_goalPrefix_2237_);
lean_dec(v_userName_x3f_2236_);
v_a_2284_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2268_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2268_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_dec(v_a_2250_);
lean_del_object(v___x_2247_);
lean_dec_ref(v_ctx_2245_);
lean_dec_ref(v_type_2244_);
lean_del_object(v___x_2241_);
lean_dec(v_isRemoved_x3f_2239_);
lean_dec(v_mvarId_2238_);
lean_dec_ref(v_goalPrefix_2237_);
lean_dec(v_userName_x3f_2236_);
v_a_2292_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2266_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2266_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
else
{
lean_object* v___x_2300_; lean_object* v___x_2302_; 
lean_dec(v___x_2261_);
lean_dec(v_a_2255_);
lean_dec(v_a_2250_);
lean_del_object(v___x_2247_);
lean_dec_ref(v_ctx_2245_);
lean_dec_ref(v_type_2244_);
lean_del_object(v___x_2241_);
lean_dec(v_isRemoved_x3f_2239_);
lean_dec_ref(v_goalPrefix_2237_);
lean_dec(v_userName_x3f_2236_);
v___x_2300_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2);
if (v_isShared_2258_ == 0)
{
lean_ctor_set_tag(v___x_2257_, 1);
lean_ctor_set(v___x_2257_, 0, v_mvarId_2238_);
v___x_2302_ = v___x_2257_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_mvarId_2238_);
v___x_2302_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
lean_object* v___x_2304_; 
if (v_isShared_2235_ == 0)
{
lean_ctor_set_tag(v___x_2234_, 7);
lean_ctor_set(v___x_2234_, 1, v___x_2302_);
lean_ctor_set(v___x_2234_, 0, v___x_2300_);
v___x_2304_ = v___x_2234_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2300_);
lean_ctor_set(v_reuseFailAlloc_2306_, 1, v___x_2302_);
v___x_2304_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
lean_object* v___x_2305_; 
v___x_2305_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_2304_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
return v___x_2305_;
}
}
}
}
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
lean_dec(v_a_2250_);
lean_del_object(v___x_2247_);
lean_dec_ref(v_ctx_2245_);
lean_dec_ref(v_type_2244_);
lean_del_object(v___x_2241_);
lean_dec(v_isRemoved_x3f_2239_);
lean_dec(v_mvarId_2238_);
lean_dec_ref(v_goalPrefix_2237_);
lean_dec(v_userName_x3f_2236_);
lean_del_object(v___x_2234_);
v_a_2309_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2252_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2252_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
else
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2324_; 
lean_del_object(v___x_2247_);
lean_dec_ref(v_ctx_2245_);
lean_dec_ref(v_type_2244_);
lean_del_object(v___x_2241_);
lean_dec(v_isRemoved_x3f_2239_);
lean_dec(v_mvarId_2238_);
lean_dec_ref(v_goalPrefix_2237_);
lean_dec(v_userName_x3f_2236_);
lean_del_object(v___x_2234_);
lean_dec(v_g_u2080_2215_);
v_a_2317_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2319_ = v___x_2249_;
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2249_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2322_; 
if (v_isShared_2320_ == 0)
{
v___x_2322_ = v___x_2319_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_a_2317_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
lean_dec(v___x_2224_);
lean_dec_ref(v_i_u2081_2216_);
v___x_2331_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4);
v___x_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2332_, 0, v_g_u2080_2215_);
v___x_2333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2331_);
lean_ctor_set(v___x_2333_, 1, v___x_2332_);
v___x_2334_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6);
v___x_2335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2333_);
lean_ctor_set(v___x_2335_, 1, v___x_2334_);
v___x_2336_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_2335_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
return v___x_2336_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___boxed(lean_object* v_useAfter_2337_, lean_object* v_g_u2080_2338_, lean_object* v_i_u2081_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_){
_start:
{
uint8_t v_useAfter_boxed_2345_; lean_object* v_res_2346_; 
v_useAfter_boxed_2345_ = lean_unbox(v_useAfter_2337_);
v_res_2346_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(v_useAfter_boxed_2345_, v_g_u2080_2338_, v_i_u2081_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_);
lean_dec(v_a_2343_);
lean_dec_ref(v_a_2342_);
lean_dec(v_a_2341_);
lean_dec_ref(v_a_2340_);
return v_res_2346_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(lean_object* v_opts_2347_, lean_object* v_opt_2348_){
_start:
{
lean_object* v_name_2349_; lean_object* v_defValue_2350_; lean_object* v_map_2351_; lean_object* v___x_2352_; 
v_name_2349_ = lean_ctor_get(v_opt_2348_, 0);
v_defValue_2350_ = lean_ctor_get(v_opt_2348_, 1);
v_map_2351_ = lean_ctor_get(v_opts_2347_, 0);
v___x_2352_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2351_, v_name_2349_);
if (lean_obj_tag(v___x_2352_) == 0)
{
uint8_t v___x_2353_; 
v___x_2353_ = lean_unbox(v_defValue_2350_);
return v___x_2353_;
}
else
{
lean_object* v_val_2354_; 
v_val_2354_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_val_2354_);
lean_dec_ref(v___x_2352_);
if (lean_obj_tag(v_val_2354_) == 1)
{
uint8_t v_v_2355_; 
v_v_2355_ = lean_ctor_get_uint8(v_val_2354_, 0);
lean_dec_ref(v_val_2354_);
return v_v_2355_;
}
else
{
uint8_t v___x_2356_; 
lean_dec(v_val_2354_);
v___x_2356_ = lean_unbox(v_defValue_2350_);
return v___x_2356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0___boxed(lean_object* v_opts_2357_, lean_object* v_opt_2358_){
_start:
{
uint8_t v_res_2359_; lean_object* v_r_2360_; 
v_res_2359_ = l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(v_opts_2357_, v_opt_2358_);
lean_dec_ref(v_opt_2358_);
lean_dec_ref(v_opts_2357_);
v_r_2360_ = lean_box(v_res_2359_);
return v_r_2360_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(lean_object* v_x_2361_, lean_object* v_x_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
if (lean_obj_tag(v_x_2362_) == 0)
{
lean_object* v___x_2368_; 
v___x_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2368_, 0, v_x_2361_);
return v___x_2368_;
}
else
{
lean_object* v_head_2369_; lean_object* v_tail_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
v_head_2369_ = lean_ctor_get(v_x_2362_, 0);
lean_inc(v_head_2369_);
v_tail_2370_ = lean_ctor_get(v_x_2362_, 1);
lean_inc(v_tail_2370_);
lean_dec_ref(v_x_2362_);
lean_inc(v_head_2369_);
v___x_2371_ = l_Lean_Expr_mvar___override(v_head_2369_);
v___x_2372_ = l_Lean_Meta_getMVars(v___x_2371_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v_a_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
lean_inc(v_a_2373_);
lean_dec_ref(v___x_2372_);
v___x_2374_ = l_Lean_MVarIdSet_ofArray(v_a_2373_);
lean_dec(v_a_2373_);
v___x_2375_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_head_2369_, v___x_2374_, v_x_2361_);
v_x_2361_ = v___x_2375_;
v_x_2362_ = v_tail_2370_;
goto _start;
}
else
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
lean_dec(v_tail_2370_);
lean_dec(v_head_2369_);
lean_dec(v_x_2361_);
v_a_2377_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2379_ = v___x_2372_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2372_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1___boxed(lean_object* v_x_2385_, lean_object* v_x_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(v_x_2385_, v_x_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
return v_res_2392_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__1(uint8_t v___y_2393_, lean_object* v___f_2394_, lean_object* v_mvarId_2395_, lean_object* v_g_u2080_2396_){
_start:
{
if (v___y_2393_ == 0)
{
lean_object* v___x_2397_; uint8_t v___x_2398_; 
v___x_2397_ = lean_apply_2(v___f_2394_, v_mvarId_2395_, v_g_u2080_2396_);
v___x_2398_ = lean_unbox(v___x_2397_);
return v___x_2398_;
}
else
{
lean_object* v___x_2399_; uint8_t v___x_2400_; 
v___x_2399_ = lean_apply_2(v___f_2394_, v_g_u2080_2396_, v_mvarId_2395_);
v___x_2400_ = lean_unbox(v___x_2399_);
return v___x_2400_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__1___boxed(lean_object* v___y_2401_, lean_object* v___f_2402_, lean_object* v_mvarId_2403_, lean_object* v_g_u2080_2404_){
_start:
{
uint8_t v___y_3395__boxed_2405_; uint8_t v_res_2406_; lean_object* v_r_2407_; 
v___y_3395__boxed_2405_ = lean_unbox(v___y_2401_);
v_res_2406_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__1(v___y_3395__boxed_2405_, v___f_2402_, v_mvarId_2403_, v_g_u2080_2404_);
v_r_2407_ = lean_box(v_res_2406_);
return v_r_2407_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(lean_object* v_t_2408_, lean_object* v_k_2409_){
_start:
{
if (lean_obj_tag(v_t_2408_) == 0)
{
lean_object* v_k_2410_; lean_object* v_v_2411_; lean_object* v_l_2412_; lean_object* v_r_2413_; uint8_t v___x_2414_; 
v_k_2410_ = lean_ctor_get(v_t_2408_, 1);
v_v_2411_ = lean_ctor_get(v_t_2408_, 2);
v_l_2412_ = lean_ctor_get(v_t_2408_, 3);
v_r_2413_ = lean_ctor_get(v_t_2408_, 4);
v___x_2414_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2409_, v_k_2410_);
switch(v___x_2414_)
{
case 0:
{
v_t_2408_ = v_l_2412_;
goto _start;
}
case 1:
{
lean_object* v___x_2416_; 
lean_inc(v_v_2411_);
v___x_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2416_, 0, v_v_2411_);
return v___x_2416_;
}
default: 
{
v_t_2408_ = v_r_2413_;
goto _start;
}
}
}
else
{
lean_object* v___x_2418_; 
v___x_2418_ = lean_box(0);
return v___x_2418_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg___boxed(lean_object* v_t_2419_, lean_object* v_k_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(v_t_2419_, v_k_2420_);
lean_dec(v_k_2420_);
lean_dec(v_t_2419_);
return v_res_2421_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(lean_object* v_k_2422_, lean_object* v_t_2423_){
_start:
{
if (lean_obj_tag(v_t_2423_) == 0)
{
lean_object* v_k_2424_; lean_object* v_l_2425_; lean_object* v_r_2426_; uint8_t v___x_2427_; 
v_k_2424_ = lean_ctor_get(v_t_2423_, 1);
v_l_2425_ = lean_ctor_get(v_t_2423_, 3);
v_r_2426_ = lean_ctor_get(v_t_2423_, 4);
v___x_2427_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2422_, v_k_2424_);
switch(v___x_2427_)
{
case 0:
{
v_t_2423_ = v_l_2425_;
goto _start;
}
case 1:
{
uint8_t v___x_2429_; 
v___x_2429_ = 1;
return v___x_2429_;
}
default: 
{
v_t_2423_ = v_r_2426_;
goto _start;
}
}
}
else
{
uint8_t v___x_2431_; 
v___x_2431_ = 0;
return v___x_2431_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg___boxed(lean_object* v_k_2432_, lean_object* v_t_2433_){
_start:
{
uint8_t v_res_2434_; lean_object* v_r_2435_; 
v_res_2434_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_k_2432_, v_t_2433_);
lean_dec(v_t_2433_);
lean_dec(v_k_2432_);
v_r_2435_ = lean_box(v_res_2434_);
return v_r_2435_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(lean_object* v_a_2436_, uint8_t v___x_2437_, lean_object* v_before_2438_, lean_object* v_after_2439_){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(v_a_2436_, v_before_2438_);
if (lean_obj_tag(v___x_2440_) == 0)
{
return v___x_2437_;
}
else
{
lean_object* v_val_2441_; uint8_t v___x_2442_; 
v_val_2441_ = lean_ctor_get(v___x_2440_, 0);
lean_inc(v_val_2441_);
lean_dec_ref(v___x_2440_);
v___x_2442_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_after_2439_, v_val_2441_);
lean_dec(v_val_2441_);
return v___x_2442_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0___boxed(lean_object* v_a_2443_, lean_object* v___x_2444_, lean_object* v_before_2445_, lean_object* v_after_2446_){
_start:
{
uint8_t v___x_3447__boxed_2447_; uint8_t v_res_2448_; lean_object* v_r_2449_; 
v___x_3447__boxed_2447_ = lean_unbox(v___x_2444_);
v_res_2448_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(v_a_2443_, v___x_3447__boxed_2447_, v_before_2445_, v_after_2446_);
lean_dec(v_after_2446_);
lean_dec(v_before_2445_);
lean_dec(v_a_2443_);
v_r_2449_ = lean_box(v_res_2448_);
return v_r_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4_spec__4___redArg(lean_object* v_lctx_2450_, lean_object* v_localInsts_2451_, lean_object* v_x_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2450_, v_localInsts_2451_, v_x_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2458_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2458_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
v_a_2467_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2458_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2458_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4_spec__4___redArg___boxed(lean_object* v_lctx_2475_, lean_object* v_localInsts_2476_, lean_object* v_x_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4_spec__4___redArg(v_lctx_2475_, v_localInsts_2476_, v_x_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
return v_res_2483_;
}
}
static lean_object* _init_l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2485_ = ((lean_object*)(l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___redArg___closed__0));
v___x_2486_ = l_Lean_stringToMessageData(v___x_2485_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___redArg(lean_object* v_goal_2487_, lean_object* v_action_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v___x_2494_; lean_object* v_mctx_2495_; lean_object* v___x_2496_; 
v___x_2494_ = lean_st_ref_get(v___y_2490_);
v_mctx_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc_ref(v_mctx_2495_);
lean_dec(v___x_2494_);
v___x_2496_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2495_, v_goal_2487_);
if (lean_obj_tag(v___x_2496_) == 1)
{
lean_object* v_val_2497_; lean_object* v_options_2498_; lean_object* v_lctx_2499_; lean_object* v_localInstances_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v_fst_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
lean_dec(v_goal_2487_);
v_val_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_val_2497_);
lean_dec_ref(v___x_2496_);
v_options_2498_ = lean_ctor_get(v___y_2491_, 2);
v_lctx_2499_ = lean_ctor_get(v_val_2497_, 1);
v_localInstances_2500_ = lean_ctor_get(v_val_2497_, 4);
lean_inc_ref(v_localInstances_2500_);
v___x_2501_ = lean_box(1);
lean_inc_ref(v_options_2498_);
v___x_2502_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2502_, 0, v_options_2498_);
lean_ctor_set(v___x_2502_, 1, v___x_2501_);
lean_ctor_set(v___x_2502_, 2, v___x_2501_);
lean_inc_ref(v_lctx_2499_);
v___x_2503_ = l_Lean_LocalContext_sanitizeNames(v_lctx_2499_, v___x_2502_);
v_fst_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_fst_2504_);
lean_dec_ref(v___x_2503_);
lean_inc(v_fst_2504_);
v___x_2505_ = lean_apply_2(v_action_2488_, v_fst_2504_, v_val_2497_);
v___x_2506_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4_spec__4___redArg(v_fst_2504_, v_localInstances_2500_, v___x_2505_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
return v___x_2506_;
}
else
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
lean_dec(v___x_2496_);
lean_dec_ref(v_action_2488_);
v___x_2507_ = lean_obj_once(&l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___redArg___closed__1, &l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___redArg___closed__1_once, _init_l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___redArg___closed__1);
v___x_2508_ = l_Lean_MessageData_ofName(v_goal_2487_);
v___x_2509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2507_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
v___x_2510_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_2509_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
return v___x_2510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___redArg___boxed(lean_object* v_goal_2511_, lean_object* v_action_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___redArg(v_goal_2511_, v_action_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
return v_res_2518_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__2(lean_object* v_mvarId_2519_, lean_object* v_g_u2080_2520_){
_start:
{
uint8_t v___x_2521_; 
v___x_2521_ = l_Lean_instBEqMVarId_beq(v_g_u2080_2520_, v_mvarId_2519_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__2___boxed(lean_object* v_mvarId_2522_, lean_object* v_g_u2080_2523_){
_start:
{
uint8_t v_res_2524_; lean_object* v_r_2525_; 
v_res_2524_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__2(v_mvarId_2522_, v_g_u2080_2523_);
lean_dec(v_g_u2080_2523_);
lean_dec(v_mvarId_2522_);
v_r_2525_ = lean_box(v_res_2524_);
return v_r_2525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__3(lean_object* v___y_2526_, lean_object* v___f_2527_, lean_object* v___f_2528_, uint8_t v_useAfter_2529_, lean_object* v_v_2530_, uint8_t v___y_2531_, uint8_t v___x_2532_, lean_object* v_toInteractiveGoalCore_2533_, lean_object* v_userName_x3f_2534_, lean_object* v_goalPrefix_2535_, lean_object* v_mvarId_2536_, lean_object* v_isInserted_x3f_2537_, lean_object* v_isRemoved_x3f_2538_, lean_object* v___lctx_u2081_2539_, lean_object* v___md_u2081_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
uint8_t v___x_2546_; 
lean_inc(v___y_2526_);
v___x_2546_ = l_List_any___redArg(v___y_2526_, v___f_2527_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2547_; 
v___x_2547_ = l_List_find_x3f___redArg(v___f_2528_, v___y_2526_);
if (lean_obj_tag(v___x_2547_) == 1)
{
lean_object* v_val_2548_; lean_object* v___x_2549_; 
lean_dec(v_isRemoved_x3f_2538_);
lean_dec(v_isInserted_x3f_2537_);
lean_dec(v_mvarId_2536_);
lean_dec_ref(v_goalPrefix_2535_);
lean_dec(v_userName_x3f_2534_);
lean_dec_ref(v_toInteractiveGoalCore_2533_);
v_val_2548_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_val_2548_);
lean_dec_ref(v___x_2547_);
v___x_2549_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(v_useAfter_2529_, v_val_2548_, v_v_2530_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
return v___x_2549_;
}
else
{
lean_dec(v___x_2547_);
lean_dec(v_v_2530_);
if (v___y_2531_ == 0)
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
lean_dec(v_isRemoved_x3f_2538_);
v___x_2550_ = lean_box(v___x_2532_);
v___x_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2550_);
v___x_2552_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2552_, 0, v_toInteractiveGoalCore_2533_);
lean_ctor_set(v___x_2552_, 1, v_userName_x3f_2534_);
lean_ctor_set(v___x_2552_, 2, v_goalPrefix_2535_);
lean_ctor_set(v___x_2552_, 3, v_mvarId_2536_);
lean_ctor_set(v___x_2552_, 4, v_isInserted_x3f_2537_);
lean_ctor_set(v___x_2552_, 5, v___x_2551_);
v___x_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2552_);
return v___x_2553_;
}
else
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
lean_dec(v_isInserted_x3f_2537_);
v___x_2554_ = lean_box(v___x_2532_);
v___x_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
v___x_2556_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2556_, 0, v_toInteractiveGoalCore_2533_);
lean_ctor_set(v___x_2556_, 1, v_userName_x3f_2534_);
lean_ctor_set(v___x_2556_, 2, v_goalPrefix_2535_);
lean_ctor_set(v___x_2556_, 3, v_mvarId_2536_);
lean_ctor_set(v___x_2556_, 4, v___x_2555_);
lean_ctor_set(v___x_2556_, 5, v_isRemoved_x3f_2538_);
v___x_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2556_);
return v___x_2557_;
}
}
}
else
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
lean_dec(v_isInserted_x3f_2537_);
lean_dec(v_v_2530_);
lean_dec_ref(v___f_2528_);
lean_dec(v___y_2526_);
v___x_2558_ = lean_box(0);
v___x_2559_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2559_, 0, v_toInteractiveGoalCore_2533_);
lean_ctor_set(v___x_2559_, 1, v_userName_x3f_2534_);
lean_ctor_set(v___x_2559_, 2, v_goalPrefix_2535_);
lean_ctor_set(v___x_2559_, 3, v_mvarId_2536_);
lean_ctor_set(v___x_2559_, 4, v___x_2558_);
lean_ctor_set(v___x_2559_, 5, v_isRemoved_x3f_2538_);
v___x_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2559_);
return v___x_2560_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__3___boxed(lean_object** _args){
lean_object* v___y_2561_ = _args[0];
lean_object* v___f_2562_ = _args[1];
lean_object* v___f_2563_ = _args[2];
lean_object* v_useAfter_2564_ = _args[3];
lean_object* v_v_2565_ = _args[4];
lean_object* v___y_2566_ = _args[5];
lean_object* v___x_2567_ = _args[6];
lean_object* v_toInteractiveGoalCore_2568_ = _args[7];
lean_object* v_userName_x3f_2569_ = _args[8];
lean_object* v_goalPrefix_2570_ = _args[9];
lean_object* v_mvarId_2571_ = _args[10];
lean_object* v_isInserted_x3f_2572_ = _args[11];
lean_object* v_isRemoved_x3f_2573_ = _args[12];
lean_object* v___lctx_u2081_2574_ = _args[13];
lean_object* v___md_u2081_2575_ = _args[14];
lean_object* v___y_2576_ = _args[15];
lean_object* v___y_2577_ = _args[16];
lean_object* v___y_2578_ = _args[17];
lean_object* v___y_2579_ = _args[18];
lean_object* v___y_2580_ = _args[19];
_start:
{
uint8_t v_useAfter_boxed_2581_; uint8_t v___y_3560__boxed_2582_; uint8_t v___x_3561__boxed_2583_; lean_object* v_res_2584_; 
v_useAfter_boxed_2581_ = lean_unbox(v_useAfter_2564_);
v___y_3560__boxed_2582_ = lean_unbox(v___y_2566_);
v___x_3561__boxed_2583_ = lean_unbox(v___x_2567_);
v_res_2584_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__3(v___y_2561_, v___f_2562_, v___f_2563_, v_useAfter_boxed_2581_, v_v_2565_, v___y_3560__boxed_2582_, v___x_3561__boxed_2583_, v_toInteractiveGoalCore_2568_, v_userName_x3f_2569_, v_goalPrefix_2570_, v_mvarId_2571_, v_isInserted_x3f_2572_, v_isRemoved_x3f_2573_, v___lctx_u2081_2574_, v___md_u2081_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec_ref(v___md_u2081_2575_);
lean_dec_ref(v___lctx_u2081_2574_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5(uint8_t v___y_2585_, lean_object* v_a_2586_, lean_object* v___y_2587_, uint8_t v_useAfter_2588_, uint8_t v___x_2589_, size_t v_sz_2590_, size_t v_i_2591_, lean_object* v_bs_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
uint8_t v___x_2598_; 
v___x_2598_ = lean_usize_dec_lt(v_i_2591_, v_sz_2590_);
if (v___x_2598_ == 0)
{
lean_object* v___x_2599_; 
lean_dec(v___y_2587_);
lean_dec(v_a_2586_);
v___x_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2599_, 0, v_bs_2592_);
return v___x_2599_;
}
else
{
lean_object* v_v_2600_; lean_object* v_toInteractiveGoalCore_2601_; lean_object* v_userName_x3f_2602_; lean_object* v_goalPrefix_2603_; lean_object* v_mvarId_2604_; lean_object* v_isInserted_x3f_2605_; lean_object* v_isRemoved_x3f_2606_; uint8_t v___x_2607_; lean_object* v___x_2608_; lean_object* v___f_2609_; lean_object* v___x_2610_; lean_object* v___f_2611_; lean_object* v___f_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___f_2616_; lean_object* v___x_2617_; 
v_v_2600_ = lean_array_uget_borrowed(v_bs_2592_, v_i_2591_);
v_toInteractiveGoalCore_2601_ = lean_ctor_get(v_v_2600_, 0);
v_userName_x3f_2602_ = lean_ctor_get(v_v_2600_, 1);
v_goalPrefix_2603_ = lean_ctor_get(v_v_2600_, 2);
v_mvarId_2604_ = lean_ctor_get(v_v_2600_, 3);
v_isInserted_x3f_2605_ = lean_ctor_get(v_v_2600_, 4);
v_isRemoved_x3f_2606_ = lean_ctor_get(v_v_2600_, 5);
v___x_2607_ = 0;
v___x_2608_ = lean_box(v___x_2607_);
lean_inc(v_a_2586_);
v___f_2609_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2609_, 0, v_a_2586_);
lean_closure_set(v___f_2609_, 1, v___x_2608_);
v___x_2610_ = lean_box(v___y_2585_);
lean_inc(v_mvarId_2604_);
v___f_2611_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2611_, 0, v___x_2610_);
lean_closure_set(v___f_2611_, 1, v___f_2609_);
lean_closure_set(v___f_2611_, 2, v_mvarId_2604_);
lean_inc(v_mvarId_2604_);
v___f_2612_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__2___boxed), 2, 1);
lean_closure_set(v___f_2612_, 0, v_mvarId_2604_);
v___x_2613_ = lean_box(v_useAfter_2588_);
v___x_2614_ = lean_box(v___y_2585_);
v___x_2615_ = lean_box(v___x_2589_);
lean_inc(v_isRemoved_x3f_2606_);
lean_inc(v_isInserted_x3f_2605_);
lean_inc(v_mvarId_2604_);
lean_inc_ref(v_goalPrefix_2603_);
lean_inc(v_userName_x3f_2602_);
lean_inc_ref(v_toInteractiveGoalCore_2601_);
lean_inc(v_v_2600_);
lean_inc(v___y_2587_);
v___f_2616_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__3___boxed), 20, 13);
lean_closure_set(v___f_2616_, 0, v___y_2587_);
lean_closure_set(v___f_2616_, 1, v___f_2612_);
lean_closure_set(v___f_2616_, 2, v___f_2611_);
lean_closure_set(v___f_2616_, 3, v___x_2613_);
lean_closure_set(v___f_2616_, 4, v_v_2600_);
lean_closure_set(v___f_2616_, 5, v___x_2614_);
lean_closure_set(v___f_2616_, 6, v___x_2615_);
lean_closure_set(v___f_2616_, 7, v_toInteractiveGoalCore_2601_);
lean_closure_set(v___f_2616_, 8, v_userName_x3f_2602_);
lean_closure_set(v___f_2616_, 9, v_goalPrefix_2603_);
lean_closure_set(v___f_2616_, 10, v_mvarId_2604_);
lean_closure_set(v___f_2616_, 11, v_isInserted_x3f_2605_);
lean_closure_set(v___f_2616_, 12, v_isRemoved_x3f_2606_);
lean_inc(v_mvarId_2604_);
v___x_2617_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___redArg(v_mvarId_2604_, v___f_2616_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; lean_object* v___x_2619_; lean_object* v_bs_x27_2620_; size_t v___x_2621_; size_t v___x_2622_; lean_object* v___x_2623_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_a_2618_);
lean_dec_ref(v___x_2617_);
v___x_2619_ = lean_unsigned_to_nat(0u);
v_bs_x27_2620_ = lean_array_uset(v_bs_2592_, v_i_2591_, v___x_2619_);
v___x_2621_ = ((size_t)1ULL);
v___x_2622_ = lean_usize_add(v_i_2591_, v___x_2621_);
v___x_2623_ = lean_array_uset(v_bs_x27_2620_, v_i_2591_, v_a_2618_);
v_i_2591_ = v___x_2622_;
v_bs_2592_ = v___x_2623_;
goto _start;
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec_ref(v_bs_2592_);
lean_dec(v___y_2587_);
lean_dec(v_a_2586_);
v_a_2625_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2617_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2617_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___boxed(lean_object* v___y_2633_, lean_object* v_a_2634_, lean_object* v___y_2635_, lean_object* v_useAfter_2636_, lean_object* v___x_2637_, lean_object* v_sz_2638_, lean_object* v_i_2639_, lean_object* v_bs_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
uint8_t v___y_3617__boxed_2646_; uint8_t v_useAfter_boxed_2647_; uint8_t v___x_3620__boxed_2648_; size_t v_sz_boxed_2649_; size_t v_i_boxed_2650_; lean_object* v_res_2651_; 
v___y_3617__boxed_2646_ = lean_unbox(v___y_2633_);
v_useAfter_boxed_2647_ = lean_unbox(v_useAfter_2636_);
v___x_3620__boxed_2648_ = lean_unbox(v___x_2637_);
v_sz_boxed_2649_ = lean_unbox_usize(v_sz_2638_);
lean_dec(v_sz_2638_);
v_i_boxed_2650_ = lean_unbox_usize(v_i_2639_);
lean_dec(v_i_2639_);
v_res_2651_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5(v___y_3617__boxed_2646_, v_a_2634_, v___y_2635_, v_useAfter_boxed_2647_, v___x_3620__boxed_2648_, v_sz_boxed_2649_, v_i_boxed_2650_, v_bs_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
return v_res_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_diffInteractiveGoals(uint8_t v_useAfter_2652_, lean_object* v_info_2653_, lean_object* v_igs_u2081_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
lean_object* v_options_2660_; lean_object* v___x_2661_; uint8_t v___x_2662_; lean_object* v___y_2664_; 
v_options_2660_ = lean_ctor_get(v_a_2657_, 2);
v___x_2661_ = l___private_Lean_Widget_Diff_0__Lean_Widget_showTacticDiff;
v___x_2662_ = l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(v_options_2660_, v___x_2661_);
if (v___x_2662_ == 0)
{
lean_object* v___x_2696_; 
lean_dec_ref(v_info_2653_);
v___x_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2696_, 0, v_igs_u2081_2654_);
return v___x_2696_;
}
else
{
if (v_useAfter_2652_ == 0)
{
lean_object* v_goalsAfter_2697_; 
v_goalsAfter_2697_ = lean_ctor_get(v_info_2653_, 4);
lean_inc(v_goalsAfter_2697_);
v___y_2664_ = v_goalsAfter_2697_;
goto v___jp_2663_;
}
else
{
lean_object* v_goalsBefore_2698_; 
v_goalsBefore_2698_ = lean_ctor_get(v_info_2653_, 2);
lean_inc(v_goalsBefore_2698_);
v___y_2664_ = v_goalsBefore_2698_;
goto v___jp_2663_;
}
}
v___jp_2663_:
{
lean_object* v_goalsBefore_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v_goalsBefore_2665_ = lean_ctor_get(v_info_2653_, 2);
lean_inc(v_goalsBefore_2665_);
lean_dec_ref(v_info_2653_);
v___x_2666_ = lean_box(1);
v___x_2667_ = l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(v___x_2666_, v_goalsBefore_2665_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; size_t v_sz_2669_; size_t v___x_2670_; lean_object* v___x_2671_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
lean_inc(v_a_2668_);
lean_dec_ref(v___x_2667_);
v_sz_2669_ = lean_array_size(v_igs_u2081_2654_);
v___x_2670_ = ((size_t)0ULL);
v___x_2671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5(v_useAfter_2652_, v_a_2668_, v___y_2664_, v_useAfter_2652_, v___x_2662_, v_sz_2669_, v___x_2670_, v_igs_u2081_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2679_; 
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2674_ = v___x_2671_;
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2671_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2677_; 
if (v_isShared_2675_ == 0)
{
v___x_2677_ = v___x_2674_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2672_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
else
{
lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2687_; 
v_a_2680_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2682_ = v___x_2671_;
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2671_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2683_ == 0)
{
v___x_2685_ = v___x_2682_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2680_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
lean_dec(v___y_2664_);
lean_dec_ref(v_igs_u2081_2654_);
v_a_2688_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2667_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2667_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_diffInteractiveGoals___boxed(lean_object* v_useAfter_2699_, lean_object* v_info_2700_, lean_object* v_igs_u2081_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_){
_start:
{
uint8_t v_useAfter_boxed_2707_; lean_object* v_res_2708_; 
v_useAfter_boxed_2707_ = lean_unbox(v_useAfter_2699_);
v_res_2708_ = l_Lean_Widget_diffInteractiveGoals(v_useAfter_boxed_2707_, v_info_2700_, v_igs_u2081_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_);
lean_dec(v_a_2705_);
lean_dec_ref(v_a_2704_);
lean_dec(v_a_2703_);
lean_dec_ref(v_a_2702_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2(lean_object* v_00_u03b4_2709_, lean_object* v_t_2710_, lean_object* v_k_2711_){
_start:
{
lean_object* v___x_2712_; 
v___x_2712_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(v_t_2710_, v_k_2711_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___boxed(lean_object* v_00_u03b4_2713_, lean_object* v_t_2714_, lean_object* v_k_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2(v_00_u03b4_2713_, v_t_2714_, v_k_2715_);
lean_dec(v_k_2715_);
lean_dec(v_t_2714_);
return v_res_2716_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3(lean_object* v_00_u03b2_2717_, lean_object* v_k_2718_, lean_object* v_t_2719_){
_start:
{
uint8_t v___x_2720_; 
v___x_2720_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_k_2718_, v_t_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___boxed(lean_object* v_00_u03b2_2721_, lean_object* v_k_2722_, lean_object* v_t_2723_){
_start:
{
uint8_t v_res_2724_; lean_object* v_r_2725_; 
v_res_2724_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3(v_00_u03b2_2721_, v_k_2722_, v_t_2723_);
lean_dec(v_t_2723_);
lean_dec(v_k_2722_);
v_r_2725_ = lean_box(v_res_2724_);
return v_r_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4_spec__4(lean_object* v_00_u03b1_2726_, lean_object* v_lctx_2727_, lean_object* v_localInsts_2728_, lean_object* v_x_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v___x_2735_; 
v___x_2735_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4_spec__4___redArg(v_lctx_2727_, v_localInsts_2728_, v_x_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4_spec__4___boxed(lean_object* v_00_u03b1_2736_, lean_object* v_lctx_2737_, lean_object* v_localInsts_2738_, lean_object* v_x_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4_spec__4(v_00_u03b1_2736_, v_lctx_2737_, v_localInsts_2738_, v_x_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4(lean_object* v_00_u03b1_2746_, lean_object* v_goal_2747_, lean_object* v_action_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___redArg(v_goal_2747_, v_action_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___boxed(lean_object* v_00_u03b1_2755_, lean_object* v_goal_2756_, lean_object* v_action_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4(v_00_u03b1_2755_, v_goal_2756_, v_action_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
return v_res_2763_;
}
}
lean_object* runtime_initialize_Lean_Widget_InteractiveGoal(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Widget_Diff(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Widget_InteractiveGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Widget_Diff_0__Lean_Widget_showTacticDiff = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Widget_Diff_0__Lean_Widget_showTacticDiff);
lean_dec_ref(res);
l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff = _init_l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff();
lean_mark_persistent(l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Widget_Diff(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Widget_InteractiveGoal(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Widget_Diff(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Widget_InteractiveGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Widget_Diff(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Widget_Diff(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Widget_Diff(builtin);
}
#ifdef __cplusplus
}
#endif
