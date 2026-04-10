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
static const lean_ctor_object l_Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_closure_object l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__5, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__1_value),((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__1_value)} };
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__2 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__2_value;
LEAN_EXPORT const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__2_value;
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
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_50_ = ((lean_object*)(l_Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_));
v___x_51_ = ((lean_object*)(l_Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_));
v___x_52_ = ((lean_object*)(l_Lean_Widget_initFn___closed__6_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_));
v___x_53_ = l_Lean_Option_register___at___00Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__spec__0(v___x_50_, v___x_51_, v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4____boxed(lean_object* v_a_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_();
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx(uint8_t v_x_56_){
_start:
{
switch(v_x_56_)
{
case 0:
{
lean_object* v___x_57_; 
v___x_57_ = lean_unsigned_to_nat(0u);
return v___x_57_;
}
case 1:
{
lean_object* v___x_58_; 
v___x_58_ = lean_unsigned_to_nat(1u);
return v___x_58_;
}
default: 
{
lean_object* v___x_59_; 
v___x_59_ = lean_unsigned_to_nat(2u);
return v___x_59_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx___boxed(lean_object* v_x_60_){
_start:
{
uint8_t v_x_boxed_61_; lean_object* v_res_62_; 
v_x_boxed_61_ = lean_unbox(v_x_60_);
v_res_62_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx(v_x_boxed_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toCtorIdx(uint8_t v_x_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx(v_x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toCtorIdx___boxed(lean_object* v_x_65_){
_start:
{
uint8_t v_x_4__boxed_66_; lean_object* v_res_67_; 
v_x_4__boxed_66_ = lean_unbox(v_x_65_);
v_res_67_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toCtorIdx(v_x_4__boxed_66_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___redArg(lean_object* v_k_68_){
_start:
{
lean_inc(v_k_68_);
return v_k_68_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___redArg___boxed(lean_object* v_k_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___redArg(v_k_69_);
lean_dec(v_k_69_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim(lean_object* v_motive_71_, lean_object* v_ctorIdx_72_, uint8_t v_t_73_, lean_object* v_h_74_, lean_object* v_k_75_){
_start:
{
lean_inc(v_k_75_);
return v_k_75_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___boxed(lean_object* v_motive_76_, lean_object* v_ctorIdx_77_, lean_object* v_t_78_, lean_object* v_h_79_, lean_object* v_k_80_){
_start:
{
uint8_t v_t_boxed_81_; lean_object* v_res_82_; 
v_t_boxed_81_ = lean_unbox(v_t_78_);
v_res_82_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim(v_motive_76_, v_ctorIdx_77_, v_t_boxed_81_, v_h_79_, v_k_80_);
lean_dec(v_k_80_);
lean_dec(v_ctorIdx_77_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___redArg(lean_object* v_change_83_){
_start:
{
lean_inc(v_change_83_);
return v_change_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___redArg___boxed(lean_object* v_change_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___redArg(v_change_84_);
lean_dec(v_change_84_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim(lean_object* v_motive_86_, uint8_t v_t_87_, lean_object* v_h_88_, lean_object* v_change_89_){
_start:
{
lean_inc(v_change_89_);
return v_change_89_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___boxed(lean_object* v_motive_90_, lean_object* v_t_91_, lean_object* v_h_92_, lean_object* v_change_93_){
_start:
{
uint8_t v_t_boxed_94_; lean_object* v_res_95_; 
v_t_boxed_94_ = lean_unbox(v_t_91_);
v_res_95_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim(v_motive_90_, v_t_boxed_94_, v_h_92_, v_change_93_);
lean_dec(v_change_93_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___redArg(lean_object* v_delete_96_){
_start:
{
lean_inc(v_delete_96_);
return v_delete_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___redArg___boxed(lean_object* v_delete_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___redArg(v_delete_97_);
lean_dec(v_delete_97_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim(lean_object* v_motive_99_, uint8_t v_t_100_, lean_object* v_h_101_, lean_object* v_delete_102_){
_start:
{
lean_inc(v_delete_102_);
return v_delete_102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___boxed(lean_object* v_motive_103_, lean_object* v_t_104_, lean_object* v_h_105_, lean_object* v_delete_106_){
_start:
{
uint8_t v_t_boxed_107_; lean_object* v_res_108_; 
v_t_boxed_107_ = lean_unbox(v_t_104_);
v_res_108_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim(v_motive_103_, v_t_boxed_107_, v_h_105_, v_delete_106_);
lean_dec(v_delete_106_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___redArg(lean_object* v_insert_109_){
_start:
{
lean_inc(v_insert_109_);
return v_insert_109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___redArg___boxed(lean_object* v_insert_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___redArg(v_insert_110_);
lean_dec(v_insert_110_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim(lean_object* v_motive_112_, uint8_t v_t_113_, lean_object* v_h_114_, lean_object* v_insert_115_){
_start:
{
lean_inc(v_insert_115_);
return v_insert_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___boxed(lean_object* v_motive_116_, lean_object* v_t_117_, lean_object* v_h_118_, lean_object* v_insert_119_){
_start:
{
uint8_t v_t_boxed_120_; lean_object* v_res_121_; 
v_t_boxed_120_ = lean_unbox(v_t_117_);
v_res_121_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim(v_motive_116_, v_t_boxed_120_, v_h_118_, v_insert_119_);
lean_dec(v_insert_119_);
return v_res_121_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag(uint8_t v_x_122_, uint8_t v_x_123_){
_start:
{
if (v_x_122_ == 0)
{
switch(v_x_123_)
{
case 0:
{
uint8_t v___x_124_; 
v___x_124_ = 1;
return v___x_124_;
}
case 1:
{
uint8_t v___x_125_; 
v___x_125_ = 3;
return v___x_125_;
}
default: 
{
uint8_t v___x_126_; 
v___x_126_ = 5;
return v___x_126_;
}
}
}
else
{
switch(v_x_123_)
{
case 0:
{
uint8_t v___x_127_; 
v___x_127_ = 0;
return v___x_127_;
}
case 1:
{
uint8_t v___x_128_; 
v___x_128_ = 2;
return v___x_128_;
}
default: 
{
uint8_t v___x_129_; 
v___x_129_ = 4;
return v___x_129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag___boxed(lean_object* v_x_130_, lean_object* v_x_131_){
_start:
{
uint8_t v_x_49__boxed_132_; uint8_t v_x_50__boxed_133_; uint8_t v_res_134_; lean_object* v_r_135_; 
v_x_49__boxed_132_ = lean_unbox(v_x_130_);
v_x_50__boxed_133_ = lean_unbox(v_x_131_);
v_res_134_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag(v_x_49__boxed_132_, v_x_50__boxed_133_);
v_r_135_ = lean_box(v_res_134_);
return v_r_135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString(uint8_t v_x_139_){
_start:
{
switch(v_x_139_)
{
case 0:
{
lean_object* v___x_140_; 
v___x_140_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__0));
return v___x_140_;
}
case 1:
{
lean_object* v___x_141_; 
v___x_141_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__1));
return v___x_141_;
}
default: 
{
lean_object* v___x_142_; 
v___x_142_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__2));
return v___x_142_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___boxed(lean_object* v_x_143_){
_start:
{
uint8_t v_x_31__boxed_144_; lean_object* v_res_145_; 
v_x_31__boxed_144_ = lean_unbox(v_x_143_);
v_res_145_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString(v_x_31__boxed_144_);
return v_res_145_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0(lean_object* v_x_151_, lean_object* v_y_152_){
_start:
{
uint8_t v___x_153_; 
v___x_153_ = lean_nat_dec_lt(v_x_151_, v_y_152_);
if (v___x_153_ == 0)
{
uint8_t v___x_154_; 
v___x_154_ = lean_nat_dec_eq(v_x_151_, v_y_152_);
if (v___x_154_ == 0)
{
uint8_t v___x_155_; 
v___x_155_ = 2;
return v___x_155_;
}
else
{
uint8_t v___x_156_; 
v___x_156_ = 1;
return v___x_156_;
}
}
else
{
uint8_t v___x_157_; 
v___x_157_ = 0;
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0___boxed(lean_object* v_x_158_, lean_object* v_y_159_){
_start:
{
uint8_t v_res_160_; lean_object* v_r_161_; 
v_res_160_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0(v_x_158_, v_y_159_);
lean_dec(v_y_159_);
lean_dec(v_x_158_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1(uint8_t v_b_u2082_162_, lean_object* v_x_163_){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_box(v_b_u2082_162_);
v___x_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1___boxed(lean_object* v_b_u2082_166_, lean_object* v_x_167_){
_start:
{
uint8_t v_b_u2082_boxed_168_; lean_object* v_res_169_; 
v_b_u2082_boxed_168_ = lean_unbox(v_b_u2082_166_);
v_res_169_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1(v_b_u2082_boxed_168_, v_x_167_);
lean_dec(v_x_167_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2(lean_object* v___f_170_, lean_object* v_t_171_, lean_object* v_a_172_, uint8_t v_b_u2082_173_){
_start:
{
lean_object* v___x_174_; lean_object* v___f_175_; lean_object* v___x_176_; 
v___x_174_ = lean_box(v_b_u2082_173_);
v___f_175_ = lean_alloc_closure((void*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1___boxed), 2, 1);
lean_closure_set(v___f_175_, 0, v___x_174_);
v___x_176_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v___f_170_, v_a_172_, v___f_175_, v_t_171_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2___boxed(lean_object* v___f_177_, lean_object* v_t_178_, lean_object* v_a_179_, lean_object* v_b_u2082_180_){
_start:
{
uint8_t v_b_u2082_boxed_181_; lean_object* v_res_182_; 
v_b_u2082_boxed_181_ = lean_unbox(v_b_u2082_180_);
v_res_182_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2(v___f_177_, v_t_178_, v_a_179_, v_b_u2082_boxed_181_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__5(lean_object* v___f_183_, lean_object* v___f_184_, lean_object* v_a_185_, lean_object* v_b_186_){
_start:
{
lean_object* v_changesBefore_187_; lean_object* v_changesAfter_188_; lean_object* v_changesBefore_189_; lean_object* v_changesAfter_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_199_; 
v_changesBefore_187_ = lean_ctor_get(v_a_185_, 0);
lean_inc(v_changesBefore_187_);
v_changesAfter_188_ = lean_ctor_get(v_a_185_, 1);
lean_inc(v_changesAfter_188_);
lean_dec_ref(v_a_185_);
v_changesBefore_189_ = lean_ctor_get(v_b_186_, 0);
v_changesAfter_190_ = lean_ctor_get(v_b_186_, 1);
v_isSharedCheck_199_ = !lean_is_exclusive(v_b_186_);
if (v_isSharedCheck_199_ == 0)
{
v___x_192_ = v_b_186_;
v_isShared_193_ = v_isSharedCheck_199_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_changesAfter_190_);
lean_inc(v_changesBefore_189_);
lean_dec(v_b_186_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_199_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_194_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_183_, v_changesBefore_187_, v_changesBefore_189_);
v___x_195_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_184_, v_changesAfter_188_, v_changesAfter_190_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 1, v___x_195_);
lean_ctor_set(v___x_192_, 0, v___x_194_);
v___x_197_ = v___x_192_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0(lean_object* v_x_209_){
_start:
{
lean_object* v_fst_210_; lean_object* v_snd_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_fst_210_ = lean_ctor_get(v_x_209_, 0);
v_snd_211_ = lean_ctor_get(v_x_209_, 1);
v___x_212_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__0));
v___x_213_ = l_Lean_SubExpr_Pos_toString(v_fst_210_);
v___x_214_ = lean_string_append(v___x_212_, v___x_213_);
lean_dec_ref(v___x_213_);
v___x_215_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__1));
v___x_216_ = lean_string_append(v___x_214_, v___x_215_);
v___x_217_ = lean_unbox(v_snd_211_);
v___x_218_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString(v___x_217_);
v___x_219_ = lean_string_append(v___x_216_, v___x_218_);
lean_dec_ref(v___x_218_);
v___x_220_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__2));
v___x_221_ = lean_string_append(v___x_219_, v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___boxed(lean_object* v_x_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0(v_x_222_);
lean_dec_ref(v_x_222_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1(lean_object* v_x1_224_, uint8_t v_x2_225_, lean_object* v_x3_226_){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_227_ = lean_box(v_x2_225_);
v___x_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_228_, 0, v_x1_224_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v_x3_226_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1___boxed(lean_object* v_x1_230_, lean_object* v_x2_231_, lean_object* v_x3_232_){
_start:
{
uint8_t v_x2_243__boxed_233_; lean_object* v_res_234_; 
v_x2_243__boxed_233_ = lean_unbox(v_x2_231_);
v_res_234_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1(v_x1_230_, v_x2_243__boxed_233_, v_x3_232_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2(lean_object* v___f_254_, lean_object* v___f_255_, lean_object* v_p_256_){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_257_ = lean_box(0);
v___x_258_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__9));
v___x_259_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_258_, v___f_254_, v___x_257_, v_p_256_);
v___x_260_ = l_List_mapTR_loop___redArg(v___f_255_, v___x_259_, v___x_257_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3(lean_object* v_f_263_, lean_object* v___f_264_, lean_object* v_x_265_){
_start:
{
lean_object* v_changesBefore_266_; lean_object* v_changesAfter_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_changesBefore_266_ = lean_ctor_get(v_x_265_, 0);
lean_inc(v_changesBefore_266_);
v_changesAfter_267_ = lean_ctor_get(v_x_265_, 1);
lean_inc(v_changesAfter_267_);
lean_dec_ref(v_x_265_);
v___x_268_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__0));
lean_inc_ref(v_f_263_);
v___x_269_ = lean_apply_1(v_f_263_, v_changesBefore_266_);
lean_inc_ref(v___f_264_);
v___x_270_ = l_List_toString___redArg(v___f_264_, v___x_269_);
v___x_271_ = lean_string_append(v___x_268_, v___x_270_);
lean_dec_ref(v___x_270_);
v___x_272_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__1));
v___x_273_ = lean_string_append(v___x_271_, v___x_272_);
v___x_274_ = lean_apply_1(v_f_263_, v_changesAfter_267_);
v___x_275_ = l_List_toString___redArg(v___f_264_, v___x_274_);
v___x_276_ = lean_string_append(v___x_273_, v___x_275_);
lean_dec_ref(v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(lean_object* v_k_287_, lean_object* v_v_288_, lean_object* v_t_289_){
_start:
{
if (lean_obj_tag(v_t_289_) == 0)
{
lean_object* v_size_290_; lean_object* v_k_291_; lean_object* v_v_292_; lean_object* v_l_293_; lean_object* v_r_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_575_; 
v_size_290_ = lean_ctor_get(v_t_289_, 0);
v_k_291_ = lean_ctor_get(v_t_289_, 1);
v_v_292_ = lean_ctor_get(v_t_289_, 2);
v_l_293_ = lean_ctor_get(v_t_289_, 3);
v_r_294_ = lean_ctor_get(v_t_289_, 4);
v_isSharedCheck_575_ = !lean_is_exclusive(v_t_289_);
if (v_isSharedCheck_575_ == 0)
{
v___x_296_ = v_t_289_;
v_isShared_297_ = v_isSharedCheck_575_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_r_294_);
lean_inc(v_l_293_);
lean_inc(v_v_292_);
lean_inc(v_k_291_);
lean_inc(v_size_290_);
lean_dec(v_t_289_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_575_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
uint8_t v___x_298_; 
v___x_298_ = lean_nat_dec_lt(v_k_287_, v_k_291_);
if (v___x_298_ == 0)
{
uint8_t v___x_299_; 
v___x_299_ = lean_nat_dec_eq(v_k_287_, v_k_291_);
if (v___x_299_ == 0)
{
lean_object* v_impl_300_; lean_object* v___x_301_; 
lean_dec(v_size_290_);
v_impl_300_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_k_287_, v_v_288_, v_r_294_);
v___x_301_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_293_) == 0)
{
lean_object* v_size_302_; lean_object* v_size_303_; lean_object* v_k_304_; lean_object* v_v_305_; lean_object* v_l_306_; lean_object* v_r_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v_size_302_ = lean_ctor_get(v_l_293_, 0);
v_size_303_ = lean_ctor_get(v_impl_300_, 0);
lean_inc(v_size_303_);
v_k_304_ = lean_ctor_get(v_impl_300_, 1);
lean_inc(v_k_304_);
v_v_305_ = lean_ctor_get(v_impl_300_, 2);
lean_inc(v_v_305_);
v_l_306_ = lean_ctor_get(v_impl_300_, 3);
lean_inc(v_l_306_);
v_r_307_ = lean_ctor_get(v_impl_300_, 4);
lean_inc(v_r_307_);
v___x_308_ = lean_unsigned_to_nat(3u);
v___x_309_ = lean_nat_mul(v___x_308_, v_size_302_);
v___x_310_ = lean_nat_dec_lt(v___x_309_, v_size_303_);
lean_dec(v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_314_; 
lean_dec(v_r_307_);
lean_dec(v_l_306_);
lean_dec(v_v_305_);
lean_dec(v_k_304_);
v___x_311_ = lean_nat_add(v___x_301_, v_size_302_);
v___x_312_ = lean_nat_add(v___x_311_, v_size_303_);
lean_dec(v_size_303_);
lean_dec(v___x_311_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 4, v_impl_300_);
lean_ctor_set(v___x_296_, 0, v___x_312_);
v___x_314_ = v___x_296_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_312_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_k_291_);
lean_ctor_set(v_reuseFailAlloc_315_, 2, v_v_292_);
lean_ctor_set(v_reuseFailAlloc_315_, 3, v_l_293_);
lean_ctor_set(v_reuseFailAlloc_315_, 4, v_impl_300_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
else
{
lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_379_; 
v_isSharedCheck_379_ = !lean_is_exclusive(v_impl_300_);
if (v_isSharedCheck_379_ == 0)
{
lean_object* v_unused_380_; lean_object* v_unused_381_; lean_object* v_unused_382_; lean_object* v_unused_383_; lean_object* v_unused_384_; 
v_unused_380_ = lean_ctor_get(v_impl_300_, 4);
lean_dec(v_unused_380_);
v_unused_381_ = lean_ctor_get(v_impl_300_, 3);
lean_dec(v_unused_381_);
v_unused_382_ = lean_ctor_get(v_impl_300_, 2);
lean_dec(v_unused_382_);
v_unused_383_ = lean_ctor_get(v_impl_300_, 1);
lean_dec(v_unused_383_);
v_unused_384_ = lean_ctor_get(v_impl_300_, 0);
lean_dec(v_unused_384_);
v___x_317_ = v_impl_300_;
v_isShared_318_ = v_isSharedCheck_379_;
goto v_resetjp_316_;
}
else
{
lean_dec(v_impl_300_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_379_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v_size_319_; lean_object* v_k_320_; lean_object* v_v_321_; lean_object* v_l_322_; lean_object* v_r_323_; lean_object* v_size_324_; lean_object* v___x_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v_size_319_ = lean_ctor_get(v_l_306_, 0);
v_k_320_ = lean_ctor_get(v_l_306_, 1);
v_v_321_ = lean_ctor_get(v_l_306_, 2);
v_l_322_ = lean_ctor_get(v_l_306_, 3);
v_r_323_ = lean_ctor_get(v_l_306_, 4);
v_size_324_ = lean_ctor_get(v_r_307_, 0);
v___x_325_ = lean_unsigned_to_nat(2u);
v___x_326_ = lean_nat_mul(v___x_325_, v_size_324_);
v___x_327_ = lean_nat_dec_lt(v_size_319_, v___x_326_);
lean_dec(v___x_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_355_; 
lean_inc(v_r_323_);
lean_inc(v_l_322_);
lean_inc(v_v_321_);
lean_inc(v_k_320_);
v_isSharedCheck_355_ = !lean_is_exclusive(v_l_306_);
if (v_isSharedCheck_355_ == 0)
{
lean_object* v_unused_356_; lean_object* v_unused_357_; lean_object* v_unused_358_; lean_object* v_unused_359_; lean_object* v_unused_360_; 
v_unused_356_ = lean_ctor_get(v_l_306_, 4);
lean_dec(v_unused_356_);
v_unused_357_ = lean_ctor_get(v_l_306_, 3);
lean_dec(v_unused_357_);
v_unused_358_ = lean_ctor_get(v_l_306_, 2);
lean_dec(v_unused_358_);
v_unused_359_ = lean_ctor_get(v_l_306_, 1);
lean_dec(v_unused_359_);
v_unused_360_ = lean_ctor_get(v_l_306_, 0);
lean_dec(v_unused_360_);
v___x_329_ = v_l_306_;
v_isShared_330_ = v_isSharedCheck_355_;
goto v_resetjp_328_;
}
else
{
lean_dec(v_l_306_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_355_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___y_345_; 
v___x_331_ = lean_nat_add(v___x_301_, v_size_302_);
v___x_332_ = lean_nat_add(v___x_331_, v_size_303_);
lean_dec(v_size_303_);
if (lean_obj_tag(v_l_322_) == 0)
{
lean_object* v_size_353_; 
v_size_353_ = lean_ctor_get(v_l_322_, 0);
lean_inc(v_size_353_);
v___y_345_ = v_size_353_;
goto v___jp_344_;
}
else
{
lean_object* v___x_354_; 
v___x_354_ = lean_unsigned_to_nat(0u);
v___y_345_ = v___x_354_;
goto v___jp_344_;
}
v___jp_333_:
{
lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_337_ = lean_nat_add(v___y_334_, v___y_336_);
lean_dec(v___y_336_);
lean_dec(v___y_334_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 4, v_r_307_);
lean_ctor_set(v___x_329_, 3, v_r_323_);
lean_ctor_set(v___x_329_, 2, v_v_305_);
lean_ctor_set(v___x_329_, 1, v_k_304_);
lean_ctor_set(v___x_329_, 0, v___x_337_);
v___x_339_ = v___x_329_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_337_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_k_304_);
lean_ctor_set(v_reuseFailAlloc_343_, 2, v_v_305_);
lean_ctor_set(v_reuseFailAlloc_343_, 3, v_r_323_);
lean_ctor_set(v_reuseFailAlloc_343_, 4, v_r_307_);
v___x_339_ = v_reuseFailAlloc_343_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
lean_object* v___x_341_; 
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 4, v___x_339_);
lean_ctor_set(v___x_317_, 3, v___y_335_);
lean_ctor_set(v___x_317_, 2, v_v_321_);
lean_ctor_set(v___x_317_, 1, v_k_320_);
lean_ctor_set(v___x_317_, 0, v___x_332_);
v___x_341_ = v___x_317_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_k_320_);
lean_ctor_set(v_reuseFailAlloc_342_, 2, v_v_321_);
lean_ctor_set(v_reuseFailAlloc_342_, 3, v___y_335_);
lean_ctor_set(v_reuseFailAlloc_342_, 4, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
v___jp_344_:
{
lean_object* v___x_346_; lean_object* v___x_348_; 
v___x_346_ = lean_nat_add(v___x_331_, v___y_345_);
lean_dec(v___y_345_);
lean_dec(v___x_331_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 4, v_l_322_);
lean_ctor_set(v___x_296_, 0, v___x_346_);
v___x_348_ = v___x_296_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_346_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_k_291_);
lean_ctor_set(v_reuseFailAlloc_352_, 2, v_v_292_);
lean_ctor_set(v_reuseFailAlloc_352_, 3, v_l_293_);
lean_ctor_set(v_reuseFailAlloc_352_, 4, v_l_322_);
v___x_348_ = v_reuseFailAlloc_352_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
lean_object* v___x_349_; 
v___x_349_ = lean_nat_add(v___x_301_, v_size_324_);
if (lean_obj_tag(v_r_323_) == 0)
{
lean_object* v_size_350_; 
v_size_350_ = lean_ctor_get(v_r_323_, 0);
lean_inc(v_size_350_);
v___y_334_ = v___x_349_;
v___y_335_ = v___x_348_;
v___y_336_ = v_size_350_;
goto v___jp_333_;
}
else
{
lean_object* v___x_351_; 
v___x_351_ = lean_unsigned_to_nat(0u);
v___y_334_ = v___x_349_;
v___y_335_ = v___x_348_;
v___y_336_ = v___x_351_;
goto v___jp_333_;
}
}
}
}
}
else
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_365_; 
lean_del_object(v___x_296_);
v___x_361_ = lean_nat_add(v___x_301_, v_size_302_);
v___x_362_ = lean_nat_add(v___x_361_, v_size_303_);
lean_dec(v_size_303_);
v___x_363_ = lean_nat_add(v___x_361_, v_size_319_);
lean_dec(v___x_361_);
lean_inc_ref(v_l_293_);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 4, v_l_306_);
lean_ctor_set(v___x_317_, 3, v_l_293_);
lean_ctor_set(v___x_317_, 2, v_v_292_);
lean_ctor_set(v___x_317_, 1, v_k_291_);
lean_ctor_set(v___x_317_, 0, v___x_363_);
v___x_365_ = v___x_317_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_k_291_);
lean_ctor_set(v_reuseFailAlloc_378_, 2, v_v_292_);
lean_ctor_set(v_reuseFailAlloc_378_, 3, v_l_293_);
lean_ctor_set(v_reuseFailAlloc_378_, 4, v_l_306_);
v___x_365_ = v_reuseFailAlloc_378_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_372_; 
v_isSharedCheck_372_ = !lean_is_exclusive(v_l_293_);
if (v_isSharedCheck_372_ == 0)
{
lean_object* v_unused_373_; lean_object* v_unused_374_; lean_object* v_unused_375_; lean_object* v_unused_376_; lean_object* v_unused_377_; 
v_unused_373_ = lean_ctor_get(v_l_293_, 4);
lean_dec(v_unused_373_);
v_unused_374_ = lean_ctor_get(v_l_293_, 3);
lean_dec(v_unused_374_);
v_unused_375_ = lean_ctor_get(v_l_293_, 2);
lean_dec(v_unused_375_);
v_unused_376_ = lean_ctor_get(v_l_293_, 1);
lean_dec(v_unused_376_);
v_unused_377_ = lean_ctor_get(v_l_293_, 0);
lean_dec(v_unused_377_);
v___x_367_ = v_l_293_;
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
else
{
lean_dec(v_l_293_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 4, v_r_307_);
lean_ctor_set(v___x_367_, 3, v___x_365_);
lean_ctor_set(v___x_367_, 2, v_v_305_);
lean_ctor_set(v___x_367_, 1, v_k_304_);
lean_ctor_set(v___x_367_, 0, v___x_362_);
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_362_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_k_304_);
lean_ctor_set(v_reuseFailAlloc_371_, 2, v_v_305_);
lean_ctor_set(v_reuseFailAlloc_371_, 3, v___x_365_);
lean_ctor_set(v_reuseFailAlloc_371_, 4, v_r_307_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_385_; 
v_l_385_ = lean_ctor_get(v_impl_300_, 3);
lean_inc(v_l_385_);
if (lean_obj_tag(v_l_385_) == 0)
{
lean_object* v_r_386_; lean_object* v_k_387_; lean_object* v_v_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_411_; 
v_r_386_ = lean_ctor_get(v_impl_300_, 4);
v_k_387_ = lean_ctor_get(v_impl_300_, 1);
v_v_388_ = lean_ctor_get(v_impl_300_, 2);
v_isSharedCheck_411_ = !lean_is_exclusive(v_impl_300_);
if (v_isSharedCheck_411_ == 0)
{
lean_object* v_unused_412_; lean_object* v_unused_413_; 
v_unused_412_ = lean_ctor_get(v_impl_300_, 3);
lean_dec(v_unused_412_);
v_unused_413_ = lean_ctor_get(v_impl_300_, 0);
lean_dec(v_unused_413_);
v___x_390_ = v_impl_300_;
v_isShared_391_ = v_isSharedCheck_411_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_r_386_);
lean_inc(v_v_388_);
lean_inc(v_k_387_);
lean_dec(v_impl_300_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_411_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v_k_392_; lean_object* v_v_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_407_; 
v_k_392_ = lean_ctor_get(v_l_385_, 1);
v_v_393_ = lean_ctor_get(v_l_385_, 2);
v_isSharedCheck_407_ = !lean_is_exclusive(v_l_385_);
if (v_isSharedCheck_407_ == 0)
{
lean_object* v_unused_408_; lean_object* v_unused_409_; lean_object* v_unused_410_; 
v_unused_408_ = lean_ctor_get(v_l_385_, 4);
lean_dec(v_unused_408_);
v_unused_409_ = lean_ctor_get(v_l_385_, 3);
lean_dec(v_unused_409_);
v_unused_410_ = lean_ctor_get(v_l_385_, 0);
lean_dec(v_unused_410_);
v___x_395_ = v_l_385_;
v_isShared_396_ = v_isSharedCheck_407_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_v_393_);
lean_inc(v_k_392_);
lean_dec(v_l_385_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_407_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_397_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_386_, 2);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 4, v_r_386_);
lean_ctor_set(v___x_395_, 3, v_r_386_);
lean_ctor_set(v___x_395_, 2, v_v_292_);
lean_ctor_set(v___x_395_, 1, v_k_291_);
lean_ctor_set(v___x_395_, 0, v___x_301_);
v___x_399_ = v___x_395_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_k_291_);
lean_ctor_set(v_reuseFailAlloc_406_, 2, v_v_292_);
lean_ctor_set(v_reuseFailAlloc_406_, 3, v_r_386_);
lean_ctor_set(v_reuseFailAlloc_406_, 4, v_r_386_);
v___x_399_ = v_reuseFailAlloc_406_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_401_; 
lean_inc(v_r_386_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 3, v_r_386_);
lean_ctor_set(v___x_390_, 0, v___x_301_);
v___x_401_ = v___x_390_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_k_387_);
lean_ctor_set(v_reuseFailAlloc_405_, 2, v_v_388_);
lean_ctor_set(v_reuseFailAlloc_405_, 3, v_r_386_);
lean_ctor_set(v_reuseFailAlloc_405_, 4, v_r_386_);
v___x_401_ = v_reuseFailAlloc_405_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_403_; 
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 4, v___x_401_);
lean_ctor_set(v___x_296_, 3, v___x_399_);
lean_ctor_set(v___x_296_, 2, v_v_393_);
lean_ctor_set(v___x_296_, 1, v_k_392_);
lean_ctor_set(v___x_296_, 0, v___x_397_);
v___x_403_ = v___x_296_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_397_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_k_392_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v_v_393_);
lean_ctor_set(v_reuseFailAlloc_404_, 3, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_404_, 4, v___x_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
}
}
else
{
lean_object* v_r_414_; 
v_r_414_ = lean_ctor_get(v_impl_300_, 4);
lean_inc(v_r_414_);
if (lean_obj_tag(v_r_414_) == 0)
{
lean_object* v_k_415_; lean_object* v_v_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_427_; 
v_k_415_ = lean_ctor_get(v_impl_300_, 1);
v_v_416_ = lean_ctor_get(v_impl_300_, 2);
v_isSharedCheck_427_ = !lean_is_exclusive(v_impl_300_);
if (v_isSharedCheck_427_ == 0)
{
lean_object* v_unused_428_; lean_object* v_unused_429_; lean_object* v_unused_430_; 
v_unused_428_ = lean_ctor_get(v_impl_300_, 4);
lean_dec(v_unused_428_);
v_unused_429_ = lean_ctor_get(v_impl_300_, 3);
lean_dec(v_unused_429_);
v_unused_430_ = lean_ctor_get(v_impl_300_, 0);
lean_dec(v_unused_430_);
v___x_418_ = v_impl_300_;
v_isShared_419_ = v_isSharedCheck_427_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_v_416_);
lean_inc(v_k_415_);
lean_dec(v_impl_300_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_427_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; lean_object* v___x_422_; 
v___x_420_ = lean_unsigned_to_nat(3u);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 4, v_l_385_);
lean_ctor_set(v___x_418_, 2, v_v_292_);
lean_ctor_set(v___x_418_, 1, v_k_291_);
lean_ctor_set(v___x_418_, 0, v___x_301_);
v___x_422_ = v___x_418_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_k_291_);
lean_ctor_set(v_reuseFailAlloc_426_, 2, v_v_292_);
lean_ctor_set(v_reuseFailAlloc_426_, 3, v_l_385_);
lean_ctor_set(v_reuseFailAlloc_426_, 4, v_l_385_);
v___x_422_ = v_reuseFailAlloc_426_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
lean_object* v___x_424_; 
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 4, v_r_414_);
lean_ctor_set(v___x_296_, 3, v___x_422_);
lean_ctor_set(v___x_296_, 2, v_v_416_);
lean_ctor_set(v___x_296_, 1, v_k_415_);
lean_ctor_set(v___x_296_, 0, v___x_420_);
v___x_424_ = v___x_296_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_k_415_);
lean_ctor_set(v_reuseFailAlloc_425_, 2, v_v_416_);
lean_ctor_set(v_reuseFailAlloc_425_, 3, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_425_, 4, v_r_414_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
else
{
lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_431_ = lean_unsigned_to_nat(2u);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 4, v_impl_300_);
lean_ctor_set(v___x_296_, 3, v_r_414_);
lean_ctor_set(v___x_296_, 0, v___x_431_);
v___x_433_ = v___x_296_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_k_291_);
lean_ctor_set(v_reuseFailAlloc_434_, 2, v_v_292_);
lean_ctor_set(v_reuseFailAlloc_434_, 3, v_r_414_);
lean_ctor_set(v_reuseFailAlloc_434_, 4, v_impl_300_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
else
{
lean_object* v___x_436_; 
lean_dec(v_v_292_);
lean_dec(v_k_291_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 2, v_v_288_);
lean_ctor_set(v___x_296_, 1, v_k_287_);
v___x_436_ = v___x_296_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_size_290_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_k_287_);
lean_ctor_set(v_reuseFailAlloc_437_, 2, v_v_288_);
lean_ctor_set(v_reuseFailAlloc_437_, 3, v_l_293_);
lean_ctor_set(v_reuseFailAlloc_437_, 4, v_r_294_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
else
{
lean_object* v_impl_438_; lean_object* v___x_439_; 
lean_dec(v_size_290_);
v_impl_438_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_k_287_, v_v_288_, v_l_293_);
v___x_439_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_294_) == 0)
{
lean_object* v_size_440_; lean_object* v_size_441_; lean_object* v_k_442_; lean_object* v_v_443_; lean_object* v_l_444_; lean_object* v_r_445_; lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v_size_440_ = lean_ctor_get(v_r_294_, 0);
v_size_441_ = lean_ctor_get(v_impl_438_, 0);
lean_inc(v_size_441_);
v_k_442_ = lean_ctor_get(v_impl_438_, 1);
lean_inc(v_k_442_);
v_v_443_ = lean_ctor_get(v_impl_438_, 2);
lean_inc(v_v_443_);
v_l_444_ = lean_ctor_get(v_impl_438_, 3);
lean_inc(v_l_444_);
v_r_445_ = lean_ctor_get(v_impl_438_, 4);
lean_inc(v_r_445_);
v___x_446_ = lean_unsigned_to_nat(3u);
v___x_447_ = lean_nat_mul(v___x_446_, v_size_440_);
v___x_448_ = lean_nat_dec_lt(v___x_447_, v_size_441_);
lean_dec(v___x_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
lean_dec(v_r_445_);
lean_dec(v_l_444_);
lean_dec(v_v_443_);
lean_dec(v_k_442_);
v___x_449_ = lean_nat_add(v___x_439_, v_size_441_);
lean_dec(v_size_441_);
v___x_450_ = lean_nat_add(v___x_449_, v_size_440_);
lean_dec(v___x_449_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 3, v_impl_438_);
lean_ctor_set(v___x_296_, 0, v___x_450_);
v___x_452_ = v___x_296_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_k_291_);
lean_ctor_set(v_reuseFailAlloc_453_, 2, v_v_292_);
lean_ctor_set(v_reuseFailAlloc_453_, 3, v_impl_438_);
lean_ctor_set(v_reuseFailAlloc_453_, 4, v_r_294_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
else
{
lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_519_; 
v_isSharedCheck_519_ = !lean_is_exclusive(v_impl_438_);
if (v_isSharedCheck_519_ == 0)
{
lean_object* v_unused_520_; lean_object* v_unused_521_; lean_object* v_unused_522_; lean_object* v_unused_523_; lean_object* v_unused_524_; 
v_unused_520_ = lean_ctor_get(v_impl_438_, 4);
lean_dec(v_unused_520_);
v_unused_521_ = lean_ctor_get(v_impl_438_, 3);
lean_dec(v_unused_521_);
v_unused_522_ = lean_ctor_get(v_impl_438_, 2);
lean_dec(v_unused_522_);
v_unused_523_ = lean_ctor_get(v_impl_438_, 1);
lean_dec(v_unused_523_);
v_unused_524_ = lean_ctor_get(v_impl_438_, 0);
lean_dec(v_unused_524_);
v___x_455_ = v_impl_438_;
v_isShared_456_ = v_isSharedCheck_519_;
goto v_resetjp_454_;
}
else
{
lean_dec(v_impl_438_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_519_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v_size_457_; lean_object* v_size_458_; lean_object* v_k_459_; lean_object* v_v_460_; lean_object* v_l_461_; lean_object* v_r_462_; lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v_size_457_ = lean_ctor_get(v_l_444_, 0);
v_size_458_ = lean_ctor_get(v_r_445_, 0);
v_k_459_ = lean_ctor_get(v_r_445_, 1);
v_v_460_ = lean_ctor_get(v_r_445_, 2);
v_l_461_ = lean_ctor_get(v_r_445_, 3);
v_r_462_ = lean_ctor_get(v_r_445_, 4);
v___x_463_ = lean_unsigned_to_nat(2u);
v___x_464_ = lean_nat_mul(v___x_463_, v_size_457_);
v___x_465_ = lean_nat_dec_lt(v_size_458_, v___x_464_);
lean_dec(v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_494_; 
lean_inc(v_r_462_);
lean_inc(v_l_461_);
lean_inc(v_v_460_);
lean_inc(v_k_459_);
v_isSharedCheck_494_ = !lean_is_exclusive(v_r_445_);
if (v_isSharedCheck_494_ == 0)
{
lean_object* v_unused_495_; lean_object* v_unused_496_; lean_object* v_unused_497_; lean_object* v_unused_498_; lean_object* v_unused_499_; 
v_unused_495_ = lean_ctor_get(v_r_445_, 4);
lean_dec(v_unused_495_);
v_unused_496_ = lean_ctor_get(v_r_445_, 3);
lean_dec(v_unused_496_);
v_unused_497_ = lean_ctor_get(v_r_445_, 2);
lean_dec(v_unused_497_);
v_unused_498_ = lean_ctor_get(v_r_445_, 1);
lean_dec(v_unused_498_);
v_unused_499_ = lean_ctor_get(v_r_445_, 0);
lean_dec(v_unused_499_);
v___x_467_ = v_r_445_;
v_isShared_468_ = v_isSharedCheck_494_;
goto v_resetjp_466_;
}
else
{
lean_dec(v_r_445_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_494_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___x_482_; lean_object* v___y_484_; 
v___x_469_ = lean_nat_add(v___x_439_, v_size_441_);
lean_dec(v_size_441_);
v___x_470_ = lean_nat_add(v___x_469_, v_size_440_);
lean_dec(v___x_469_);
v___x_482_ = lean_nat_add(v___x_439_, v_size_457_);
if (lean_obj_tag(v_l_461_) == 0)
{
lean_object* v_size_492_; 
v_size_492_ = lean_ctor_get(v_l_461_, 0);
lean_inc(v_size_492_);
v___y_484_ = v_size_492_;
goto v___jp_483_;
}
else
{
lean_object* v___x_493_; 
v___x_493_ = lean_unsigned_to_nat(0u);
v___y_484_ = v___x_493_;
goto v___jp_483_;
}
v___jp_471_:
{
lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_475_ = lean_nat_add(v___y_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec(v___y_473_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 4, v_r_294_);
lean_ctor_set(v___x_467_, 3, v_r_462_);
lean_ctor_set(v___x_467_, 2, v_v_292_);
lean_ctor_set(v___x_467_, 1, v_k_291_);
lean_ctor_set(v___x_467_, 0, v___x_475_);
v___x_477_ = v___x_467_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_k_291_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v_v_292_);
lean_ctor_set(v_reuseFailAlloc_481_, 3, v_r_462_);
lean_ctor_set(v_reuseFailAlloc_481_, 4, v_r_294_);
v___x_477_ = v_reuseFailAlloc_481_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___x_479_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v___x_477_);
lean_ctor_set(v___x_455_, 3, v___y_472_);
lean_ctor_set(v___x_455_, 2, v_v_460_);
lean_ctor_set(v___x_455_, 1, v_k_459_);
lean_ctor_set(v___x_455_, 0, v___x_470_);
v___x_479_ = v___x_455_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_470_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_k_459_);
lean_ctor_set(v_reuseFailAlloc_480_, 2, v_v_460_);
lean_ctor_set(v_reuseFailAlloc_480_, 3, v___y_472_);
lean_ctor_set(v_reuseFailAlloc_480_, 4, v___x_477_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
v___jp_483_:
{
lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_485_ = lean_nat_add(v___x_482_, v___y_484_);
lean_dec(v___y_484_);
lean_dec(v___x_482_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 4, v_l_461_);
lean_ctor_set(v___x_296_, 3, v_l_444_);
lean_ctor_set(v___x_296_, 2, v_v_443_);
lean_ctor_set(v___x_296_, 1, v_k_442_);
lean_ctor_set(v___x_296_, 0, v___x_485_);
v___x_487_ = v___x_296_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_k_442_);
lean_ctor_set(v_reuseFailAlloc_491_, 2, v_v_443_);
lean_ctor_set(v_reuseFailAlloc_491_, 3, v_l_444_);
lean_ctor_set(v_reuseFailAlloc_491_, 4, v_l_461_);
v___x_487_ = v_reuseFailAlloc_491_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_488_; 
v___x_488_ = lean_nat_add(v___x_439_, v_size_440_);
if (lean_obj_tag(v_r_462_) == 0)
{
lean_object* v_size_489_; 
v_size_489_ = lean_ctor_get(v_r_462_, 0);
lean_inc(v_size_489_);
v___y_472_ = v___x_487_;
v___y_473_ = v___x_488_;
v___y_474_ = v_size_489_;
goto v___jp_471_;
}
else
{
lean_object* v___x_490_; 
v___x_490_ = lean_unsigned_to_nat(0u);
v___y_472_ = v___x_487_;
v___y_473_ = v___x_488_;
v___y_474_ = v___x_490_;
goto v___jp_471_;
}
}
}
}
}
else
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_505_; 
lean_del_object(v___x_296_);
v___x_500_ = lean_nat_add(v___x_439_, v_size_441_);
lean_dec(v_size_441_);
v___x_501_ = lean_nat_add(v___x_500_, v_size_440_);
lean_dec(v___x_500_);
v___x_502_ = lean_nat_add(v___x_439_, v_size_440_);
v___x_503_ = lean_nat_add(v___x_502_, v_size_458_);
lean_dec(v___x_502_);
lean_inc_ref(v_r_294_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v_r_294_);
lean_ctor_set(v___x_455_, 3, v_r_445_);
lean_ctor_set(v___x_455_, 2, v_v_292_);
lean_ctor_set(v___x_455_, 1, v_k_291_);
lean_ctor_set(v___x_455_, 0, v___x_503_);
v___x_505_ = v___x_455_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_503_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_k_291_);
lean_ctor_set(v_reuseFailAlloc_518_, 2, v_v_292_);
lean_ctor_set(v_reuseFailAlloc_518_, 3, v_r_445_);
lean_ctor_set(v_reuseFailAlloc_518_, 4, v_r_294_);
v___x_505_ = v_reuseFailAlloc_518_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
v_isSharedCheck_512_ = !lean_is_exclusive(v_r_294_);
if (v_isSharedCheck_512_ == 0)
{
lean_object* v_unused_513_; lean_object* v_unused_514_; lean_object* v_unused_515_; lean_object* v_unused_516_; lean_object* v_unused_517_; 
v_unused_513_ = lean_ctor_get(v_r_294_, 4);
lean_dec(v_unused_513_);
v_unused_514_ = lean_ctor_get(v_r_294_, 3);
lean_dec(v_unused_514_);
v_unused_515_ = lean_ctor_get(v_r_294_, 2);
lean_dec(v_unused_515_);
v_unused_516_ = lean_ctor_get(v_r_294_, 1);
lean_dec(v_unused_516_);
v_unused_517_ = lean_ctor_get(v_r_294_, 0);
lean_dec(v_unused_517_);
v___x_507_ = v_r_294_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_dec(v_r_294_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 4, v___x_505_);
lean_ctor_set(v___x_507_, 3, v_l_444_);
lean_ctor_set(v___x_507_, 2, v_v_443_);
lean_ctor_set(v___x_507_, 1, v_k_442_);
lean_ctor_set(v___x_507_, 0, v___x_501_);
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_k_442_);
lean_ctor_set(v_reuseFailAlloc_511_, 2, v_v_443_);
lean_ctor_set(v_reuseFailAlloc_511_, 3, v_l_444_);
lean_ctor_set(v_reuseFailAlloc_511_, 4, v___x_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_525_; 
v_l_525_ = lean_ctor_get(v_impl_438_, 3);
lean_inc(v_l_525_);
if (lean_obj_tag(v_l_525_) == 0)
{
lean_object* v_r_526_; lean_object* v_k_527_; lean_object* v_v_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_539_; 
v_r_526_ = lean_ctor_get(v_impl_438_, 4);
v_k_527_ = lean_ctor_get(v_impl_438_, 1);
v_v_528_ = lean_ctor_get(v_impl_438_, 2);
v_isSharedCheck_539_ = !lean_is_exclusive(v_impl_438_);
if (v_isSharedCheck_539_ == 0)
{
lean_object* v_unused_540_; lean_object* v_unused_541_; 
v_unused_540_ = lean_ctor_get(v_impl_438_, 3);
lean_dec(v_unused_540_);
v_unused_541_ = lean_ctor_get(v_impl_438_, 0);
lean_dec(v_unused_541_);
v___x_530_ = v_impl_438_;
v_isShared_531_ = v_isSharedCheck_539_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_r_526_);
lean_inc(v_v_528_);
lean_inc(v_k_527_);
lean_dec(v_impl_438_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_539_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_532_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_526_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 3, v_r_526_);
lean_ctor_set(v___x_530_, 2, v_v_292_);
lean_ctor_set(v___x_530_, 1, v_k_291_);
lean_ctor_set(v___x_530_, 0, v___x_439_);
v___x_534_ = v___x_530_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_k_291_);
lean_ctor_set(v_reuseFailAlloc_538_, 2, v_v_292_);
lean_ctor_set(v_reuseFailAlloc_538_, 3, v_r_526_);
lean_ctor_set(v_reuseFailAlloc_538_, 4, v_r_526_);
v___x_534_ = v_reuseFailAlloc_538_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_536_; 
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 4, v___x_534_);
lean_ctor_set(v___x_296_, 3, v_l_525_);
lean_ctor_set(v___x_296_, 2, v_v_528_);
lean_ctor_set(v___x_296_, 1, v_k_527_);
lean_ctor_set(v___x_296_, 0, v___x_532_);
v___x_536_ = v___x_296_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_532_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v_k_527_);
lean_ctor_set(v_reuseFailAlloc_537_, 2, v_v_528_);
lean_ctor_set(v_reuseFailAlloc_537_, 3, v_l_525_);
lean_ctor_set(v_reuseFailAlloc_537_, 4, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
else
{
lean_object* v_r_542_; 
v_r_542_ = lean_ctor_get(v_impl_438_, 4);
lean_inc(v_r_542_);
if (lean_obj_tag(v_r_542_) == 0)
{
lean_object* v_k_543_; lean_object* v_v_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_567_; 
v_k_543_ = lean_ctor_get(v_impl_438_, 1);
v_v_544_ = lean_ctor_get(v_impl_438_, 2);
v_isSharedCheck_567_ = !lean_is_exclusive(v_impl_438_);
if (v_isSharedCheck_567_ == 0)
{
lean_object* v_unused_568_; lean_object* v_unused_569_; lean_object* v_unused_570_; 
v_unused_568_ = lean_ctor_get(v_impl_438_, 4);
lean_dec(v_unused_568_);
v_unused_569_ = lean_ctor_get(v_impl_438_, 3);
lean_dec(v_unused_569_);
v_unused_570_ = lean_ctor_get(v_impl_438_, 0);
lean_dec(v_unused_570_);
v___x_546_ = v_impl_438_;
v_isShared_547_ = v_isSharedCheck_567_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_v_544_);
lean_inc(v_k_543_);
lean_dec(v_impl_438_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_567_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v_k_548_; lean_object* v_v_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_563_; 
v_k_548_ = lean_ctor_get(v_r_542_, 1);
v_v_549_ = lean_ctor_get(v_r_542_, 2);
v_isSharedCheck_563_ = !lean_is_exclusive(v_r_542_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; lean_object* v_unused_565_; lean_object* v_unused_566_; 
v_unused_564_ = lean_ctor_get(v_r_542_, 4);
lean_dec(v_unused_564_);
v_unused_565_ = lean_ctor_get(v_r_542_, 3);
lean_dec(v_unused_565_);
v_unused_566_ = lean_ctor_get(v_r_542_, 0);
lean_dec(v_unused_566_);
v___x_551_ = v_r_542_;
v_isShared_552_ = v_isSharedCheck_563_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_v_549_);
lean_inc(v_k_548_);
lean_dec(v_r_542_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_563_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_553_ = lean_unsigned_to_nat(3u);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 4, v_l_525_);
lean_ctor_set(v___x_551_, 3, v_l_525_);
lean_ctor_set(v___x_551_, 2, v_v_544_);
lean_ctor_set(v___x_551_, 1, v_k_543_);
lean_ctor_set(v___x_551_, 0, v___x_439_);
v___x_555_ = v___x_551_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_k_543_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v_v_544_);
lean_ctor_set(v_reuseFailAlloc_562_, 3, v_l_525_);
lean_ctor_set(v_reuseFailAlloc_562_, 4, v_l_525_);
v___x_555_ = v_reuseFailAlloc_562_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_557_; 
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 4, v_l_525_);
lean_ctor_set(v___x_546_, 2, v_v_292_);
lean_ctor_set(v___x_546_, 1, v_k_291_);
lean_ctor_set(v___x_546_, 0, v___x_439_);
v___x_557_ = v___x_546_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_k_291_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v_v_292_);
lean_ctor_set(v_reuseFailAlloc_561_, 3, v_l_525_);
lean_ctor_set(v_reuseFailAlloc_561_, 4, v_l_525_);
v___x_557_ = v_reuseFailAlloc_561_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_559_; 
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 4, v___x_557_);
lean_ctor_set(v___x_296_, 3, v___x_555_);
lean_ctor_set(v___x_296_, 2, v_v_549_);
lean_ctor_set(v___x_296_, 1, v_k_548_);
lean_ctor_set(v___x_296_, 0, v___x_553_);
v___x_559_ = v___x_296_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_k_548_);
lean_ctor_set(v_reuseFailAlloc_560_, 2, v_v_549_);
lean_ctor_set(v_reuseFailAlloc_560_, 3, v___x_555_);
lean_ctor_set(v_reuseFailAlloc_560_, 4, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
}
}
else
{
lean_object* v___x_571_; lean_object* v___x_573_; 
v___x_571_ = lean_unsigned_to_nat(2u);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 4, v_r_542_);
lean_ctor_set(v___x_296_, 3, v_impl_438_);
lean_ctor_set(v___x_296_, 0, v___x_571_);
v___x_573_ = v___x_296_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_k_291_);
lean_ctor_set(v_reuseFailAlloc_574_, 2, v_v_292_);
lean_ctor_set(v_reuseFailAlloc_574_, 3, v_impl_438_);
lean_ctor_set(v_reuseFailAlloc_574_, 4, v_r_542_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_unsigned_to_nat(1u);
v___x_577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v_k_287_);
lean_ctor_set(v___x_577_, 2, v_v_288_);
lean_ctor_set(v___x_577_, 3, v_t_289_);
lean_ctor_set(v___x_577_, 4, v_t_289_);
return v___x_577_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange(lean_object* v_p_578_, uint8_t v_d_579_, lean_object* v_00_u03b4_580_){
_start:
{
lean_object* v_changesBefore_581_; lean_object* v_changesAfter_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_591_; 
v_changesBefore_581_ = lean_ctor_get(v_00_u03b4_580_, 0);
v_changesAfter_582_ = lean_ctor_get(v_00_u03b4_580_, 1);
v_isSharedCheck_591_ = !lean_is_exclusive(v_00_u03b4_580_);
if (v_isSharedCheck_591_ == 0)
{
v___x_584_ = v_00_u03b4_580_;
v_isShared_585_ = v_isSharedCheck_591_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_changesAfter_582_);
lean_inc(v_changesBefore_581_);
lean_dec(v_00_u03b4_580_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_591_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_586_ = lean_box(v_d_579_);
v___x_587_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_p_578_, v___x_586_, v_changesBefore_581_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_587_);
v___x_589_ = v___x_584_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_changesAfter_582_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange___boxed(lean_object* v_p_592_, lean_object* v_d_593_, lean_object* v_00_u03b4_594_){
_start:
{
uint8_t v_d_boxed_595_; lean_object* v_res_596_; 
v_d_boxed_595_ = lean_unbox(v_d_593_);
v_res_596_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange(v_p_592_, v_d_boxed_595_, v_00_u03b4_594_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0(lean_object* v_00_u03b2_597_, lean_object* v_k_598_, lean_object* v_v_599_, lean_object* v_t_600_, lean_object* v_hl_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_k_598_, v_v_599_, v_t_600_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertAfterChange(lean_object* v_p_603_, uint8_t v_d_604_, lean_object* v_00_u03b4_605_){
_start:
{
lean_object* v_changesBefore_606_; lean_object* v_changesAfter_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_616_; 
v_changesBefore_606_ = lean_ctor_get(v_00_u03b4_605_, 0);
v_changesAfter_607_ = lean_ctor_get(v_00_u03b4_605_, 1);
v_isSharedCheck_616_ = !lean_is_exclusive(v_00_u03b4_605_);
if (v_isSharedCheck_616_ == 0)
{
v___x_609_ = v_00_u03b4_605_;
v_isShared_610_ = v_isSharedCheck_616_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_changesAfter_607_);
lean_inc(v_changesBefore_606_);
lean_dec(v_00_u03b4_605_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_616_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_611_ = lean_box(v_d_604_);
v___x_612_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_p_603_, v___x_611_, v_changesAfter_607_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 1, v___x_612_);
v___x_614_ = v___x_609_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_changesBefore_606_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v___x_612_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertAfterChange___boxed(lean_object* v_p_617_, lean_object* v_d_618_, lean_object* v_00_u03b4_619_){
_start:
{
uint8_t v_d_boxed_620_; lean_object* v_res_621_; 
v_d_boxed_620_ = lean_unbox(v_d_618_);
v_res_621_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertAfterChange(v_p_617_, v_d_boxed_620_, v_00_u03b4_619_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(lean_object* v_before_622_, lean_object* v_after_623_, uint8_t v_d_624_){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_625_ = lean_box(1);
v___x_626_ = lean_box(v_d_624_);
v___x_627_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_before_622_, v___x_626_, v___x_625_);
v___x_628_ = lean_box(v_d_624_);
v___x_629_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_after_623_, v___x_628_, v___x_625_);
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_627_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos___boxed(lean_object* v_before_631_, lean_object* v_after_632_, lean_object* v_d_633_){
_start:
{
uint8_t v_d_boxed_634_; lean_object* v_res_635_; 
v_d_boxed_634_ = lean_unbox(v_d_633_);
v_res_635_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v_before_631_, v_after_632_, v_d_boxed_634_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(lean_object* v_before_636_, lean_object* v_after_637_, uint8_t v_d_638_){
_start:
{
lean_object* v_pos_639_; lean_object* v_pos_640_; lean_object* v___x_641_; 
v_pos_639_ = lean_ctor_get(v_before_636_, 1);
lean_inc(v_pos_639_);
lean_dec_ref(v_before_636_);
v_pos_640_ = lean_ctor_get(v_after_637_, 1);
lean_inc(v_pos_640_);
lean_dec_ref(v_after_637_);
v___x_641_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v_pos_639_, v_pos_640_, v_d_638_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange___boxed(lean_object* v_before_642_, lean_object* v_after_643_, lean_object* v_d_644_){
_start:
{
uint8_t v_d_boxed_645_; lean_object* v_res_646_; 
v_d_boxed_645_ = lean_unbox(v_d_644_);
v_res_646_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_642_, v_after_643_, v_d_boxed_645_);
return v_res_646_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(lean_object* v_d_647_){
_start:
{
lean_object* v_changesAfter_648_; 
v_changesAfter_648_ = lean_ctor_get(v_d_647_, 1);
if (lean_obj_tag(v_changesAfter_648_) == 0)
{
uint8_t v___x_649_; 
v___x_649_ = 0;
return v___x_649_;
}
else
{
lean_object* v_changesBefore_650_; 
v_changesBefore_650_ = lean_ctor_get(v_d_647_, 0);
if (lean_obj_tag(v_changesBefore_650_) == 0)
{
uint8_t v___x_651_; 
v___x_651_ = 0;
return v___x_651_;
}
else
{
uint8_t v___x_652_; 
v___x_652_ = 1;
return v___x_652_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty___boxed(lean_object* v_d_653_){
_start:
{
uint8_t v_res_654_; lean_object* v_r_655_; 
v_res_654_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_d_653_);
lean_dec_ref(v_d_653_);
v_r_655_ = lean_box(v_res_654_);
return v_r_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0(lean_object* v_k_656_, lean_object* v_b_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v___x_663_; 
lean_inc(v___y_661_);
lean_inc_ref(v___y_660_);
lean_inc(v___y_659_);
lean_inc_ref(v___y_658_);
v___x_663_ = lean_apply_6(v_k_656_, v_b_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, lean_box(0));
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0___boxed(lean_object* v_k_664_, lean_object* v_b_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0(v_k_664_, v_b_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(lean_object* v_name_672_, uint8_t v_bi_673_, lean_object* v_type_674_, lean_object* v_k_675_, uint8_t v_kind_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v___f_682_; lean_object* v___x_683_; 
v___f_682_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_682_, 0, v_k_675_);
v___x_683_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_672_, v_bi_673_, v_type_674_, v___f_682_, v_kind_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_683_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_683_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
else
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
v_a_692_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_683_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_683_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___boxed(lean_object* v_name_700_, lean_object* v_bi_701_, lean_object* v_type_702_, lean_object* v_k_703_, lean_object* v_kind_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
uint8_t v_bi_boxed_710_; uint8_t v_kind_boxed_711_; lean_object* v_res_712_; 
v_bi_boxed_710_ = lean_unbox(v_bi_701_);
v_kind_boxed_711_ = lean_unbox(v_kind_704_);
v_res_712_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_name_700_, v_bi_boxed_710_, v_type_702_, v_k_703_, v_kind_boxed_711_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6(lean_object* v_00_u03b1_713_, lean_object* v_name_714_, uint8_t v_bi_715_, lean_object* v_type_716_, lean_object* v_k_717_, uint8_t v_kind_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_name_714_, v_bi_715_, v_type_716_, v_k_717_, v_kind_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___boxed(lean_object* v_00_u03b1_725_, lean_object* v_name_726_, lean_object* v_bi_727_, lean_object* v_type_728_, lean_object* v_k_729_, lean_object* v_kind_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
uint8_t v_bi_boxed_736_; uint8_t v_kind_boxed_737_; lean_object* v_res_738_; 
v_bi_boxed_736_ = lean_unbox(v_bi_727_);
v_kind_boxed_737_ = lean_unbox(v_kind_730_);
v_res_738_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6(v_00_u03b1_725_, v_name_726_, v_bi_boxed_736_, v_type_728_, v_k_729_, v_kind_boxed_737_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(lean_object* v_msgData_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v___x_745_; lean_object* v_env_746_; lean_object* v___x_747_; lean_object* v_mctx_748_; lean_object* v_lctx_749_; lean_object* v_options_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_745_ = lean_st_ref_get(v___y_743_);
v_env_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc_ref(v_env_746_);
lean_dec(v___x_745_);
v___x_747_ = lean_st_ref_get(v___y_741_);
v_mctx_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc_ref(v_mctx_748_);
lean_dec(v___x_747_);
v_lctx_749_ = lean_ctor_get(v___y_740_, 2);
v_options_750_ = lean_ctor_get(v___y_742_, 2);
lean_inc_ref(v_options_750_);
lean_inc_ref(v_lctx_749_);
v___x_751_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_751_, 0, v_env_746_);
lean_ctor_set(v___x_751_, 1, v_mctx_748_);
lean_ctor_set(v___x_751_, 2, v_lctx_749_);
lean_ctor_set(v___x_751_, 3, v_options_750_);
v___x_752_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
lean_ctor_set(v___x_752_, 1, v_msgData_739_);
v___x_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4___boxed(lean_object* v_msgData_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(v_msgData_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(lean_object* v_msg_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v_ref_767_; lean_object* v___x_768_; lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_777_; 
v_ref_767_ = lean_ctor_get(v___y_764_, 5);
v___x_768_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(v_msg_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
v_a_769_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_777_ == 0)
{
v___x_771_ = v___x_768_;
v_isShared_772_ = v_isSharedCheck_777_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_768_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_777_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; lean_object* v___x_775_; 
lean_inc(v_ref_767_);
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v_ref_767_);
lean_ctor_set(v___x_773_, 1, v_a_769_);
if (v_isShared_772_ == 0)
{
lean_ctor_set_tag(v___x_771_, 1);
lean_ctor_set(v___x_771_, 0, v___x_773_);
v___x_775_ = v___x_771_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg___boxed(lean_object* v_msg_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v_msg_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(lean_object* v_x_785_, lean_object* v_x_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
if (lean_obj_tag(v_x_785_) == 0)
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = l_List_reverse___redArg(v_x_786_);
v___x_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
return v___x_793_;
}
else
{
lean_object* v_head_794_; lean_object* v_tail_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_813_; 
v_head_794_ = lean_ctor_get(v_x_785_, 0);
v_tail_795_ = lean_ctor_get(v_x_785_, 1);
v_isSharedCheck_813_ = !lean_is_exclusive(v_x_785_);
if (v_isSharedCheck_813_ == 0)
{
v___x_797_ = v_x_785_;
v_isShared_798_ = v_isSharedCheck_813_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_tail_795_);
lean_inc(v_head_794_);
lean_dec(v_x_785_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_813_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_Meta_getFVarFromUserName(v_head_794_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_802_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
lean_dec_ref(v___x_799_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 1, v_x_786_);
lean_ctor_set(v___x_797_, 0, v_a_800_);
v___x_802_ = v___x_797_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_800_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_x_786_);
v___x_802_ = v_reuseFailAlloc_804_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
v_x_785_ = v_tail_795_;
v_x_786_ = v___x_802_;
goto _start;
}
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_del_object(v___x_797_);
lean_dec(v_tail_795_);
lean_dec(v_x_786_);
v_a_805_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_799_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_799_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2___boxed(lean_object* v_x_814_, lean_object* v_x_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(v_x_814_, v_x_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(lean_object* v_upperBound_822_, lean_object* v_before_823_, lean_object* v_a_824_, lean_object* v_b_825_){
_start:
{
uint8_t v___x_827_; 
v___x_827_ = lean_nat_dec_lt(v_a_824_, v_upperBound_822_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; 
lean_dec(v_a_824_);
lean_dec_ref(v_before_823_);
v___x_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_828_, 0, v_b_825_);
return v___x_828_;
}
else
{
lean_object* v_pos_829_; lean_object* v___x_830_; uint8_t v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v_pos_829_ = lean_ctor_get(v_before_823_, 1);
lean_inc(v_pos_829_);
lean_inc(v_a_824_);
v___x_830_ = l_Lean_SubExpr_Pos_pushNthBindingDomain(v_a_824_, v_pos_829_);
v___x_831_ = 1;
v___x_832_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange(v___x_830_, v___x_831_, v_b_825_);
v___x_833_ = lean_unsigned_to_nat(1u);
v___x_834_ = lean_nat_add(v_a_824_, v___x_833_);
lean_dec(v_a_824_);
v_a_824_ = v___x_834_;
v_b_825_ = v___x_832_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg___boxed(lean_object* v_upperBound_836_, lean_object* v_before_837_, lean_object* v_a_838_, lean_object* v_b_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v_upperBound_836_, v_before_837_, v_a_838_, v_b_839_);
lean_dec(v_upperBound_836_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0(lean_object* v_x_842_, lean_object* v_x_843_){
_start:
{
if (lean_obj_tag(v_x_842_) == 0)
{
lean_object* v___x_844_; 
v___x_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_844_, 0, v_x_843_);
return v___x_844_;
}
else
{
if (lean_obj_tag(v_x_843_) == 0)
{
lean_object* v___x_845_; 
v___x_845_ = lean_box(0);
return v___x_845_;
}
else
{
lean_object* v_head_846_; lean_object* v_tail_847_; lean_object* v_head_848_; lean_object* v_tail_849_; uint8_t v___x_850_; 
v_head_846_ = lean_ctor_get(v_x_842_, 0);
v_tail_847_ = lean_ctor_get(v_x_842_, 1);
v_head_848_ = lean_ctor_get(v_x_843_, 0);
lean_inc(v_head_848_);
v_tail_849_ = lean_ctor_get(v_x_843_, 1);
lean_inc(v_tail_849_);
lean_dec_ref(v_x_843_);
v___x_850_ = lean_name_eq(v_head_846_, v_head_848_);
lean_dec(v_head_848_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; 
lean_dec(v_tail_849_);
v___x_851_ = lean_box(0);
return v___x_851_;
}
else
{
v_x_842_ = v_tail_847_;
v_x_843_ = v_tail_849_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0___boxed(lean_object* v_x_853_, lean_object* v_x_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0(v_x_853_, v_x_854_);
lean_dec(v_x_853_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0(lean_object* v_l_u2081_856_, lean_object* v_l_u2082_857_){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_858_ = l_List_reverse___redArg(v_l_u2081_856_);
v___x_859_ = l_List_reverse___redArg(v_l_u2082_857_);
v___x_860_ = l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0(v___x_858_, v___x_859_);
lean_dec(v___x_858_);
if (lean_obj_tag(v___x_860_) == 0)
{
return v___x_860_;
}
else
{
lean_object* v_val_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_869_; 
v_val_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_869_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_val_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v___x_867_; 
v___x_865_ = l_List_reverse___redArg(v_val_861_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_865_);
v___x_867_ = v___x_863_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_865_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(uint8_t v_b_u2082_870_, lean_object* v_k_871_, lean_object* v_t_872_){
_start:
{
if (lean_obj_tag(v_t_872_) == 0)
{
lean_object* v_size_873_; lean_object* v_k_874_; lean_object* v_v_875_; lean_object* v_l_876_; lean_object* v_r_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_891_; 
v_size_873_ = lean_ctor_get(v_t_872_, 0);
v_k_874_ = lean_ctor_get(v_t_872_, 1);
v_v_875_ = lean_ctor_get(v_t_872_, 2);
v_l_876_ = lean_ctor_get(v_t_872_, 3);
v_r_877_ = lean_ctor_get(v_t_872_, 4);
v_isSharedCheck_891_ = !lean_is_exclusive(v_t_872_);
if (v_isSharedCheck_891_ == 0)
{
v___x_879_ = v_t_872_;
v_isShared_880_ = v_isSharedCheck_891_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_r_877_);
lean_inc(v_l_876_);
lean_inc(v_v_875_);
lean_inc(v_k_874_);
lean_inc(v_size_873_);
lean_dec(v_t_872_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_891_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
uint8_t v___x_881_; 
v___x_881_ = lean_nat_dec_lt(v_k_871_, v_k_874_);
if (v___x_881_ == 0)
{
uint8_t v___x_882_; 
v___x_882_ = lean_nat_dec_eq(v_k_871_, v_k_874_);
if (v___x_882_ == 0)
{
lean_object* v_impl_883_; lean_object* v___x_884_; 
lean_del_object(v___x_879_);
lean_dec(v_size_873_);
v_impl_883_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_870_, v_k_871_, v_r_877_);
v___x_884_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_874_, v_v_875_, v_l_876_, v_impl_883_);
return v___x_884_;
}
else
{
lean_object* v___x_885_; lean_object* v___x_887_; 
lean_dec(v_v_875_);
lean_dec(v_k_874_);
v___x_885_ = lean_box(v_b_u2082_870_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 2, v___x_885_);
lean_ctor_set(v___x_879_, 1, v_k_871_);
v___x_887_ = v___x_879_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_size_873_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_k_871_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v___x_885_);
lean_ctor_set(v_reuseFailAlloc_888_, 3, v_l_876_);
lean_ctor_set(v_reuseFailAlloc_888_, 4, v_r_877_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
else
{
lean_object* v_impl_889_; lean_object* v___x_890_; 
lean_del_object(v___x_879_);
lean_dec(v_size_873_);
v_impl_889_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_870_, v_k_871_, v_l_876_);
v___x_890_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_874_, v_v_875_, v_impl_889_, v_r_877_);
return v___x_890_;
}
}
}
else
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_892_ = lean_unsigned_to_nat(1u);
v___x_893_ = lean_box(v_b_u2082_870_);
v___x_894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_894_, 0, v___x_892_);
lean_ctor_set(v___x_894_, 1, v_k_871_);
lean_ctor_set(v___x_894_, 2, v___x_893_);
lean_ctor_set(v___x_894_, 3, v_t_872_);
lean_ctor_set(v___x_894_, 4, v_t_872_);
return v___x_894_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg___boxed(lean_object* v_b_u2082_895_, lean_object* v_k_896_, lean_object* v_t_897_){
_start:
{
uint8_t v_b_u2082_boxed_898_; lean_object* v_res_899_; 
v_b_u2082_boxed_898_ = lean_unbox(v_b_u2082_895_);
v_res_899_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_boxed_898_, v_k_896_, v_t_897_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(lean_object* v_init_900_, lean_object* v_x_901_){
_start:
{
if (lean_obj_tag(v_x_901_) == 0)
{
lean_object* v_k_902_; lean_object* v_v_903_; lean_object* v_l_904_; lean_object* v_r_905_; lean_object* v___x_906_; uint8_t v___x_907_; lean_object* v___x_908_; 
v_k_902_ = lean_ctor_get(v_x_901_, 1);
lean_inc(v_k_902_);
v_v_903_ = lean_ctor_get(v_x_901_, 2);
lean_inc(v_v_903_);
v_l_904_ = lean_ctor_get(v_x_901_, 3);
lean_inc(v_l_904_);
v_r_905_ = lean_ctor_get(v_x_901_, 4);
lean_inc(v_r_905_);
lean_dec_ref(v_x_901_);
v___x_906_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_init_900_, v_l_904_);
v___x_907_ = lean_unbox(v_v_903_);
lean_dec(v_v_903_);
v___x_908_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v___x_907_, v_k_902_, v___x_906_);
v_init_900_ = v___x_908_;
v_x_901_ = v_r_905_;
goto _start;
}
else
{
return v_init_900_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(lean_object* v_as_910_, size_t v_i_911_, size_t v_stop_912_, lean_object* v_b_913_){
_start:
{
uint8_t v___x_914_; 
v___x_914_ = lean_usize_dec_eq(v_i_911_, v_stop_912_);
if (v___x_914_ == 0)
{
lean_object* v_changesBefore_915_; lean_object* v_changesAfter_916_; lean_object* v___x_917_; lean_object* v_changesBefore_918_; lean_object* v_changesAfter_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_931_; 
v_changesBefore_915_ = lean_ctor_get(v_b_913_, 0);
lean_inc(v_changesBefore_915_);
v_changesAfter_916_ = lean_ctor_get(v_b_913_, 1);
lean_inc(v_changesAfter_916_);
lean_dec_ref(v_b_913_);
v___x_917_ = lean_array_uget(v_as_910_, v_i_911_);
v_changesBefore_918_ = lean_ctor_get(v___x_917_, 0);
v_changesAfter_919_ = lean_ctor_get(v___x_917_, 1);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_931_ == 0)
{
v___x_921_ = v___x_917_;
v_isShared_922_ = v_isSharedCheck_931_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_changesAfter_919_);
lean_inc(v_changesBefore_918_);
lean_dec(v___x_917_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_931_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_923_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesBefore_915_, v_changesBefore_918_);
v___x_924_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesAfter_916_, v_changesAfter_919_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 1, v___x_924_);
lean_ctor_set(v___x_921_, 0, v___x_923_);
v___x_926_ = v___x_921_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_923_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v___x_924_);
v___x_926_ = v_reuseFailAlloc_930_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
size_t v___x_927_; size_t v___x_928_; 
v___x_927_ = ((size_t)1ULL);
v___x_928_ = lean_usize_add(v_i_911_, v___x_927_);
v_i_911_ = v___x_928_;
v_b_913_ = v___x_926_;
goto _start;
}
}
}
else
{
return v_b_913_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10___boxed(lean_object* v_as_932_, lean_object* v_i_933_, lean_object* v_stop_934_, lean_object* v_b_935_){
_start:
{
size_t v_i_boxed_936_; size_t v_stop_boxed_937_; lean_object* v_res_938_; 
v_i_boxed_936_ = lean_unbox_usize(v_i_933_);
lean_dec(v_i_933_);
v_stop_boxed_937_ = lean_unbox_usize(v_stop_934_);
lean_dec(v_stop_934_);
v_res_938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_as_932_, v_i_boxed_936_, v_stop_boxed_937_, v_b_935_);
lean_dec_ref(v_as_932_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(lean_object* v_x_939_, lean_object* v_x_940_, lean_object* v_x_941_){
_start:
{
if (lean_obj_tag(v_x_939_) == 5)
{
lean_object* v_fn_942_; lean_object* v_arg_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v_fn_942_ = lean_ctor_get(v_x_939_, 0);
lean_inc_ref(v_fn_942_);
v_arg_943_ = lean_ctor_get(v_x_939_, 1);
lean_inc_ref(v_arg_943_);
lean_dec_ref(v_x_939_);
v___x_944_ = lean_array_set(v_x_940_, v_x_941_, v_arg_943_);
v___x_945_ = lean_unsigned_to_nat(1u);
v___x_946_ = lean_nat_sub(v_x_941_, v___x_945_);
lean_dec(v_x_941_);
v_x_939_ = v_fn_942_;
v_x_940_ = v___x_944_;
v_x_941_ = v___x_946_;
goto _start;
}
else
{
lean_object* v___x_948_; 
lean_dec(v_x_941_);
v___x_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_948_, 0, v_x_939_);
lean_ctor_set(v___x_948_, 1, v_x_940_);
return v___x_948_;
}
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0(void){
_start:
{
lean_object* v___x_949_; lean_object* v_dummy_950_; 
v___x_949_ = lean_box(0);
v_dummy_950_ = l_Lean_Expr_sort___override(v___x_949_);
return v_dummy_950_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(lean_object* v_snd_951_, lean_object* v_before_952_, lean_object* v_after_953_, lean_object* v_as_954_, lean_object* v_i_955_, lean_object* v_j_956_, lean_object* v_bs_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_zero_963_; uint8_t v_isZero_964_; 
v_zero_963_ = lean_unsigned_to_nat(0u);
v_isZero_964_ = lean_nat_dec_eq(v_i_955_, v_zero_963_);
if (v_isZero_964_ == 1)
{
lean_object* v___x_965_; 
lean_dec(v_j_956_);
lean_dec(v_i_955_);
v___x_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_965_, 0, v_bs_957_);
return v___x_965_;
}
else
{
lean_object* v___x_966_; lean_object* v_fst_967_; lean_object* v_snd_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_996_; 
v___x_966_ = lean_array_fget(v_as_954_, v_j_956_);
v_fst_967_ = lean_ctor_get(v___x_966_, 0);
v_snd_968_ = lean_ctor_get(v___x_966_, 1);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_996_ == 0)
{
v___x_970_ = v___x_966_;
v_isShared_971_ = v_isSharedCheck_996_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_snd_968_);
lean_inc(v_fst_967_);
lean_dec(v___x_966_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_996_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v_pos_972_; lean_object* v_pos_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_977_; 
v_pos_972_ = lean_ctor_get(v_before_952_, 1);
v_pos_973_ = lean_ctor_get(v_after_953_, 1);
v___x_974_ = lean_array_get_size(v_snd_951_);
v___x_975_ = l_Lean_SubExpr_Pos_pushNaryArg(v___x_974_, v_j_956_, v_pos_972_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 1, v___x_975_);
v___x_977_ = v___x_970_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_fst_967_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v___x_975_);
v___x_977_ = v_reuseFailAlloc_995_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_978_ = l_Lean_SubExpr_Pos_pushNaryArg(v___x_974_, v_j_956_, v_pos_973_);
v___x_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_979_, 0, v_snd_968_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v___x_980_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_977_, v___x_979_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v_one_982_; lean_object* v_n_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref(v___x_980_);
v_one_982_ = lean_unsigned_to_nat(1u);
v_n_983_ = lean_nat_sub(v_i_955_, v_one_982_);
lean_dec(v_i_955_);
v___x_984_ = lean_nat_add(v_j_956_, v_one_982_);
lean_dec(v_j_956_);
v___x_985_ = lean_array_push(v_bs_957_, v_a_981_);
v_i_955_ = v_n_983_;
v_j_956_ = v___x_984_;
v_bs_957_ = v___x_985_;
goto _start;
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_dec_ref(v_bs_957_);
lean_dec(v_j_956_);
lean_dec(v_i_955_);
v_a_987_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_980_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_980_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
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
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__0));
v___x_999_ = l_Lean_stringToMessageData(v___x_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0___boxed(lean_object* v_body_1000_, lean_object* v_pos_1001_, lean_object* v_body_1002_, lean_object* v_pos_1003_, lean_object* v_x_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0(v_body_1000_, v_pos_1001_, v_body_1002_, v_pos_1003_, v_x_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec_ref(v_x_1004_);
lean_dec(v_pos_1003_);
lean_dec_ref(v_body_1002_);
lean_dec(v_pos_1001_);
lean_dec_ref(v_body_1000_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(lean_object* v_before_1011_, lean_object* v_after_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v_a_1024_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; uint8_t v___y_1035_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v_a_1054_; lean_object* v_expr_1057_; lean_object* v_pos_1058_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; 
v_expr_1057_ = lean_ctor_get(v_before_1011_, 0);
v_pos_1058_ = lean_ctor_get(v_before_1011_, 1);
if (lean_obj_tag(v_expr_1057_) == 7)
{
lean_object* v_binderName_1095_; lean_object* v_binderType_1096_; lean_object* v_body_1097_; uint8_t v_binderInfo_1098_; lean_object* v_expr_1099_; lean_object* v_pos_1100_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; 
v_binderName_1095_ = lean_ctor_get(v_expr_1057_, 0);
v_binderType_1096_ = lean_ctor_get(v_expr_1057_, 1);
v_body_1097_ = lean_ctor_get(v_expr_1057_, 2);
v_binderInfo_1098_ = lean_ctor_get_uint8(v_expr_1057_, sizeof(void*)*3 + 8);
v_expr_1099_ = lean_ctor_get(v_after_1012_, 0);
v_pos_1100_ = lean_ctor_get(v_after_1012_, 1);
if (lean_obj_tag(v_expr_1099_) == 7)
{
lean_object* v_binderName_1126_; lean_object* v_binderType_1127_; lean_object* v_body_1128_; uint8_t v_binderInfo_1129_; lean_object* v___f_1130_; uint8_t v___y_1132_; uint8_t v___x_1182_; 
v_binderName_1126_ = lean_ctor_get(v_expr_1099_, 0);
v_binderType_1127_ = lean_ctor_get(v_expr_1099_, 1);
v_body_1128_ = lean_ctor_get(v_expr_1099_, 2);
v_binderInfo_1129_ = lean_ctor_get_uint8(v_expr_1099_, sizeof(void*)*3 + 8);
lean_inc(v_pos_1100_);
lean_inc_ref(v_body_1128_);
lean_inc(v_pos_1058_);
lean_inc_ref(v_body_1097_);
v___f_1130_ = lean_alloc_closure((void*)(l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1130_, 0, v_body_1097_);
lean_closure_set(v___f_1130_, 1, v_pos_1058_);
lean_closure_set(v___f_1130_, 2, v_body_1128_);
lean_closure_set(v___f_1130_, 3, v_pos_1100_);
v___x_1182_ = lean_name_eq(v_binderName_1095_, v_binderName_1126_);
if (v___x_1182_ == 0)
{
v___y_1132_ = v___x_1182_;
goto v___jp_1131_;
}
else
{
uint8_t v___x_1183_; 
v___x_1183_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1098_, v_binderInfo_1129_);
v___y_1132_ = v___x_1183_;
goto v___jp_1131_;
}
v___jp_1131_:
{
if (v___y_1132_ == 0)
{
lean_dec_ref(v___f_1130_);
v___y_1102_ = v_a_1013_;
v___y_1103_ = v_a_1014_;
v___y_1104_ = v_a_1015_;
v___y_1105_ = v_a_1016_;
goto v___jp_1101_;
}
else
{
lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1179_; 
lean_inc_ref(v_binderType_1127_);
lean_inc(v_pos_1100_);
lean_inc_ref(v_binderType_1096_);
lean_inc(v_binderName_1095_);
lean_inc(v_pos_1058_);
v_isSharedCheck_1179_ = !lean_is_exclusive(v_before_1011_);
if (v_isSharedCheck_1179_ == 0)
{
lean_object* v_unused_1180_; lean_object* v_unused_1181_; 
v_unused_1180_ = lean_ctor_get(v_before_1011_, 1);
lean_dec(v_unused_1180_);
v_unused_1181_ = lean_ctor_get(v_before_1011_, 0);
lean_dec(v_unused_1181_);
v___x_1134_ = v_before_1011_;
v_isShared_1135_ = v_isSharedCheck_1179_;
goto v_resetjp_1133_;
}
else
{
lean_dec(v_before_1011_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1179_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1176_; 
v_isSharedCheck_1176_ = !lean_is_exclusive(v_after_1012_);
if (v_isSharedCheck_1176_ == 0)
{
lean_object* v_unused_1177_; lean_object* v_unused_1178_; 
v_unused_1177_ = lean_ctor_get(v_after_1012_, 1);
lean_dec(v_unused_1177_);
v_unused_1178_ = lean_ctor_get(v_after_1012_, 0);
lean_dec(v_unused_1178_);
v___x_1137_ = v_after_1012_;
v_isShared_1138_ = v_isSharedCheck_1176_;
goto v_resetjp_1136_;
}
else
{
lean_dec(v_after_1012_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1176_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1139_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1058_);
lean_inc_ref(v_binderType_1096_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 1, v___x_1139_);
lean_ctor_set(v___x_1137_, 0, v_binderType_1096_);
v___x_1141_ = v___x_1137_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_binderType_1096_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1142_; lean_object* v___x_1144_; 
v___x_1142_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1100_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 1, v___x_1142_);
lean_ctor_set(v___x_1134_, 0, v_binderType_1127_);
v___x_1144_ = v___x_1134_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_binderType_1127_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v___x_1142_);
v___x_1144_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1145_; 
v___x_1145_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1141_, v___x_1144_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1173_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1148_ = v___x_1145_;
v_isShared_1149_ = v_isSharedCheck_1173_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1145_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1173_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
uint8_t v___x_1150_; 
v___x_1150_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_a_1146_);
if (v___x_1150_ == 0)
{
lean_object* v_changesBefore_1151_; lean_object* v_changesAfter_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; uint8_t v___x_1155_; lean_object* v___x_1156_; lean_object* v_changesBefore_1157_; lean_object* v_changesAfter_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1170_; 
lean_dec_ref(v___f_1130_);
lean_dec_ref(v_binderType_1096_);
lean_dec(v_binderName_1095_);
v_changesBefore_1151_ = lean_ctor_get(v_a_1146_, 0);
lean_inc(v_changesBefore_1151_);
v_changesAfter_1152_ = lean_ctor_get(v_a_1146_, 1);
lean_inc(v_changesAfter_1152_);
lean_dec(v_a_1146_);
v___x_1153_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1058_);
lean_dec(v_pos_1058_);
v___x_1154_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1100_);
lean_dec(v_pos_1100_);
v___x_1155_ = 0;
v___x_1156_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v___x_1153_, v___x_1154_, v___x_1155_);
v_changesBefore_1157_ = lean_ctor_get(v___x_1156_, 0);
v_changesAfter_1158_ = lean_ctor_get(v___x_1156_, 1);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1160_ = v___x_1156_;
v_isShared_1161_ = v_isSharedCheck_1170_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_changesAfter_1158_);
lean_inc(v_changesBefore_1157_);
lean_dec(v___x_1156_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1170_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1162_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesBefore_1151_, v_changesBefore_1157_);
v___x_1163_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesAfter_1152_, v_changesAfter_1158_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 1, v___x_1163_);
lean_ctor_set(v___x_1160_, 0, v___x_1162_);
v___x_1165_ = v___x_1160_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1167_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1165_);
v___x_1167_ = v___x_1148_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
else
{
uint8_t v___x_1171_; lean_object* v___x_1172_; 
lean_del_object(v___x_1148_);
lean_dec(v_a_1146_);
lean_dec(v_pos_1100_);
lean_dec(v_pos_1058_);
v___x_1171_ = 0;
v___x_1172_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_binderName_1095_, v_binderInfo_1098_, v_binderType_1096_, v___f_1130_, v___x_1171_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
return v___x_1172_;
}
}
}
else
{
lean_dec_ref(v___f_1130_);
lean_dec(v_pos_1100_);
lean_dec_ref(v_binderType_1096_);
lean_dec(v_binderName_1095_);
lean_dec(v_pos_1058_);
return v___x_1145_;
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
v___y_1102_ = v_a_1013_;
v___y_1103_ = v_a_1014_;
v___y_1104_ = v_a_1015_;
v___y_1105_ = v_a_1016_;
goto v___jp_1101_;
}
v___jp_1101_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1106_ = l_Lean_Expr_getForallBinderNames(v_expr_1099_);
v___x_1107_ = l_Lean_Expr_getForallBinderNames(v_expr_1057_);
v___x_1108_ = l_List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0(v___x_1106_, v___x_1107_);
if (lean_obj_tag(v___x_1108_) == 1)
{
lean_object* v_val_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; uint8_t v___x_1112_; 
v_val_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_val_1109_);
lean_dec_ref(v___x_1108_);
v___x_1110_ = l_List_lengthTR___redArg(v_val_1109_);
v___x_1111_ = lean_unsigned_to_nat(0u);
v___x_1112_ = lean_nat_dec_eq(v___x_1110_, v___x_1111_);
lean_dec(v___x_1110_);
if (v___x_1112_ == 0)
{
v___y_1060_ = v_val_1109_;
v___y_1061_ = v___y_1102_;
v___y_1062_ = v___y_1103_;
v___y_1063_ = v___y_1104_;
v___y_1064_ = v___y_1105_;
goto v___jp_1059_;
}
else
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1, &l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1);
v___x_1114_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_1113_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_dec_ref(v___x_1114_);
v___y_1060_ = v_val_1109_;
v___y_1061_ = v___y_1102_;
v___y_1062_ = v___y_1103_;
v___y_1063_ = v___y_1104_;
v___y_1064_ = v___y_1105_;
goto v___jp_1059_;
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
lean_dec(v_val_1109_);
lean_dec_ref(v_after_1012_);
lean_dec_ref(v_before_1011_);
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1114_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1114_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
}
else
{
uint8_t v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
lean_dec(v___x_1108_);
v___x_1123_ = 0;
v___x_1124_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1011_, v_after_1012_, v___x_1123_);
v___x_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
return v___x_1125_;
}
}
}
else
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_dec_ref(v_after_1012_);
lean_dec_ref(v_before_1011_);
v___x_1184_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___x_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
return v___x_1185_;
}
v___jp_1018_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = lean_unsigned_to_nat(0u);
v___x_1026_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v___y_1019_, v_before_1011_, v___x_1025_, v_a_1024_);
lean_dec(v___y_1019_);
return v___x_1026_;
}
v___jp_1027_:
{
if (v___y_1035_ == 0)
{
lean_object* v___x_1036_; 
lean_dec_ref(v___y_1034_);
v___x_1036_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1033_, v___y_1029_, v___y_1032_);
lean_dec_ref(v___y_1033_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v___x_1037_; 
lean_dec_ref(v___x_1036_);
v___x_1037_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___y_1019_ = v___y_1028_;
v___y_1020_ = v___y_1029_;
v___y_1021_ = v___y_1030_;
v___y_1022_ = v___y_1031_;
v___y_1023_ = v___y_1032_;
v_a_1024_ = v___x_1037_;
goto v___jp_1018_;
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec(v___y_1028_);
lean_dec_ref(v_before_1011_);
v_a_1038_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1036_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1036_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
else
{
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1028_);
lean_dec_ref(v_before_1011_);
return v___y_1034_;
}
}
v___jp_1046_:
{
uint8_t v___x_1055_; 
v___x_1055_ = l_Lean_Exception_isInterrupt(v_a_1054_);
if (v___x_1055_ == 0)
{
uint8_t v___x_1056_; 
v___x_1056_ = l_Lean_Exception_isRuntime(v_a_1054_);
v___y_1028_ = v___y_1047_;
v___y_1029_ = v___y_1048_;
v___y_1030_ = v___y_1049_;
v___y_1031_ = v___y_1050_;
v___y_1032_ = v___y_1052_;
v___y_1033_ = v___y_1051_;
v___y_1034_ = v___y_1053_;
v___y_1035_ = v___x_1056_;
goto v___jp_1027_;
}
else
{
lean_dec_ref(v_a_1054_);
v___y_1028_ = v___y_1047_;
v___y_1029_ = v___y_1048_;
v___y_1030_ = v___y_1049_;
v___y_1031_ = v___y_1050_;
v___y_1032_ = v___y_1052_;
v___y_1033_ = v___y_1051_;
v___y_1034_ = v___y_1053_;
v___y_1035_ = v___x_1055_;
goto v___jp_1027_;
}
}
v___jp_1059_:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_Meta_saveState___redArg(v___y_1062_, v___y_1064_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_a_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_a_1066_);
lean_dec_ref(v___x_1065_);
v___x_1067_ = l_List_lengthTR___redArg(v___y_1060_);
v___x_1068_ = lean_box(0);
v___x_1069_ = l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(v___y_1060_, v___x_1068_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v_body_u2080_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
lean_dec_ref(v___x_1069_);
lean_inc_n(v___x_1067_, 2);
v_body_u2080_1071_ = l_Lean_Expr_getForallBodyMaxDepth(v___x_1067_, v_expr_1057_);
v___x_1072_ = lean_array_mk(v_a_1070_);
v___x_1073_ = lean_expr_instantiate_rev(v_body_u2080_1071_, v___x_1072_);
lean_dec_ref(v___x_1072_);
lean_dec_ref(v_body_u2080_1071_);
lean_inc(v_pos_1058_);
v___x_1074_ = l_Lean_SubExpr_Pos_pushNthBindingBody(v___x_1067_, v_pos_1058_);
v___x_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1075_, v_after_1012_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; 
lean_dec(v_a_1066_);
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1077_);
lean_dec_ref(v___x_1076_);
v___y_1019_ = v___x_1067_;
v___y_1020_ = v___y_1062_;
v___y_1021_ = v___y_1061_;
v___y_1022_ = v___y_1063_;
v___y_1023_ = v___y_1064_;
v_a_1024_ = v_a_1077_;
goto v___jp_1018_;
}
else
{
lean_object* v_a_1078_; 
v_a_1078_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1078_);
v___y_1047_ = v___x_1067_;
v___y_1048_ = v___y_1062_;
v___y_1049_ = v___y_1061_;
v___y_1050_ = v___y_1063_;
v___y_1051_ = v_a_1066_;
v___y_1052_ = v___y_1064_;
v___y_1053_ = v___x_1076_;
v_a_1054_ = v_a_1078_;
goto v___jp_1046_;
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_dec_ref(v_after_1012_);
v_a_1079_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1069_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1069_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
lean_inc(v_a_1079_);
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
v___y_1047_ = v___x_1067_;
v___y_1048_ = v___y_1062_;
v___y_1049_ = v___y_1061_;
v___y_1050_ = v___y_1063_;
v___y_1051_ = v_a_1066_;
v___y_1052_ = v___y_1064_;
v___y_1053_ = v___x_1084_;
v_a_1054_ = v_a_1079_;
goto v___jp_1046_;
}
}
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec(v___y_1060_);
lean_dec_ref(v_after_1012_);
lean_dec_ref(v_before_1011_);
v_a_1087_ = lean_ctor_get(v___x_1065_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1065_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1065_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(lean_object* v_before_1186_, lean_object* v_after_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_){
_start:
{
lean_object* v_expr_1209_; lean_object* v_pos_1210_; lean_object* v_expr_1211_; lean_object* v_pos_1212_; lean_object* v_e_u2081_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; uint8_t v___x_1221_; 
v_expr_1209_ = lean_ctor_get(v_before_1186_, 0);
v_pos_1210_ = lean_ctor_get(v_before_1186_, 1);
v_expr_1211_ = lean_ctor_get(v_after_1187_, 0);
v_pos_1212_ = lean_ctor_get(v_after_1187_, 1);
v___x_1221_ = lean_expr_eqv(v_expr_1209_, v_expr_1211_);
if (v___x_1221_ == 0)
{
switch(lean_obj_tag(v_expr_1209_))
{
case 10:
{
lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1230_; 
lean_inc_ref(v_expr_1209_);
lean_inc(v_pos_1210_);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_before_1186_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; lean_object* v_unused_1232_; 
v_unused_1231_ = lean_ctor_get(v_before_1186_, 1);
lean_dec(v_unused_1231_);
v_unused_1232_ = lean_ctor_get(v_before_1186_, 0);
lean_dec(v_unused_1232_);
v___x_1223_ = v_before_1186_;
v_isShared_1224_ = v_isSharedCheck_1230_;
goto v_resetjp_1222_;
}
else
{
lean_dec(v_before_1186_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1230_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v_expr_1225_; lean_object* v___x_1227_; 
v_expr_1225_ = lean_ctor_get(v_expr_1209_, 1);
lean_inc_ref(v_expr_1225_);
lean_dec_ref(v_expr_1209_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v_expr_1225_);
v___x_1227_ = v___x_1223_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_expr_1225_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_pos_1210_);
v___x_1227_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
v_before_1186_ = v___x_1227_;
goto _start;
}
}
}
case 5:
{
switch(lean_obj_tag(v_expr_1211_))
{
case 10:
{
lean_object* v_expr_1233_; 
lean_inc_ref(v_expr_1211_);
lean_inc(v_pos_1212_);
lean_dec_ref(v_after_1187_);
v_expr_1233_ = lean_ctor_get(v_expr_1211_, 1);
lean_inc_ref(v_expr_1233_);
lean_dec_ref(v_expr_1211_);
v_e_u2081_1214_ = v_expr_1233_;
v___y_1215_ = v_a_1188_;
v___y_1216_ = v_a_1189_;
v___y_1217_ = v_a_1190_;
v___y_1218_ = v_a_1191_;
goto v___jp_1213_;
}
case 5:
{
lean_object* v_dummy_1234_; lean_object* v_nargs_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v_fst_1240_; lean_object* v_snd_1241_; lean_object* v_nargs_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v_fst_1246_; lean_object* v_snd_1247_; uint8_t v___x_1248_; 
v_dummy_1234_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0, &l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0);
v_nargs_1235_ = l_Lean_Expr_getAppNumArgs(v_expr_1211_);
lean_inc(v_nargs_1235_);
v___x_1236_ = lean_mk_array(v_nargs_1235_, v_dummy_1234_);
v___x_1237_ = lean_unsigned_to_nat(1u);
v___x_1238_ = lean_nat_sub(v_nargs_1235_, v___x_1237_);
lean_dec(v_nargs_1235_);
lean_inc_ref(v_expr_1211_);
v___x_1239_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(v_expr_1211_, v___x_1236_, v___x_1238_);
v_fst_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_fst_1240_);
v_snd_1241_ = lean_ctor_get(v___x_1239_, 1);
lean_inc(v_snd_1241_);
lean_dec_ref(v___x_1239_);
v_nargs_1242_ = l_Lean_Expr_getAppNumArgs(v_expr_1209_);
lean_inc(v_nargs_1242_);
v___x_1243_ = lean_mk_array(v_nargs_1242_, v_dummy_1234_);
v___x_1244_ = lean_nat_sub(v_nargs_1242_, v___x_1237_);
lean_dec(v_nargs_1242_);
lean_inc_ref(v_expr_1209_);
v___x_1245_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(v_expr_1209_, v___x_1243_, v___x_1244_);
v_fst_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_fst_1246_);
v_snd_1247_ = lean_ctor_get(v___x_1245_, 1);
lean_inc(v_snd_1247_);
lean_dec_ref(v___x_1245_);
v___x_1248_ = lean_expr_eqv(v_fst_1240_, v_fst_1246_);
lean_dec(v_fst_1246_);
lean_dec(v_fst_1240_);
if (v___x_1248_ == 0)
{
lean_dec(v_snd_1247_);
lean_dec(v_snd_1241_);
goto v___jp_1201_;
}
else
{
if (v___x_1221_ == 0)
{
lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___x_1249_ = lean_array_get_size(v_snd_1241_);
v___x_1250_ = lean_array_get_size(v_snd_1247_);
v___x_1251_ = lean_nat_dec_eq(v___x_1249_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_dec(v_snd_1247_);
lean_dec(v_snd_1241_);
goto v___jp_1201_;
}
else
{
lean_object* v_args_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v_args_1252_ = l_Array_zip___redArg(v_snd_1241_, v_snd_1247_);
lean_dec(v_snd_1247_);
v___x_1253_ = lean_array_get_size(v_args_1252_);
v___x_1254_ = lean_unsigned_to_nat(0u);
v___x_1255_ = lean_mk_empty_array_with_capacity(v___x_1253_);
v___x_1256_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_1241_, v_before_1186_, v_after_1187_, v_args_1252_, v___x_1253_, v___x_1254_, v___x_1255_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
lean_dec_ref(v_args_1252_);
lean_dec_ref(v_after_1187_);
lean_dec_ref(v_before_1186_);
lean_dec(v_snd_1241_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1283_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1259_ = v___x_1256_;
v_isShared_1260_ = v_isSharedCheck_1283_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1256_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1283_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v___x_1261_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___x_1262_ = lean_array_get_size(v_a_1257_);
v___x_1263_ = lean_nat_dec_lt(v___x_1254_, v___x_1262_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1265_; 
lean_dec(v_a_1257_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1261_);
v___x_1265_ = v___x_1259_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1261_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
else
{
uint8_t v___x_1267_; 
v___x_1267_ = lean_nat_dec_le(v___x_1262_, v___x_1262_);
if (v___x_1267_ == 0)
{
if (v___x_1263_ == 0)
{
lean_object* v___x_1269_; 
lean_dec(v_a_1257_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1261_);
v___x_1269_ = v___x_1259_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1261_);
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
size_t v___x_1271_; size_t v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1275_; 
v___x_1271_ = ((size_t)0ULL);
v___x_1272_ = lean_usize_of_nat(v___x_1262_);
v___x_1273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_a_1257_, v___x_1271_, v___x_1272_, v___x_1261_);
lean_dec(v_a_1257_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1273_);
v___x_1275_ = v___x_1259_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
else
{
size_t v___x_1277_; size_t v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1281_; 
v___x_1277_ = ((size_t)0ULL);
v___x_1278_ = lean_usize_of_nat(v___x_1262_);
v___x_1279_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_a_1257_, v___x_1277_, v___x_1278_, v___x_1261_);
lean_dec(v_a_1257_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1279_);
v___x_1281_ = v___x_1259_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1279_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
v_a_1284_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1256_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1256_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
else
{
lean_dec(v_snd_1247_);
lean_dec(v_snd_1241_);
goto v___jp_1201_;
}
}
}
default: 
{
goto v___jp_1205_;
}
}
}
case 7:
{
if (lean_obj_tag(v_expr_1211_) == 10)
{
lean_object* v_expr_1292_; 
lean_inc_ref(v_expr_1211_);
lean_inc(v_pos_1212_);
lean_dec_ref(v_after_1187_);
v_expr_1292_ = lean_ctor_get(v_expr_1211_, 1);
lean_inc_ref(v_expr_1292_);
lean_dec_ref(v_expr_1211_);
v_e_u2081_1214_ = v_expr_1292_;
v___y_1215_ = v_a_1188_;
v___y_1216_ = v_a_1189_;
v___y_1217_ = v_a_1190_;
v___y_1218_ = v_a_1191_;
goto v___jp_1213_;
}
else
{
lean_object* v___x_1293_; 
v___x_1293_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(v_before_1186_, v_after_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
return v___x_1293_;
}
}
case 6:
{
switch(lean_obj_tag(v_expr_1211_))
{
case 10:
{
lean_object* v_expr_1294_; 
lean_inc_ref(v_expr_1211_);
lean_inc(v_pos_1212_);
lean_dec_ref(v_after_1187_);
v_expr_1294_ = lean_ctor_get(v_expr_1211_, 1);
lean_inc_ref(v_expr_1294_);
lean_dec_ref(v_expr_1211_);
v_e_u2081_1214_ = v_expr_1294_;
v___y_1215_ = v_a_1188_;
v___y_1216_ = v_a_1189_;
v___y_1217_ = v_a_1190_;
v___y_1218_ = v_a_1191_;
goto v___jp_1213_;
}
case 6:
{
lean_object* v_binderName_1295_; lean_object* v_binderType_1296_; lean_object* v_body_1297_; uint8_t v_binderInfo_1298_; lean_object* v_binderName_1299_; lean_object* v_binderType_1300_; lean_object* v_body_1301_; uint8_t v_binderInfo_1302_; uint8_t v___x_1303_; 
v_binderName_1295_ = lean_ctor_get(v_expr_1209_, 0);
v_binderType_1296_ = lean_ctor_get(v_expr_1209_, 1);
v_body_1297_ = lean_ctor_get(v_expr_1209_, 2);
v_binderInfo_1298_ = lean_ctor_get_uint8(v_expr_1209_, sizeof(void*)*3 + 8);
v_binderName_1299_ = lean_ctor_get(v_expr_1211_, 0);
v_binderType_1300_ = lean_ctor_get(v_expr_1211_, 1);
v_body_1301_ = lean_ctor_get(v_expr_1211_, 2);
v_binderInfo_1302_ = lean_ctor_get_uint8(v_expr_1211_, sizeof(void*)*3 + 8);
v___x_1303_ = lean_name_eq(v_binderName_1295_, v_binderName_1299_);
if (v___x_1303_ == 0)
{
goto v___jp_1197_;
}
else
{
if (v___x_1221_ == 0)
{
uint8_t v___x_1304_; 
v___x_1304_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1298_, v_binderInfo_1302_);
if (v___x_1304_ == 0)
{
goto v___jp_1197_;
}
else
{
lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1354_; 
lean_inc_ref(v_body_1301_);
lean_inc_ref(v_binderType_1300_);
lean_inc_ref(v_body_1297_);
lean_inc_ref(v_binderType_1296_);
lean_inc(v_pos_1212_);
lean_inc(v_pos_1210_);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_before_1186_);
if (v_isSharedCheck_1354_ == 0)
{
lean_object* v_unused_1355_; lean_object* v_unused_1356_; 
v_unused_1355_ = lean_ctor_get(v_before_1186_, 1);
lean_dec(v_unused_1355_);
v_unused_1356_ = lean_ctor_get(v_before_1186_, 0);
lean_dec(v_unused_1356_);
v___x_1306_ = v_before_1186_;
v_isShared_1307_ = v_isSharedCheck_1354_;
goto v_resetjp_1305_;
}
else
{
lean_dec(v_before_1186_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1354_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1351_; 
v_isSharedCheck_1351_ = !lean_is_exclusive(v_after_1187_);
if (v_isSharedCheck_1351_ == 0)
{
lean_object* v_unused_1352_; lean_object* v_unused_1353_; 
v_unused_1352_ = lean_ctor_get(v_after_1187_, 1);
lean_dec(v_unused_1352_);
v_unused_1353_ = lean_ctor_get(v_after_1187_, 0);
lean_dec(v_unused_1353_);
v___x_1309_ = v_after_1187_;
v_isShared_1310_ = v_isSharedCheck_1351_;
goto v_resetjp_1308_;
}
else
{
lean_dec(v_after_1187_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1351_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1311_; lean_object* v___x_1313_; 
v___x_1311_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1210_);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 1, v___x_1311_);
lean_ctor_set(v___x_1309_, 0, v_binderType_1296_);
v___x_1313_ = v___x_1309_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_binderType_1296_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1314_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1212_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 1, v___x_1314_);
lean_ctor_set(v___x_1306_, 0, v_binderType_1300_);
v___x_1316_ = v___x_1306_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_binderType_1300_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1317_; 
v___x_1317_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1313_, v___x_1316_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1348_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1320_ = v___x_1317_;
v_isShared_1321_ = v_isSharedCheck_1348_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1317_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1348_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
uint8_t v___x_1322_; 
v___x_1322_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_a_1318_);
if (v___x_1322_ == 0)
{
lean_object* v_changesBefore_1323_; lean_object* v_changesAfter_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; lean_object* v___x_1328_; lean_object* v_changesBefore_1329_; lean_object* v_changesAfter_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1342_; 
lean_dec_ref(v_body_1301_);
lean_dec_ref(v_body_1297_);
v_changesBefore_1323_ = lean_ctor_get(v_a_1318_, 0);
lean_inc(v_changesBefore_1323_);
v_changesAfter_1324_ = lean_ctor_get(v_a_1318_, 1);
lean_inc(v_changesAfter_1324_);
lean_dec(v_a_1318_);
v___x_1325_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1210_);
lean_dec(v_pos_1210_);
v___x_1326_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1212_);
lean_dec(v_pos_1212_);
v___x_1327_ = 0;
v___x_1328_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v___x_1325_, v___x_1326_, v___x_1327_);
v_changesBefore_1329_ = lean_ctor_get(v___x_1328_, 0);
v_changesAfter_1330_ = lean_ctor_get(v___x_1328_, 1);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1332_ = v___x_1328_;
v_isShared_1333_ = v_isSharedCheck_1342_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_changesAfter_1330_);
lean_inc(v_changesBefore_1329_);
lean_dec(v___x_1328_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1342_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1334_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesBefore_1323_, v_changesBefore_1329_);
v___x_1335_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesAfter_1324_, v_changesAfter_1330_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 1, v___x_1335_);
lean_ctor_set(v___x_1332_, 0, v___x_1334_);
v___x_1337_ = v___x_1332_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1334_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v___x_1339_; 
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v___x_1337_);
v___x_1339_ = v___x_1320_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
else
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
lean_del_object(v___x_1320_);
lean_dec(v_a_1318_);
v___x_1343_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1210_);
lean_dec(v_pos_1210_);
v___x_1344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1344_, 0, v_body_1297_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
v___x_1345_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1212_);
lean_dec(v_pos_1212_);
v___x_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1346_, 0, v_body_1301_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
v_before_1186_ = v___x_1344_;
v_after_1187_ = v___x_1346_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_body_1301_);
lean_dec_ref(v_body_1297_);
lean_dec(v_pos_1212_);
lean_dec(v_pos_1210_);
return v___x_1317_;
}
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
goto v___jp_1205_;
}
}
}
case 11:
{
switch(lean_obj_tag(v_expr_1211_))
{
case 10:
{
lean_object* v_expr_1357_; 
lean_inc_ref(v_expr_1211_);
lean_inc(v_pos_1212_);
lean_dec_ref(v_after_1187_);
v_expr_1357_ = lean_ctor_get(v_expr_1211_, 1);
lean_inc_ref(v_expr_1357_);
lean_dec_ref(v_expr_1211_);
v_e_u2081_1214_ = v_expr_1357_;
v___y_1215_ = v_a_1188_;
v___y_1216_ = v_a_1189_;
v___y_1217_ = v_a_1190_;
v___y_1218_ = v_a_1191_;
goto v___jp_1213_;
}
case 11:
{
lean_object* v_typeName_1358_; lean_object* v_idx_1359_; lean_object* v_struct_1360_; lean_object* v_typeName_1361_; lean_object* v_idx_1362_; lean_object* v_struct_1363_; uint8_t v___x_1364_; 
v_typeName_1358_ = lean_ctor_get(v_expr_1209_, 0);
v_idx_1359_ = lean_ctor_get(v_expr_1209_, 1);
v_struct_1360_ = lean_ctor_get(v_expr_1209_, 2);
v_typeName_1361_ = lean_ctor_get(v_expr_1211_, 0);
v_idx_1362_ = lean_ctor_get(v_expr_1211_, 1);
v_struct_1363_ = lean_ctor_get(v_expr_1211_, 2);
v___x_1364_ = lean_name_eq(v_typeName_1358_, v_typeName_1361_);
if (v___x_1364_ == 0)
{
goto v___jp_1193_;
}
else
{
if (v___x_1221_ == 0)
{
uint8_t v___x_1365_; 
v___x_1365_ = lean_nat_dec_eq(v_idx_1359_, v_idx_1362_);
if (v___x_1365_ == 0)
{
goto v___jp_1193_;
}
else
{
lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1384_; 
lean_inc_ref(v_struct_1363_);
lean_inc_ref(v_struct_1360_);
lean_inc(v_pos_1212_);
lean_inc(v_pos_1210_);
v_isSharedCheck_1384_ = !lean_is_exclusive(v_before_1186_);
if (v_isSharedCheck_1384_ == 0)
{
lean_object* v_unused_1385_; lean_object* v_unused_1386_; 
v_unused_1385_ = lean_ctor_get(v_before_1186_, 1);
lean_dec(v_unused_1385_);
v_unused_1386_ = lean_ctor_get(v_before_1186_, 0);
lean_dec(v_unused_1386_);
v___x_1367_ = v_before_1186_;
v_isShared_1368_ = v_isSharedCheck_1384_;
goto v_resetjp_1366_;
}
else
{
lean_dec(v_before_1186_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1384_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1381_; 
v_isSharedCheck_1381_ = !lean_is_exclusive(v_after_1187_);
if (v_isSharedCheck_1381_ == 0)
{
lean_object* v_unused_1382_; lean_object* v_unused_1383_; 
v_unused_1382_ = lean_ctor_get(v_after_1187_, 1);
lean_dec(v_unused_1382_);
v_unused_1383_ = lean_ctor_get(v_after_1187_, 0);
lean_dec(v_unused_1383_);
v___x_1370_ = v_after_1187_;
v_isShared_1371_ = v_isSharedCheck_1381_;
goto v_resetjp_1369_;
}
else
{
lean_dec(v_after_1187_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1381_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v___x_1374_; 
v___x_1372_ = l_Lean_SubExpr_Pos_pushProj(v_pos_1210_);
lean_dec(v_pos_1210_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 1, v___x_1372_);
lean_ctor_set(v___x_1370_, 0, v_struct_1360_);
v___x_1374_ = v___x_1370_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_struct_1360_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1375_; lean_object* v___x_1377_; 
v___x_1375_ = l_Lean_SubExpr_Pos_pushProj(v_pos_1212_);
lean_dec(v_pos_1212_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 1, v___x_1375_);
lean_ctor_set(v___x_1367_, 0, v_struct_1363_);
v___x_1377_ = v___x_1367_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_struct_1363_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
v_before_1186_ = v___x_1374_;
v_after_1187_ = v___x_1377_;
goto _start;
}
}
}
}
}
}
else
{
goto v___jp_1193_;
}
}
}
default: 
{
goto v___jp_1205_;
}
}
}
default: 
{
if (lean_obj_tag(v_expr_1211_) == 10)
{
lean_object* v_expr_1387_; 
lean_inc_ref(v_expr_1211_);
lean_inc(v_pos_1212_);
lean_dec_ref(v_after_1187_);
v_expr_1387_ = lean_ctor_get(v_expr_1211_, 1);
lean_inc_ref(v_expr_1387_);
lean_dec_ref(v_expr_1211_);
v_e_u2081_1214_ = v_expr_1387_;
v___y_1215_ = v_a_1188_;
v___y_1216_ = v_a_1189_;
v___y_1217_ = v_a_1190_;
v___y_1218_ = v_a_1191_;
goto v___jp_1213_;
}
else
{
goto v___jp_1205_;
}
}
}
}
else
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_dec_ref(v_after_1187_);
lean_dec_ref(v_before_1186_);
v___x_1388_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
v___jp_1193_:
{
uint8_t v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1194_ = 0;
v___x_1195_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1186_, v_after_1187_, v___x_1194_);
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
return v___x_1196_;
}
v___jp_1197_:
{
uint8_t v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1198_ = 0;
v___x_1199_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1186_, v_after_1187_, v___x_1198_);
v___x_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
return v___x_1200_;
}
v___jp_1201_:
{
uint8_t v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1202_ = 0;
v___x_1203_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1186_, v_after_1187_, v___x_1202_);
v___x_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
return v___x_1204_;
}
v___jp_1205_:
{
uint8_t v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = 0;
v___x_1207_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1186_, v_after_1187_, v___x_1206_);
v___x_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
return v___x_1208_;
}
v___jp_1213_:
{
lean_object* v___x_1219_; 
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v_e_u2081_1214_);
lean_ctor_set(v___x_1219_, 1, v_pos_1212_);
v_after_1187_ = v___x_1219_;
v_a_1188_ = v___y_1215_;
v_a_1189_ = v___y_1216_;
v_a_1190_ = v___y_1217_;
v_a_1191_ = v___y_1218_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0(lean_object* v_body_1390_, lean_object* v_pos_1391_, lean_object* v_body_1392_, lean_object* v_pos_1393_, lean_object* v_x_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1400_ = lean_expr_instantiate1(v_body_1390_, v_x_1394_);
v___x_1401_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1391_);
v___x_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1400_);
lean_ctor_set(v___x_1402_, 1, v___x_1401_);
v___x_1403_ = lean_expr_instantiate1(v_body_1392_, v_x_1394_);
v___x_1404_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1393_);
v___x_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1403_);
lean_ctor_set(v___x_1405_, 1, v___x_1404_);
v___x_1406_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1402_, v___x_1405_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg___boxed(lean_object* v_snd_1407_, lean_object* v_before_1408_, lean_object* v_after_1409_, lean_object* v_as_1410_, lean_object* v_i_1411_, lean_object* v_j_1412_, lean_object* v_bs_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_1407_, v_before_1408_, v_after_1409_, v_as_1410_, v_i_1411_, v_j_1412_, v_bs_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec_ref(v_as_1410_);
lean_dec_ref(v_after_1409_);
lean_dec_ref(v_before_1408_);
lean_dec_ref(v_snd_1407_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___boxed(lean_object* v_before_1420_, lean_object* v_after_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(v_before_1420_, v_after_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_);
lean_dec(v_a_1425_);
lean_dec_ref(v_a_1424_);
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___boxed(lean_object* v_before_1428_, lean_object* v_after_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v_before_1428_, v_after_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_);
lean_dec(v_a_1433_);
lean_dec_ref(v_a_1432_);
lean_dec(v_a_1431_);
lean_dec_ref(v_a_1430_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1(lean_object* v_upperBound_1436_, lean_object* v_before_1437_, lean_object* v_inst_1438_, lean_object* v_R_1439_, lean_object* v_a_1440_, lean_object* v_b_1441_, lean_object* v_c_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v_upperBound_1436_, v_before_1437_, v_a_1440_, v_b_1441_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___boxed(lean_object* v_upperBound_1449_, lean_object* v_before_1450_, lean_object* v_inst_1451_, lean_object* v_R_1452_, lean_object* v_a_1453_, lean_object* v_b_1454_, lean_object* v_c_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1(v_upperBound_1449_, v_before_1450_, v_inst_1451_, v_R_1452_, v_a_1453_, v_b_1454_, v_c_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v_upperBound_1449_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3(lean_object* v_00_u03b1_1462_, lean_object* v_msg_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v___x_1469_; 
v___x_1469_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v_msg_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___boxed(lean_object* v_00_u03b1_1470_, lean_object* v_msg_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3(v_00_u03b1_1470_, v_msg_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4(uint8_t v_b_u2082_1478_, lean_object* v_k_1479_, lean_object* v_t_1480_, lean_object* v_hl_1481_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_1478_, v_k_1479_, v_t_1480_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___boxed(lean_object* v_b_u2082_1483_, lean_object* v_k_1484_, lean_object* v_t_1485_, lean_object* v_hl_1486_){
_start:
{
uint8_t v_b_u2082_boxed_1487_; lean_object* v_res_1488_; 
v_b_u2082_boxed_1487_ = lean_unbox(v_b_u2082_1483_);
v_res_1488_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4(v_b_u2082_boxed_1487_, v_k_1484_, v_t_1485_, v_hl_1486_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5(lean_object* v_init_1489_, lean_object* v_t_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_init_1489_, v_t_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9(lean_object* v_snd_1492_, lean_object* v_before_1493_, lean_object* v_after_1494_, lean_object* v_as_1495_, lean_object* v_i_1496_, lean_object* v_j_1497_, lean_object* v_inv_1498_, lean_object* v_bs_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_1492_, v_before_1493_, v_after_1494_, v_as_1495_, v_i_1496_, v_j_1497_, v_bs_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___boxed(lean_object* v_snd_1506_, lean_object* v_before_1507_, lean_object* v_after_1508_, lean_object* v_as_1509_, lean_object* v_i_1510_, lean_object* v_j_1511_, lean_object* v_inv_1512_, lean_object* v_bs_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9(v_snd_1506_, v_before_1507_, v_after_1508_, v_as_1509_, v_i_1510_, v_j_1511_, v_inv_1512_, v_bs_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec_ref(v_as_1509_);
lean_dec_ref(v_after_1508_);
lean_dec_ref(v_before_1507_);
lean_dec_ref(v_snd_1506_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(lean_object* v_e_u2080_1520_, lean_object* v_e_u2081_1521_, uint8_t v_useAfter_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v___x_1528_; lean_object* v_s_u2080_1529_; lean_object* v_s_u2081_1530_; 
v___x_1528_ = l_Lean_SubExpr_Pos_root;
v_s_u2080_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_u2080_1529_, 0, v_e_u2080_1520_);
lean_ctor_set(v_s_u2080_1529_, 1, v___x_1528_);
v_s_u2081_1530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_u2081_1530_, 0, v_e_u2081_1521_);
lean_ctor_set(v_s_u2081_1530_, 1, v___x_1528_);
if (v_useAfter_1522_ == 0)
{
lean_object* v___x_1531_; 
v___x_1531_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v_s_u2081_1530_, v_s_u2080_1529_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
return v___x_1531_;
}
else
{
lean_object* v___x_1532_; 
v___x_1532_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v_s_u2080_1529_, v_s_u2081_1530_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
return v___x_1532_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff___boxed(lean_object* v_e_u2080_1533_, lean_object* v_e_u2081_1534_, lean_object* v_useAfter_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_){
_start:
{
uint8_t v_useAfter_boxed_1541_; lean_object* v_res_1542_; 
v_useAfter_boxed_1541_ = lean_unbox(v_useAfter_1535_);
v_res_1542_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(v_e_u2080_1533_, v_e_u2081_1534_, v_useAfter_boxed_1541_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
lean_dec(v_a_1539_);
lean_dec_ref(v_a_1538_);
lean_dec(v_a_1537_);
lean_dec_ref(v_a_1536_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0(uint8_t v_useAfter_1543_, lean_object* v_info_1544_, uint8_t v_d_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
uint8_t v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1551_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag(v_useAfter_1543_, v_d_1545_);
v___x_1552_ = l_Lean_Widget_SubexprInfo_withDiffTag(v___x_1551_, v_info_1544_);
v___x_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0___boxed(lean_object* v_useAfter_1554_, lean_object* v_info_1555_, lean_object* v_d_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
uint8_t v_useAfter_boxed_1562_; uint8_t v_d_boxed_1563_; lean_object* v_res_1564_; 
v_useAfter_boxed_1562_ = lean_unbox(v_useAfter_1554_);
v_d_boxed_1563_ = lean_unbox(v_d_1556_);
v_res_1564_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0(v_useAfter_boxed_1562_, v_info_1555_, v_d_boxed_1563_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(lean_object* v_f_1565_, lean_object* v_x_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
switch(lean_obj_tag(v_x_1566_))
{
case 0:
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1580_; 
lean_dec_ref(v_f_1565_);
v_a_1572_ = lean_ctor_get(v_x_1566_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_x_1566_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1574_ = v_x_1566_;
v_isShared_1575_ = v_isSharedCheck_1580_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v_x_1566_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1580_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
lean_object* v___x_1578_; 
v___x_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
return v___x_1578_;
}
}
}
case 1:
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1607_; 
v_a_1581_ = lean_ctor_get(v_x_1566_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v_x_1566_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1583_ = v_x_1566_;
v_isShared_1584_ = v_isSharedCheck_1607_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v_x_1566_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1607_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
size_t v_sz_1585_; size_t v___x_1586_; lean_object* v___x_1587_; 
v_sz_1585_ = lean_array_size(v_a_1581_);
v___x_1586_ = ((size_t)0ULL);
v___x_1587_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_1565_, v_sz_1585_, v___x_1586_, v_a_1581_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1598_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1590_ = v___x_1587_;
v_isShared_1591_ = v_isSharedCheck_1598_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1587_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1598_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 0, v_a_1588_);
v___x_1593_ = v___x_1583_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
lean_object* v___x_1595_; 
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v___x_1593_);
v___x_1595_ = v___x_1590_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1593_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_del_object(v___x_1583_);
v_a_1599_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1587_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1587_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
}
default: 
{
lean_object* v_a_1608_; lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1635_; 
v_a_1608_ = lean_ctor_get(v_x_1566_, 0);
v_a_1609_ = lean_ctor_get(v_x_1566_, 1);
v_isSharedCheck_1635_ = !lean_is_exclusive(v_x_1566_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1611_ = v_x_1566_;
v_isShared_1612_ = v_isSharedCheck_1635_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_inc(v_a_1608_);
lean_dec(v_x_1566_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1635_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1613_; 
lean_inc_ref(v_f_1565_);
lean_inc(v___y_1570_);
lean_inc_ref(v___y_1569_);
lean_inc(v___y_1568_);
lean_inc_ref(v___y_1567_);
v___x_1613_ = lean_apply_6(v_f_1565_, v_a_1608_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, lean_box(0));
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v___x_1615_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref(v___x_1613_);
v___x_1615_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1565_, v_a_1609_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1626_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1618_ = v___x_1615_;
v_isShared_1619_ = v_isSharedCheck_1626_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1615_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1626_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 1, v_a_1616_);
lean_ctor_set(v___x_1611_, 0, v_a_1614_);
v___x_1621_ = v___x_1611_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1614_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
lean_object* v___x_1623_; 
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 0, v___x_1621_);
v___x_1623_ = v___x_1618_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
else
{
lean_dec(v_a_1614_);
lean_del_object(v___x_1611_);
return v___x_1615_;
}
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
lean_del_object(v___x_1611_);
lean_dec_ref(v_a_1609_);
lean_dec_ref(v_f_1565_);
v_a_1627_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1613_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1613_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(lean_object* v_f_1636_, size_t v_sz_1637_, size_t v_i_1638_, lean_object* v_bs_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
uint8_t v___x_1645_; 
v___x_1645_ = lean_usize_dec_lt(v_i_1638_, v_sz_1637_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; 
lean_dec_ref(v_f_1636_);
v___x_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1646_, 0, v_bs_1639_);
return v___x_1646_;
}
else
{
lean_object* v_v_1647_; lean_object* v___x_1648_; 
v_v_1647_ = lean_array_uget_borrowed(v_bs_1639_, v_i_1638_);
lean_inc(v_v_1647_);
lean_inc_ref(v_f_1636_);
v___x_1648_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1636_, v_v_1647_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1650_; lean_object* v_bs_x27_1651_; size_t v___x_1652_; size_t v___x_1653_; lean_object* v___x_1654_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref(v___x_1648_);
v___x_1650_ = lean_unsigned_to_nat(0u);
v_bs_x27_1651_ = lean_array_uset(v_bs_1639_, v_i_1638_, v___x_1650_);
v___x_1652_ = ((size_t)1ULL);
v___x_1653_ = lean_usize_add(v_i_1638_, v___x_1652_);
v___x_1654_ = lean_array_uset(v_bs_x27_1651_, v_i_1638_, v_a_1649_);
v_i_1638_ = v___x_1653_;
v_bs_1639_ = v___x_1654_;
goto _start;
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_dec_ref(v_bs_1639_);
lean_dec_ref(v_f_1636_);
v_a_1656_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1648_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1648_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_1664_, lean_object* v_sz_1665_, lean_object* v_i_1666_, lean_object* v_bs_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
size_t v_sz_boxed_1673_; size_t v_i_boxed_1674_; lean_object* v_res_1675_; 
v_sz_boxed_1673_ = lean_unbox_usize(v_sz_1665_);
lean_dec(v_sz_1665_);
v_i_boxed_1674_ = lean_unbox_usize(v_i_1666_);
lean_dec(v_i_1666_);
v_res_1675_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_1664_, v_sz_boxed_1673_, v_i_boxed_1674_, v_bs_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg___boxed(lean_object* v_f_1676_, lean_object* v_x_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1676_, v_x_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(lean_object* v_t_1684_, lean_object* v_k_1685_){
_start:
{
if (lean_obj_tag(v_t_1684_) == 0)
{
lean_object* v_k_1686_; lean_object* v_v_1687_; lean_object* v_l_1688_; lean_object* v_r_1689_; uint8_t v___x_1690_; 
v_k_1686_ = lean_ctor_get(v_t_1684_, 1);
v_v_1687_ = lean_ctor_get(v_t_1684_, 2);
v_l_1688_ = lean_ctor_get(v_t_1684_, 3);
v_r_1689_ = lean_ctor_get(v_t_1684_, 4);
v___x_1690_ = lean_nat_dec_lt(v_k_1685_, v_k_1686_);
if (v___x_1690_ == 0)
{
uint8_t v___x_1691_; 
v___x_1691_ = lean_nat_dec_eq(v_k_1685_, v_k_1686_);
if (v___x_1691_ == 0)
{
v_t_1684_ = v_r_1689_;
goto _start;
}
else
{
lean_object* v___x_1693_; 
lean_inc(v_v_1687_);
v___x_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1693_, 0, v_v_1687_);
return v___x_1693_;
}
}
else
{
v_t_1684_ = v_l_1688_;
goto _start;
}
}
else
{
lean_object* v___x_1695_; 
v___x_1695_ = lean_box(0);
return v___x_1695_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg___boxed(lean_object* v_t_1696_, lean_object* v_k_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_t_1696_, v_k_1697_);
lean_dec(v_k_1697_);
lean_dec(v_t_1696_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0(lean_object* v_pm_1699_, lean_object* v_merger_1700_, lean_object* v_info_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v_subexprPos_1707_; lean_object* v___x_1708_; 
v_subexprPos_1707_ = lean_ctor_get(v_info_1701_, 1);
v___x_1708_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_pm_1699_, v_subexprPos_1707_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v___x_1709_; 
lean_dec_ref(v_merger_1700_);
v___x_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1709_, 0, v_info_1701_);
return v___x_1709_;
}
else
{
lean_object* v_val_1710_; lean_object* v___x_1711_; 
v_val_1710_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_val_1710_);
lean_dec_ref(v___x_1708_);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
v___x_1711_ = lean_apply_7(v_merger_1700_, v_info_1701_, v_val_1710_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, lean_box(0));
return v___x_1711_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0___boxed(lean_object* v_pm_1712_, lean_object* v_merger_1713_, lean_object* v_info_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0(v_pm_1712_, v_merger_1713_, v_info_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v_pm_1712_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(lean_object* v_merger_1721_, lean_object* v_pm_1722_, lean_object* v_tt_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
if (lean_obj_tag(v_pm_1722_) == 0)
{
lean_object* v___f_1729_; lean_object* v___x_1730_; 
v___f_1729_ = lean_alloc_closure((void*)(l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1729_, 0, v_pm_1722_);
lean_closure_set(v___f_1729_, 1, v_merger_1721_);
v___x_1730_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v___f_1729_, v_tt_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
return v___x_1730_;
}
else
{
lean_object* v___x_1731_; 
lean_dec_ref(v_merger_1721_);
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v_tt_1723_);
return v___x_1731_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___boxed(lean_object* v_merger_1732_, lean_object* v_pm_1733_, lean_object* v_tt_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v_merger_1732_, v_pm_1733_, v_tt_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(uint8_t v_useAfter_1741_, lean_object* v_diff_1742_, lean_object* v_info_u2081_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v___x_1749_; lean_object* v___f_1750_; 
v___x_1749_ = lean_box(v_useAfter_1741_);
v___f_1750_ = lean_alloc_closure((void*)(l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1750_, 0, v___x_1749_);
if (v_useAfter_1741_ == 0)
{
lean_object* v_changesBefore_1751_; lean_object* v___x_1752_; 
v_changesBefore_1751_ = lean_ctor_get(v_diff_1742_, 0);
lean_inc(v_changesBefore_1751_);
lean_dec_ref(v_diff_1742_);
v___x_1752_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v___f_1750_, v_changesBefore_1751_, v_info_u2081_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
return v___x_1752_;
}
else
{
lean_object* v_changesAfter_1753_; lean_object* v___x_1754_; 
v_changesAfter_1753_ = lean_ctor_get(v_diff_1742_, 1);
lean_inc(v_changesAfter_1753_);
lean_dec_ref(v_diff_1742_);
v___x_1754_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v___f_1750_, v_changesAfter_1753_, v_info_u2081_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
return v___x_1754_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___boxed(lean_object* v_useAfter_1755_, lean_object* v_diff_1756_, lean_object* v_info_u2081_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_){
_start:
{
uint8_t v_useAfter_boxed_1763_; lean_object* v_res_1764_; 
v_useAfter_boxed_1763_ = lean_unbox(v_useAfter_1755_);
v_res_1764_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(v_useAfter_boxed_1763_, v_diff_1756_, v_info_u2081_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_);
lean_dec(v_a_1761_);
lean_dec_ref(v_a_1760_);
lean_dec(v_a_1759_);
lean_dec_ref(v_a_1758_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0(lean_object* v_00_u03b1_1765_, lean_object* v_merger_1766_, lean_object* v_pm_1767_, lean_object* v_tt_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v_merger_1766_, v_pm_1767_, v_tt_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___boxed(lean_object* v_00_u03b1_1775_, lean_object* v_merger_1776_, lean_object* v_pm_1777_, lean_object* v_tt_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0(v_00_u03b1_1775_, v_merger_1776_, v_pm_1777_, v_tt_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0(lean_object* v_00_u03b4_1785_, lean_object* v_t_1786_, lean_object* v_k_1787_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_t_1786_, v_k_1787_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___boxed(lean_object* v_00_u03b4_1789_, lean_object* v_t_1790_, lean_object* v_k_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0(v_00_u03b4_1789_, v_t_1790_, v_k_1791_);
lean_dec(v_k_1791_);
lean_dec(v_t_1790_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1(lean_object* v_00_u03b1_1793_, lean_object* v_00_u03b2_1794_, lean_object* v_f_1795_, lean_object* v_x_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1795_, v_x_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1803_, lean_object* v_00_u03b2_1804_, lean_object* v_f_1805_, lean_object* v_x_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1(v_00_u03b1_1803_, v_00_u03b2_1804_, v_f_1805_, v_x_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1813_, lean_object* v_00_u03b2_1814_, lean_object* v_f_1815_, size_t v_sz_1816_, size_t v_i_1817_, lean_object* v_bs_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_1815_, v_sz_1816_, v_i_1817_, v_bs_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1825_, lean_object* v_00_u03b2_1826_, lean_object* v_f_1827_, lean_object* v_sz_1828_, lean_object* v_i_1829_, lean_object* v_bs_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
size_t v_sz_boxed_1836_; size_t v_i_boxed_1837_; lean_object* v_res_1838_; 
v_sz_boxed_1836_ = lean_unbox_usize(v_sz_1828_);
lean_dec(v_sz_1828_);
v_i_boxed_1837_ = lean_unbox_usize(v_i_1829_);
lean_dec(v_i_1829_);
v_res_1838_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2(v_00_u03b1_1825_, v_00_u03b2_1826_, v_f_1827_, v_sz_boxed_1836_, v_i_boxed_1837_, v_bs_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
return v_res_1838_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1(void){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__0));
v___x_1841_ = l_Lean_stringToMessageData(v___x_1840_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(uint8_t v_useAfter_1842_, lean_object* v_t_u2080_1843_, lean_object* v_h_u2081_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_){
_start:
{
lean_object* v_names_1850_; lean_object* v_fvarIds_1851_; lean_object* v_type_1852_; lean_object* v_val_x3f_1853_; lean_object* v_isInstance_x3f_1854_; lean_object* v_isType_x3f_1855_; lean_object* v_isInserted_x3f_1856_; lean_object* v_isRemoved_x3f_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1908_; 
v_names_1850_ = lean_ctor_get(v_h_u2081_1844_, 0);
v_fvarIds_1851_ = lean_ctor_get(v_h_u2081_1844_, 1);
v_type_1852_ = lean_ctor_get(v_h_u2081_1844_, 2);
v_val_x3f_1853_ = lean_ctor_get(v_h_u2081_1844_, 3);
v_isInstance_x3f_1854_ = lean_ctor_get(v_h_u2081_1844_, 4);
v_isType_x3f_1855_ = lean_ctor_get(v_h_u2081_1844_, 5);
v_isInserted_x3f_1856_ = lean_ctor_get(v_h_u2081_1844_, 6);
v_isRemoved_x3f_1857_ = lean_ctor_get(v_h_u2081_1844_, 7);
v_isSharedCheck_1908_ = !lean_is_exclusive(v_h_u2081_1844_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1859_ = v_h_u2081_1844_;
v_isShared_1860_ = v_isSharedCheck_1908_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_isRemoved_x3f_1857_);
lean_inc(v_isInserted_x3f_1856_);
lean_inc(v_isType_x3f_1855_);
lean_inc(v_isInstance_x3f_1854_);
lean_inc(v_val_x3f_1853_);
lean_inc(v_type_1852_);
lean_inc(v_fvarIds_1851_);
lean_inc(v_names_1850_);
lean_dec(v_h_u2081_1844_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1908_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; uint8_t v___x_1863_; 
v___x_1861_ = lean_unsigned_to_nat(0u);
v___x_1862_ = lean_array_get_size(v_fvarIds_1851_);
v___x_1863_ = lean_nat_dec_lt(v___x_1861_, v___x_1862_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
lean_del_object(v___x_1859_);
lean_dec(v_isRemoved_x3f_1857_);
lean_dec(v_isInserted_x3f_1856_);
lean_dec(v_isType_x3f_1855_);
lean_dec(v_isInstance_x3f_1854_);
lean_dec(v_val_x3f_1853_);
lean_dec_ref(v_type_1852_);
lean_dec_ref(v_fvarIds_1851_);
lean_dec_ref(v_names_1850_);
lean_dec_ref(v_t_u2080_1843_);
v___x_1864_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1);
v___x_1865_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_1864_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_);
return v___x_1865_;
}
else
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1866_ = lean_array_fget_borrowed(v_fvarIds_1851_, v___x_1861_);
lean_inc(v___x_1866_);
v___x_1867_ = l_Lean_Expr_fvar___override(v___x_1866_);
lean_inc(v_a_1848_);
lean_inc_ref(v_a_1847_);
lean_inc(v_a_1846_);
lean_inc_ref(v_a_1845_);
v___x_1868_ = lean_infer_type(v___x_1867_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1870_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_a_1869_);
lean_dec_ref(v___x_1868_);
v___x_1870_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(v_t_u2080_1843_, v_a_1869_, v_useAfter_1842_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1872_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
lean_dec_ref(v___x_1870_);
v___x_1872_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(v_useAfter_1842_, v_a_1871_, v_type_1852_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1883_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1875_ = v___x_1872_;
v_isShared_1876_ = v_isSharedCheck_1883_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1872_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1883_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 2, v_a_1873_);
v___x_1878_ = v___x_1859_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_names_1850_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v_fvarIds_1851_);
lean_ctor_set(v_reuseFailAlloc_1882_, 2, v_a_1873_);
lean_ctor_set(v_reuseFailAlloc_1882_, 3, v_val_x3f_1853_);
lean_ctor_set(v_reuseFailAlloc_1882_, 4, v_isInstance_x3f_1854_);
lean_ctor_set(v_reuseFailAlloc_1882_, 5, v_isType_x3f_1855_);
lean_ctor_set(v_reuseFailAlloc_1882_, 6, v_isInserted_x3f_1856_);
lean_ctor_set(v_reuseFailAlloc_1882_, 7, v_isRemoved_x3f_1857_);
v___x_1878_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
lean_object* v___x_1880_; 
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v___x_1878_);
v___x_1880_ = v___x_1875_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_del_object(v___x_1859_);
lean_dec(v_isRemoved_x3f_1857_);
lean_dec(v_isInserted_x3f_1856_);
lean_dec(v_isType_x3f_1855_);
lean_dec(v_isInstance_x3f_1854_);
lean_dec(v_val_x3f_1853_);
lean_dec_ref(v_fvarIds_1851_);
lean_dec_ref(v_names_1850_);
v_a_1884_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1872_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1872_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
else
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1899_; 
lean_del_object(v___x_1859_);
lean_dec(v_isRemoved_x3f_1857_);
lean_dec(v_isInserted_x3f_1856_);
lean_dec(v_isType_x3f_1855_);
lean_dec(v_isInstance_x3f_1854_);
lean_dec(v_val_x3f_1853_);
lean_dec_ref(v_type_1852_);
lean_dec_ref(v_fvarIds_1851_);
lean_dec_ref(v_names_1850_);
v_a_1892_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1894_ = v___x_1870_;
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1870_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
if (v_isShared_1895_ == 0)
{
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1892_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
else
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
lean_del_object(v___x_1859_);
lean_dec(v_isRemoved_x3f_1857_);
lean_dec(v_isInserted_x3f_1856_);
lean_dec(v_isType_x3f_1855_);
lean_dec(v_isInstance_x3f_1854_);
lean_dec(v_val_x3f_1853_);
lean_dec_ref(v_type_1852_);
lean_dec_ref(v_fvarIds_1851_);
lean_dec_ref(v_names_1850_);
lean_dec_ref(v_t_u2080_1843_);
v_a_1900_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1902_ = v___x_1868_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1868_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1903_ == 0)
{
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_a_1900_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___boxed(lean_object* v_useAfter_1909_, lean_object* v_t_u2080_1910_, lean_object* v_h_u2081_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_){
_start:
{
uint8_t v_useAfter_boxed_1917_; lean_object* v_res_1918_; 
v_useAfter_boxed_1917_ = lean_unbox(v_useAfter_1909_);
v_res_1918_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(v_useAfter_boxed_1917_, v_t_u2080_1910_, v_h_u2081_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
lean_dec(v_a_1915_);
lean_dec_ref(v_a_1914_);
lean_dec(v_a_1913_);
lean_dec_ref(v_a_1912_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(lean_object* v_ctx_u2080_1922_, uint8_t v_useAfter_1923_, lean_object* v_h_u2081_1924_, lean_object* v___x_1925_, lean_object* v___x_1926_, lean_object* v_as_1927_, size_t v_sz_1928_, size_t v_i_1929_, lean_object* v_b_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
uint8_t v___x_1936_; 
v___x_1936_ = lean_usize_dec_lt(v_i_1929_, v_sz_1928_);
if (v___x_1936_ == 0)
{
lean_object* v___x_1937_; 
lean_dec_ref(v___x_1926_);
lean_dec_ref(v___x_1925_);
lean_dec_ref(v_h_u2081_1924_);
v___x_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1937_, 0, v_b_1930_);
return v___x_1937_;
}
else
{
lean_object* v_a_1938_; lean_object* v_fst_1939_; lean_object* v_snd_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_2026_; 
lean_dec_ref(v_b_1930_);
v_a_1938_ = lean_array_uget(v_as_1927_, v_i_1929_);
v_fst_1939_ = lean_ctor_get(v_a_1938_, 0);
v_snd_1940_ = lean_ctor_get(v_a_1938_, 1);
v_isSharedCheck_2026_ = !lean_is_exclusive(v_a_1938_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_1942_ = v_a_1938_;
v_isShared_1943_ = v_isSharedCheck_2026_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_snd_1940_);
lean_inc(v_fst_1939_);
lean_dec(v_a_1938_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_2026_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1944_; uint8_t v___x_1945_; 
v___x_1944_ = lean_box(0);
v___x_1945_ = l_Lean_LocalContext_contains(v_ctx_u2080_1922_, v_snd_1940_);
lean_dec(v_snd_1940_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1946_ = lean_box(0);
v___x_1947_ = l_Lean_Name_str___override(v___x_1946_, v_fst_1939_);
v___x_1948_ = l_Lean_LocalContext_findFromUserName_x3f(v_ctx_u2080_1922_, v___x_1947_);
lean_dec(v___x_1947_);
if (lean_obj_tag(v___x_1948_) == 1)
{
lean_object* v_val_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1977_; 
lean_dec_ref(v___x_1926_);
lean_dec_ref(v___x_1925_);
v_val_1949_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1951_ = v___x_1948_;
v_isShared_1952_ = v_isSharedCheck_1977_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_val_1949_);
lean_dec(v___x_1948_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1977_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = l_Lean_LocalDecl_type(v_val_1949_);
lean_dec(v_val_1949_);
v___x_1954_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(v_useAfter_1923_, v___x_1953_, v_h_u2081_1924_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1968_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1957_ = v___x_1954_;
v_isShared_1958_ = v_isSharedCheck_1968_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1968_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v_a_1955_);
v___x_1960_ = v___x_1951_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___x_1962_; 
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 1, v___x_1944_);
lean_ctor_set(v___x_1942_, 0, v___x_1960_);
v___x_1962_ = v___x_1942_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1960_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v___x_1944_);
v___x_1962_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
lean_object* v___x_1964_; 
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v___x_1962_);
v___x_1964_ = v___x_1957_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1962_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
}
else
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
lean_del_object(v___x_1951_);
lean_del_object(v___x_1942_);
v_a_1969_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1954_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1954_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
}
else
{
lean_dec(v___x_1948_);
if (v_useAfter_1923_ == 0)
{
lean_object* v_type_1978_; lean_object* v_val_x3f_1979_; lean_object* v_isInstance_x3f_1980_; lean_object* v_isType_x3f_1981_; lean_object* v_isInserted_x3f_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1996_; 
v_type_1978_ = lean_ctor_get(v_h_u2081_1924_, 2);
v_val_x3f_1979_ = lean_ctor_get(v_h_u2081_1924_, 3);
v_isInstance_x3f_1980_ = lean_ctor_get(v_h_u2081_1924_, 4);
v_isType_x3f_1981_ = lean_ctor_get(v_h_u2081_1924_, 5);
v_isInserted_x3f_1982_ = lean_ctor_get(v_h_u2081_1924_, 6);
v_isSharedCheck_1996_ = !lean_is_exclusive(v_h_u2081_1924_);
if (v_isSharedCheck_1996_ == 0)
{
lean_object* v_unused_1997_; lean_object* v_unused_1998_; lean_object* v_unused_1999_; 
v_unused_1997_ = lean_ctor_get(v_h_u2081_1924_, 7);
lean_dec(v_unused_1997_);
v_unused_1998_ = lean_ctor_get(v_h_u2081_1924_, 1);
lean_dec(v_unused_1998_);
v_unused_1999_ = lean_ctor_get(v_h_u2081_1924_, 0);
lean_dec(v_unused_1999_);
v___x_1984_ = v_h_u2081_1924_;
v_isShared_1985_ = v_isSharedCheck_1996_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_isInserted_x3f_1982_);
lean_inc(v_isType_x3f_1981_);
lean_inc(v_isInstance_x3f_1980_);
lean_inc(v_val_x3f_1979_);
lean_inc(v_type_1978_);
lean_dec(v_h_u2081_1924_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1996_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1989_; 
v___x_1986_ = lean_box(v___x_1936_);
v___x_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1986_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 7, v___x_1987_);
lean_ctor_set(v___x_1984_, 1, v___x_1926_);
lean_ctor_set(v___x_1984_, 0, v___x_1925_);
v___x_1989_ = v___x_1984_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1925_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v___x_1926_);
lean_ctor_set(v_reuseFailAlloc_1995_, 2, v_type_1978_);
lean_ctor_set(v_reuseFailAlloc_1995_, 3, v_val_x3f_1979_);
lean_ctor_set(v_reuseFailAlloc_1995_, 4, v_isInstance_x3f_1980_);
lean_ctor_set(v_reuseFailAlloc_1995_, 5, v_isType_x3f_1981_);
lean_ctor_set(v_reuseFailAlloc_1995_, 6, v_isInserted_x3f_1982_);
lean_ctor_set(v_reuseFailAlloc_1995_, 7, v___x_1987_);
v___x_1989_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1990_; lean_object* v___x_1992_; 
v___x_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1989_);
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 1, v___x_1944_);
lean_ctor_set(v___x_1942_, 0, v___x_1990_);
v___x_1992_ = v___x_1942_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1990_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v___x_1944_);
v___x_1992_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
lean_object* v___x_1993_; 
v___x_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1992_);
return v___x_1993_;
}
}
}
}
else
{
lean_object* v_type_2000_; lean_object* v_val_x3f_2001_; lean_object* v_isInstance_x3f_2002_; lean_object* v_isType_x3f_2003_; lean_object* v_isRemoved_x3f_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2018_; 
v_type_2000_ = lean_ctor_get(v_h_u2081_1924_, 2);
v_val_x3f_2001_ = lean_ctor_get(v_h_u2081_1924_, 3);
v_isInstance_x3f_2002_ = lean_ctor_get(v_h_u2081_1924_, 4);
v_isType_x3f_2003_ = lean_ctor_get(v_h_u2081_1924_, 5);
v_isRemoved_x3f_2004_ = lean_ctor_get(v_h_u2081_1924_, 7);
v_isSharedCheck_2018_ = !lean_is_exclusive(v_h_u2081_1924_);
if (v_isSharedCheck_2018_ == 0)
{
lean_object* v_unused_2019_; lean_object* v_unused_2020_; lean_object* v_unused_2021_; 
v_unused_2019_ = lean_ctor_get(v_h_u2081_1924_, 6);
lean_dec(v_unused_2019_);
v_unused_2020_ = lean_ctor_get(v_h_u2081_1924_, 1);
lean_dec(v_unused_2020_);
v_unused_2021_ = lean_ctor_get(v_h_u2081_1924_, 0);
lean_dec(v_unused_2021_);
v___x_2006_ = v_h_u2081_1924_;
v_isShared_2007_ = v_isSharedCheck_2018_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_isRemoved_x3f_2004_);
lean_inc(v_isType_x3f_2003_);
lean_inc(v_isInstance_x3f_2002_);
lean_inc(v_val_x3f_2001_);
lean_inc(v_type_2000_);
lean_dec(v_h_u2081_1924_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2018_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2011_; 
v___x_2008_ = lean_box(v___x_1936_);
v___x_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2008_);
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 6, v___x_2009_);
lean_ctor_set(v___x_2006_, 1, v___x_1926_);
lean_ctor_set(v___x_2006_, 0, v___x_1925_);
v___x_2011_ = v___x_2006_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_1925_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v___x_1926_);
lean_ctor_set(v_reuseFailAlloc_2017_, 2, v_type_2000_);
lean_ctor_set(v_reuseFailAlloc_2017_, 3, v_val_x3f_2001_);
lean_ctor_set(v_reuseFailAlloc_2017_, 4, v_isInstance_x3f_2002_);
lean_ctor_set(v_reuseFailAlloc_2017_, 5, v_isType_x3f_2003_);
lean_ctor_set(v_reuseFailAlloc_2017_, 6, v___x_2009_);
lean_ctor_set(v_reuseFailAlloc_2017_, 7, v_isRemoved_x3f_2004_);
v___x_2011_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2012_; lean_object* v___x_2014_; 
v___x_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2011_);
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 1, v___x_1944_);
lean_ctor_set(v___x_1942_, 0, v___x_2012_);
v___x_2014_ = v___x_1942_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2012_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v___x_1944_);
v___x_2014_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
lean_object* v___x_2015_; 
v___x_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2014_);
return v___x_2015_;
}
}
}
}
}
}
else
{
lean_object* v___x_2022_; size_t v___x_2023_; size_t v___x_2024_; 
lean_del_object(v___x_1942_);
lean_dec(v_fst_1939_);
v___x_2022_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___closed__0));
v___x_2023_ = ((size_t)1ULL);
v___x_2024_ = lean_usize_add(v_i_1929_, v___x_2023_);
v_i_1929_ = v___x_2024_;
v_b_1930_ = v___x_2022_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___boxed(lean_object* v_ctx_u2080_2027_, lean_object* v_useAfter_2028_, lean_object* v_h_u2081_2029_, lean_object* v___x_2030_, lean_object* v___x_2031_, lean_object* v_as_2032_, lean_object* v_sz_2033_, lean_object* v_i_2034_, lean_object* v_b_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
uint8_t v_useAfter_boxed_2041_; size_t v_sz_boxed_2042_; size_t v_i_boxed_2043_; lean_object* v_res_2044_; 
v_useAfter_boxed_2041_ = lean_unbox(v_useAfter_2028_);
v_sz_boxed_2042_ = lean_unbox_usize(v_sz_2033_);
lean_dec(v_sz_2033_);
v_i_boxed_2043_ = lean_unbox_usize(v_i_2034_);
lean_dec(v_i_2034_);
v_res_2044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(v_ctx_u2080_2027_, v_useAfter_boxed_2041_, v_h_u2081_2029_, v___x_2030_, v___x_2031_, v_as_2032_, v_sz_boxed_2042_, v_i_boxed_2043_, v_b_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec_ref(v_as_2032_);
lean_dec_ref(v_ctx_u2080_2027_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(uint8_t v_useAfter_2045_, lean_object* v_ctx_u2080_2046_, lean_object* v_h_u2081_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_){
_start:
{
lean_object* v_names_2053_; lean_object* v_fvarIds_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; size_t v_sz_2057_; size_t v___x_2058_; lean_object* v___x_2059_; 
v_names_2053_ = lean_ctor_get(v_h_u2081_2047_, 0);
v_fvarIds_2054_ = lean_ctor_get(v_h_u2081_2047_, 1);
v___x_2055_ = l_Array_zip___redArg(v_names_2053_, v_fvarIds_2054_);
v___x_2056_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___closed__0));
v_sz_2057_ = lean_array_size(v___x_2055_);
v___x_2058_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_2054_);
lean_inc_ref(v_names_2053_);
lean_inc_ref(v_h_u2081_2047_);
v___x_2059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(v_ctx_u2080_2046_, v_useAfter_2045_, v_h_u2081_2047_, v_names_2053_, v_fvarIds_2054_, v___x_2055_, v_sz_2057_, v___x_2058_, v___x_2056_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
lean_dec_ref(v___x_2055_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2072_; 
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2062_ = v___x_2059_;
v_isShared_2063_ = v_isSharedCheck_2072_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2059_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2072_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v_fst_2064_; 
v_fst_2064_ = lean_ctor_get(v_a_2060_, 0);
lean_inc(v_fst_2064_);
lean_dec(v_a_2060_);
if (lean_obj_tag(v_fst_2064_) == 0)
{
lean_object* v___x_2066_; 
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 0, v_h_u2081_2047_);
v___x_2066_ = v___x_2062_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_h_u2081_2047_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
else
{
lean_object* v_val_2068_; lean_object* v___x_2070_; 
lean_dec_ref(v_h_u2081_2047_);
v_val_2068_ = lean_ctor_get(v_fst_2064_, 0);
lean_inc(v_val_2068_);
lean_dec_ref(v_fst_2064_);
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 0, v_val_2068_);
v___x_2070_ = v___x_2062_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_val_2068_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_dec_ref(v_h_u2081_2047_);
v_a_2073_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2059_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2059_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle___boxed(lean_object* v_useAfter_2081_, lean_object* v_ctx_u2080_2082_, lean_object* v_h_u2081_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_){
_start:
{
uint8_t v_useAfter_boxed_2089_; lean_object* v_res_2090_; 
v_useAfter_boxed_2089_ = lean_unbox(v_useAfter_2081_);
v_res_2090_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(v_useAfter_boxed_2089_, v_ctx_u2080_2082_, v_h_u2081_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
lean_dec(v_a_2087_);
lean_dec_ref(v_a_2086_);
lean_dec(v_a_2085_);
lean_dec_ref(v_a_2084_);
lean_dec_ref(v_ctx_u2080_2082_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(uint8_t v_useAfter_2091_, lean_object* v_lctx_u2080_2092_, size_t v_sz_2093_, size_t v_i_2094_, lean_object* v_bs_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
uint8_t v___x_2101_; 
v___x_2101_ = lean_usize_dec_lt(v_i_2094_, v_sz_2093_);
if (v___x_2101_ == 0)
{
lean_object* v___x_2102_; 
v___x_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2102_, 0, v_bs_2095_);
return v___x_2102_;
}
else
{
lean_object* v_v_2103_; lean_object* v___x_2104_; 
v_v_2103_ = lean_array_uget_borrowed(v_bs_2095_, v_i_2094_);
lean_inc(v_v_2103_);
v___x_2104_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(v_useAfter_2091_, v_lctx_u2080_2092_, v_v_2103_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; lean_object* v___x_2106_; lean_object* v_bs_x27_2107_; size_t v___x_2108_; size_t v___x_2109_; lean_object* v___x_2110_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref(v___x_2104_);
v___x_2106_ = lean_unsigned_to_nat(0u);
v_bs_x27_2107_ = lean_array_uset(v_bs_2095_, v_i_2094_, v___x_2106_);
v___x_2108_ = ((size_t)1ULL);
v___x_2109_ = lean_usize_add(v_i_2094_, v___x_2108_);
v___x_2110_ = lean_array_uset(v_bs_x27_2107_, v_i_2094_, v_a_2105_);
v_i_2094_ = v___x_2109_;
v_bs_2095_ = v___x_2110_;
goto _start;
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec_ref(v_bs_2095_);
v_a_2112_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2104_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2104_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0___boxed(lean_object* v_useAfter_2120_, lean_object* v_lctx_u2080_2121_, lean_object* v_sz_2122_, lean_object* v_i_2123_, lean_object* v_bs_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
uint8_t v_useAfter_boxed_2130_; size_t v_sz_boxed_2131_; size_t v_i_boxed_2132_; lean_object* v_res_2133_; 
v_useAfter_boxed_2130_ = lean_unbox(v_useAfter_2120_);
v_sz_boxed_2131_ = lean_unbox_usize(v_sz_2122_);
lean_dec(v_sz_2122_);
v_i_boxed_2132_ = lean_unbox_usize(v_i_2123_);
lean_dec(v_i_2123_);
v_res_2133_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(v_useAfter_boxed_2130_, v_lctx_u2080_2121_, v_sz_boxed_2131_, v_i_boxed_2132_, v_bs_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec_ref(v_lctx_u2080_2121_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(uint8_t v_useAfter_2134_, lean_object* v_lctx_u2080_2135_, lean_object* v_hs_u2081_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_){
_start:
{
size_t v_sz_2142_; size_t v___x_2143_; lean_object* v___x_2144_; 
v_sz_2142_ = lean_array_size(v_hs_u2081_2136_);
v___x_2143_ = ((size_t)0ULL);
v___x_2144_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(v_useAfter_2134_, v_lctx_u2080_2135_, v_sz_2142_, v___x_2143_, v_hs_u2081_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses___boxed(lean_object* v_useAfter_2145_, lean_object* v_lctx_u2080_2146_, lean_object* v_hs_u2081_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_){
_start:
{
uint8_t v_useAfter_boxed_2153_; lean_object* v_res_2154_; 
v_useAfter_boxed_2153_ = lean_unbox(v_useAfter_2145_);
v_res_2154_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(v_useAfter_boxed_2153_, v_lctx_u2080_2146_, v_hs_u2081_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_);
lean_dec(v_a_2151_);
lean_dec_ref(v_a_2150_);
lean_dec(v_a_2149_);
lean_dec_ref(v_a_2148_);
lean_dec_ref(v_lctx_u2080_2146_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal_spec__0___redArg(lean_object* v_e_2155_, lean_object* v___y_2156_){
_start:
{
uint8_t v___x_2158_; 
v___x_2158_ = l_Lean_Expr_hasMVar(v_e_2155_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; 
v___x_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2159_, 0, v_e_2155_);
return v___x_2159_;
}
else
{
lean_object* v___x_2160_; lean_object* v_mctx_2161_; lean_object* v___x_2162_; lean_object* v_fst_2163_; lean_object* v_snd_2164_; lean_object* v___x_2165_; lean_object* v_cache_2166_; lean_object* v_zetaDeltaFVarIds_2167_; lean_object* v_postponed_2168_; lean_object* v_diag_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2178_; 
v___x_2160_ = lean_st_ref_get(v___y_2156_);
v_mctx_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc_ref(v_mctx_2161_);
lean_dec(v___x_2160_);
v___x_2162_ = l_Lean_instantiateMVarsCore(v_mctx_2161_, v_e_2155_);
v_fst_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_fst_2163_);
v_snd_2164_ = lean_ctor_get(v___x_2162_, 1);
lean_inc(v_snd_2164_);
lean_dec_ref(v___x_2162_);
v___x_2165_ = lean_st_ref_take(v___y_2156_);
v_cache_2166_ = lean_ctor_get(v___x_2165_, 1);
v_zetaDeltaFVarIds_2167_ = lean_ctor_get(v___x_2165_, 2);
v_postponed_2168_ = lean_ctor_get(v___x_2165_, 3);
v_diag_2169_ = lean_ctor_get(v___x_2165_, 4);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2178_ == 0)
{
lean_object* v_unused_2179_; 
v_unused_2179_ = lean_ctor_get(v___x_2165_, 0);
lean_dec(v_unused_2179_);
v___x_2171_ = v___x_2165_;
v_isShared_2172_ = v_isSharedCheck_2178_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_diag_2169_);
lean_inc(v_postponed_2168_);
lean_inc(v_zetaDeltaFVarIds_2167_);
lean_inc(v_cache_2166_);
lean_dec(v___x_2165_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2178_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 0, v_snd_2164_);
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_snd_2164_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_cache_2166_);
lean_ctor_set(v_reuseFailAlloc_2177_, 2, v_zetaDeltaFVarIds_2167_);
lean_ctor_set(v_reuseFailAlloc_2177_, 3, v_postponed_2168_);
lean_ctor_set(v_reuseFailAlloc_2177_, 4, v_diag_2169_);
v___x_2174_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = lean_st_ref_set(v___y_2156_, v___x_2174_);
v___x_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2176_, 0, v_fst_2163_);
return v___x_2176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal_spec__0___redArg___boxed(lean_object* v_e_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal_spec__0___redArg(v_e_2180_, v___y_2181_);
lean_dec(v___y_2181_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal_spec__0(lean_object* v_e_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal_spec__0___redArg(v_e_2184_, v___y_2186_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal_spec__0___boxed(lean_object* v_e_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal_spec__0(v_e_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
return v_res_2197_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2(void){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2202_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__1));
v___x_2203_ = l_Lean_stringToMessageData(v___x_2202_);
return v___x_2203_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__3));
v___x_2206_ = l_Lean_stringToMessageData(v___x_2205_);
return v___x_2206_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6(void){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2208_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__5));
v___x_2209_ = l_Lean_stringToMessageData(v___x_2208_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(uint8_t v_useAfter_2210_, lean_object* v_g_u2080_2211_, lean_object* v_i_u2081_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_){
_start:
{
lean_object* v___x_2218_; lean_object* v_mctx_2219_; lean_object* v___x_2220_; 
v___x_2218_ = lean_st_ref_get(v_a_2214_);
v_mctx_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc_ref(v_mctx_2219_);
lean_dec(v___x_2218_);
v___x_2220_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2219_, v_g_u2080_2211_);
if (lean_obj_tag(v___x_2220_) == 1)
{
lean_object* v_val_2221_; lean_object* v_options_2222_; lean_object* v_lctx_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v_toInteractiveGoalCore_2227_; lean_object* v_fst_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2325_; 
v_val_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_val_2221_);
lean_dec_ref(v___x_2220_);
v_options_2222_ = lean_ctor_get(v_a_2215_, 2);
v_lctx_2223_ = lean_ctor_get(v_val_2221_, 1);
lean_inc_ref(v_lctx_2223_);
lean_dec(v_val_2221_);
v___x_2224_ = lean_box(1);
lean_inc_ref(v_options_2222_);
v___x_2225_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2225_, 0, v_options_2222_);
lean_ctor_set(v___x_2225_, 1, v___x_2224_);
lean_ctor_set(v___x_2225_, 2, v___x_2224_);
v___x_2226_ = l_Lean_LocalContext_sanitizeNames(v_lctx_2223_, v___x_2225_);
v_toInteractiveGoalCore_2227_ = lean_ctor_get(v_i_u2081_2212_, 0);
lean_inc_ref(v_toInteractiveGoalCore_2227_);
v_fst_2228_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2325_ == 0)
{
lean_object* v_unused_2326_; 
v_unused_2326_ = lean_ctor_get(v___x_2226_, 1);
lean_dec(v_unused_2326_);
v___x_2230_ = v___x_2226_;
v_isShared_2231_ = v_isSharedCheck_2325_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_fst_2228_);
lean_dec(v___x_2226_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2325_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v_userName_x3f_2232_; lean_object* v_goalPrefix_2233_; lean_object* v_mvarId_2234_; lean_object* v_isRemoved_x3f_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2322_; 
v_userName_x3f_2232_ = lean_ctor_get(v_i_u2081_2212_, 1);
v_goalPrefix_2233_ = lean_ctor_get(v_i_u2081_2212_, 2);
v_mvarId_2234_ = lean_ctor_get(v_i_u2081_2212_, 3);
v_isRemoved_x3f_2235_ = lean_ctor_get(v_i_u2081_2212_, 5);
v_isSharedCheck_2322_ = !lean_is_exclusive(v_i_u2081_2212_);
if (v_isSharedCheck_2322_ == 0)
{
lean_object* v_unused_2323_; lean_object* v_unused_2324_; 
v_unused_2323_ = lean_ctor_get(v_i_u2081_2212_, 4);
lean_dec(v_unused_2323_);
v_unused_2324_ = lean_ctor_get(v_i_u2081_2212_, 0);
lean_dec(v_unused_2324_);
v___x_2237_ = v_i_u2081_2212_;
v_isShared_2238_ = v_isSharedCheck_2322_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_isRemoved_x3f_2235_);
lean_inc(v_mvarId_2234_);
lean_inc(v_goalPrefix_2233_);
lean_inc(v_userName_x3f_2232_);
lean_dec(v_i_u2081_2212_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2322_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v_hyps_2239_; lean_object* v_type_2240_; lean_object* v_ctx_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2321_; 
v_hyps_2239_ = lean_ctor_get(v_toInteractiveGoalCore_2227_, 0);
v_type_2240_ = lean_ctor_get(v_toInteractiveGoalCore_2227_, 1);
v_ctx_2241_ = lean_ctor_get(v_toInteractiveGoalCore_2227_, 2);
v_isSharedCheck_2321_ = !lean_is_exclusive(v_toInteractiveGoalCore_2227_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2243_ = v_toInteractiveGoalCore_2227_;
v_isShared_2244_ = v_isSharedCheck_2321_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_ctx_2241_);
lean_inc(v_type_2240_);
lean_inc(v_hyps_2239_);
lean_dec(v_toInteractiveGoalCore_2227_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2321_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; 
v___x_2245_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(v_useAfter_2210_, v_fst_2228_, v_hyps_2239_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_);
lean_dec(v_fst_2228_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_a_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_a_2246_);
lean_dec_ref(v___x_2245_);
v___x_2247_ = l_Lean_Expr_mvar___override(v_g_u2080_2211_);
lean_inc(v_a_2216_);
lean_inc_ref(v_a_2215_);
lean_inc(v_a_2214_);
lean_inc_ref(v_a_2213_);
v___x_2248_ = lean_infer_type(v___x_2247_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v_a_2249_; lean_object* v___x_2250_; lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2304_; 
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc(v_a_2249_);
lean_dec_ref(v___x_2248_);
v___x_2250_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal_spec__0___redArg(v_a_2249_, v_a_2214_);
v_a_2251_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2253_ = v___x_2250_;
v_isShared_2254_ = v_isSharedCheck_2304_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2250_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2304_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2255_; lean_object* v_mctx_2256_; lean_object* v___x_2257_; 
v___x_2255_ = lean_st_ref_get(v_a_2214_);
v_mctx_2256_ = lean_ctor_get(v___x_2255_, 0);
lean_inc_ref(v_mctx_2256_);
lean_dec(v___x_2255_);
v___x_2257_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2256_, v_mvarId_2234_);
if (lean_obj_tag(v___x_2257_) == 1)
{
lean_object* v_val_2258_; lean_object* v_type_2259_; lean_object* v___x_2260_; lean_object* v_a_2261_; lean_object* v___x_2262_; 
lean_del_object(v___x_2253_);
lean_del_object(v___x_2230_);
v_val_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_val_2258_);
lean_dec_ref(v___x_2257_);
v_type_2259_ = lean_ctor_get(v_val_2258_, 2);
lean_inc_ref(v_type_2259_);
lean_dec(v_val_2258_);
v___x_2260_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal_spec__0___redArg(v_type_2259_, v_a_2214_);
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_a_2261_);
lean_dec_ref(v___x_2260_);
v___x_2262_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(v_a_2251_, v_a_2261_, v_useAfter_2210_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; lean_object* v___x_2264_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc(v_a_2263_);
lean_dec_ref(v___x_2262_);
v___x_2264_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(v_useAfter_2210_, v_a_2263_, v_type_2240_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2279_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2267_ = v___x_2264_;
v_isShared_2268_ = v_isSharedCheck_2279_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2264_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2279_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 1, v_a_2265_);
lean_ctor_set(v___x_2243_, 0, v_a_2246_);
v___x_2270_ = v___x_2243_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2246_);
lean_ctor_set(v_reuseFailAlloc_2278_, 1, v_a_2265_);
lean_ctor_set(v_reuseFailAlloc_2278_, 2, v_ctx_2241_);
v___x_2270_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
lean_object* v___x_2271_; lean_object* v___x_2273_; 
v___x_2271_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__0));
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 4, v___x_2271_);
lean_ctor_set(v___x_2237_, 0, v___x_2270_);
v___x_2273_ = v___x_2237_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2270_);
lean_ctor_set(v_reuseFailAlloc_2277_, 1, v_userName_x3f_2232_);
lean_ctor_set(v_reuseFailAlloc_2277_, 2, v_goalPrefix_2233_);
lean_ctor_set(v_reuseFailAlloc_2277_, 3, v_mvarId_2234_);
lean_ctor_set(v_reuseFailAlloc_2277_, 4, v___x_2271_);
lean_ctor_set(v_reuseFailAlloc_2277_, 5, v_isRemoved_x3f_2235_);
v___x_2273_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
lean_object* v___x_2275_; 
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 0, v___x_2273_);
v___x_2275_ = v___x_2267_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2273_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
lean_dec(v_a_2246_);
lean_del_object(v___x_2243_);
lean_dec_ref(v_ctx_2241_);
lean_del_object(v___x_2237_);
lean_dec(v_isRemoved_x3f_2235_);
lean_dec(v_mvarId_2234_);
lean_dec_ref(v_goalPrefix_2233_);
lean_dec(v_userName_x3f_2232_);
v_a_2280_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___x_2264_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2264_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2285_; 
if (v_isShared_2283_ == 0)
{
v___x_2285_ = v___x_2282_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
else
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2295_; 
lean_dec(v_a_2246_);
lean_del_object(v___x_2243_);
lean_dec_ref(v_ctx_2241_);
lean_dec_ref(v_type_2240_);
lean_del_object(v___x_2237_);
lean_dec(v_isRemoved_x3f_2235_);
lean_dec(v_mvarId_2234_);
lean_dec_ref(v_goalPrefix_2233_);
lean_dec(v_userName_x3f_2232_);
v_a_2288_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2290_ = v___x_2262_;
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2262_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2293_; 
if (v_isShared_2291_ == 0)
{
v___x_2293_ = v___x_2290_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
else
{
lean_object* v___x_2296_; lean_object* v___x_2298_; 
lean_dec(v___x_2257_);
lean_dec(v_a_2251_);
lean_dec(v_a_2246_);
lean_del_object(v___x_2243_);
lean_dec_ref(v_ctx_2241_);
lean_dec_ref(v_type_2240_);
lean_del_object(v___x_2237_);
lean_dec(v_isRemoved_x3f_2235_);
lean_dec_ref(v_goalPrefix_2233_);
lean_dec(v_userName_x3f_2232_);
v___x_2296_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2);
if (v_isShared_2254_ == 0)
{
lean_ctor_set_tag(v___x_2253_, 1);
lean_ctor_set(v___x_2253_, 0, v_mvarId_2234_);
v___x_2298_ = v___x_2253_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_mvarId_2234_);
v___x_2298_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
lean_object* v___x_2300_; 
if (v_isShared_2231_ == 0)
{
lean_ctor_set_tag(v___x_2230_, 7);
lean_ctor_set(v___x_2230_, 1, v___x_2298_);
lean_ctor_set(v___x_2230_, 0, v___x_2296_);
v___x_2300_ = v___x_2230_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v___x_2296_);
lean_ctor_set(v_reuseFailAlloc_2302_, 1, v___x_2298_);
v___x_2300_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
lean_object* v___x_2301_; 
v___x_2301_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_2300_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_);
return v___x_2301_;
}
}
}
}
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_dec(v_a_2246_);
lean_del_object(v___x_2243_);
lean_dec_ref(v_ctx_2241_);
lean_dec_ref(v_type_2240_);
lean_del_object(v___x_2237_);
lean_dec(v_isRemoved_x3f_2235_);
lean_dec(v_mvarId_2234_);
lean_dec_ref(v_goalPrefix_2233_);
lean_dec(v_userName_x3f_2232_);
lean_del_object(v___x_2230_);
v_a_2305_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2248_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2248_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
lean_del_object(v___x_2243_);
lean_dec_ref(v_ctx_2241_);
lean_dec_ref(v_type_2240_);
lean_del_object(v___x_2237_);
lean_dec(v_isRemoved_x3f_2235_);
lean_dec(v_mvarId_2234_);
lean_dec_ref(v_goalPrefix_2233_);
lean_dec(v_userName_x3f_2232_);
lean_del_object(v___x_2230_);
lean_dec(v_g_u2080_2211_);
v_a_2313_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2245_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2245_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
lean_dec(v___x_2220_);
lean_dec_ref(v_i_u2081_2212_);
v___x_2327_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4);
v___x_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2328_, 0, v_g_u2080_2211_);
v___x_2329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2327_);
lean_ctor_set(v___x_2329_, 1, v___x_2328_);
v___x_2330_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6);
v___x_2331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2329_);
lean_ctor_set(v___x_2331_, 1, v___x_2330_);
v___x_2332_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_2331_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_);
return v___x_2332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___boxed(lean_object* v_useAfter_2333_, lean_object* v_g_u2080_2334_, lean_object* v_i_u2081_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_){
_start:
{
uint8_t v_useAfter_boxed_2341_; lean_object* v_res_2342_; 
v_useAfter_boxed_2341_ = lean_unbox(v_useAfter_2333_);
v_res_2342_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(v_useAfter_boxed_2341_, v_g_u2080_2334_, v_i_u2081_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_);
lean_dec(v_a_2339_);
lean_dec_ref(v_a_2338_);
lean_dec(v_a_2337_);
lean_dec_ref(v_a_2336_);
return v_res_2342_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(lean_object* v_opts_2343_, lean_object* v_opt_2344_){
_start:
{
lean_object* v_name_2345_; lean_object* v_defValue_2346_; lean_object* v_map_2347_; lean_object* v___x_2348_; 
v_name_2345_ = lean_ctor_get(v_opt_2344_, 0);
v_defValue_2346_ = lean_ctor_get(v_opt_2344_, 1);
v_map_2347_ = lean_ctor_get(v_opts_2343_, 0);
v___x_2348_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2347_, v_name_2345_);
if (lean_obj_tag(v___x_2348_) == 0)
{
uint8_t v___x_2349_; 
v___x_2349_ = lean_unbox(v_defValue_2346_);
return v___x_2349_;
}
else
{
lean_object* v_val_2350_; 
v_val_2350_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_val_2350_);
lean_dec_ref(v___x_2348_);
if (lean_obj_tag(v_val_2350_) == 1)
{
uint8_t v_v_2351_; 
v_v_2351_ = lean_ctor_get_uint8(v_val_2350_, 0);
lean_dec_ref(v_val_2350_);
return v_v_2351_;
}
else
{
uint8_t v___x_2352_; 
lean_dec(v_val_2350_);
v___x_2352_ = lean_unbox(v_defValue_2346_);
return v___x_2352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0___boxed(lean_object* v_opts_2353_, lean_object* v_opt_2354_){
_start:
{
uint8_t v_res_2355_; lean_object* v_r_2356_; 
v_res_2355_ = l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(v_opts_2353_, v_opt_2354_);
lean_dec_ref(v_opt_2354_);
lean_dec_ref(v_opts_2353_);
v_r_2356_ = lean_box(v_res_2355_);
return v_r_2356_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(lean_object* v_x_2357_, lean_object* v_x_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
if (lean_obj_tag(v_x_2358_) == 0)
{
lean_object* v___x_2364_; 
v___x_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2364_, 0, v_x_2357_);
return v___x_2364_;
}
else
{
lean_object* v_head_2365_; lean_object* v_tail_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v_head_2365_ = lean_ctor_get(v_x_2358_, 0);
lean_inc_n(v_head_2365_, 2);
v_tail_2366_ = lean_ctor_get(v_x_2358_, 1);
lean_inc(v_tail_2366_);
lean_dec_ref(v_x_2358_);
v___x_2367_ = l_Lean_Expr_mvar___override(v_head_2365_);
v___x_2368_ = l_Lean_Meta_getMVars(v___x_2367_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc(v_a_2369_);
lean_dec_ref(v___x_2368_);
v___x_2370_ = l_Lean_MVarIdSet_ofArray(v_a_2369_);
lean_dec(v_a_2369_);
v___x_2371_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_head_2365_, v___x_2370_, v_x_2357_);
v_x_2357_ = v___x_2371_;
v_x_2358_ = v_tail_2366_;
goto _start;
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
lean_dec(v_tail_2366_);
lean_dec(v_head_2365_);
lean_dec(v_x_2357_);
v_a_2373_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2368_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2368_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1___boxed(lean_object* v_x_2381_, lean_object* v_x_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(v_x_2381_, v_x_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
return v_res_2388_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__1(uint8_t v___y_2389_, lean_object* v___f_2390_, lean_object* v_mvarId_2391_, lean_object* v_g_u2080_2392_){
_start:
{
if (v___y_2389_ == 0)
{
lean_object* v___x_2393_; uint8_t v___x_2394_; 
v___x_2393_ = lean_apply_2(v___f_2390_, v_mvarId_2391_, v_g_u2080_2392_);
v___x_2394_ = lean_unbox(v___x_2393_);
return v___x_2394_;
}
else
{
lean_object* v___x_2395_; uint8_t v___x_2396_; 
v___x_2395_ = lean_apply_2(v___f_2390_, v_g_u2080_2392_, v_mvarId_2391_);
v___x_2396_ = lean_unbox(v___x_2395_);
return v___x_2396_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__1___boxed(lean_object* v___y_2397_, lean_object* v___f_2398_, lean_object* v_mvarId_2399_, lean_object* v_g_u2080_2400_){
_start:
{
uint8_t v___y_3395__boxed_2401_; uint8_t v_res_2402_; lean_object* v_r_2403_; 
v___y_3395__boxed_2401_ = lean_unbox(v___y_2397_);
v_res_2402_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__1(v___y_3395__boxed_2401_, v___f_2398_, v_mvarId_2399_, v_g_u2080_2400_);
v_r_2403_ = lean_box(v_res_2402_);
return v_r_2403_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(lean_object* v_t_2404_, lean_object* v_k_2405_){
_start:
{
if (lean_obj_tag(v_t_2404_) == 0)
{
lean_object* v_k_2406_; lean_object* v_v_2407_; lean_object* v_l_2408_; lean_object* v_r_2409_; uint8_t v___x_2410_; 
v_k_2406_ = lean_ctor_get(v_t_2404_, 1);
v_v_2407_ = lean_ctor_get(v_t_2404_, 2);
v_l_2408_ = lean_ctor_get(v_t_2404_, 3);
v_r_2409_ = lean_ctor_get(v_t_2404_, 4);
v___x_2410_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2405_, v_k_2406_);
switch(v___x_2410_)
{
case 0:
{
v_t_2404_ = v_l_2408_;
goto _start;
}
case 1:
{
lean_object* v___x_2412_; 
lean_inc(v_v_2407_);
v___x_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2412_, 0, v_v_2407_);
return v___x_2412_;
}
default: 
{
v_t_2404_ = v_r_2409_;
goto _start;
}
}
}
else
{
lean_object* v___x_2414_; 
v___x_2414_ = lean_box(0);
return v___x_2414_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg___boxed(lean_object* v_t_2415_, lean_object* v_k_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(v_t_2415_, v_k_2416_);
lean_dec(v_k_2416_);
lean_dec(v_t_2415_);
return v_res_2417_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(lean_object* v_k_2418_, lean_object* v_t_2419_){
_start:
{
if (lean_obj_tag(v_t_2419_) == 0)
{
lean_object* v_k_2420_; lean_object* v_l_2421_; lean_object* v_r_2422_; uint8_t v___x_2423_; 
v_k_2420_ = lean_ctor_get(v_t_2419_, 1);
v_l_2421_ = lean_ctor_get(v_t_2419_, 3);
v_r_2422_ = lean_ctor_get(v_t_2419_, 4);
v___x_2423_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2418_, v_k_2420_);
switch(v___x_2423_)
{
case 0:
{
v_t_2419_ = v_l_2421_;
goto _start;
}
case 1:
{
uint8_t v___x_2425_; 
v___x_2425_ = 1;
return v___x_2425_;
}
default: 
{
v_t_2419_ = v_r_2422_;
goto _start;
}
}
}
else
{
uint8_t v___x_2427_; 
v___x_2427_ = 0;
return v___x_2427_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg___boxed(lean_object* v_k_2428_, lean_object* v_t_2429_){
_start:
{
uint8_t v_res_2430_; lean_object* v_r_2431_; 
v_res_2430_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_k_2428_, v_t_2429_);
lean_dec(v_t_2429_);
lean_dec(v_k_2428_);
v_r_2431_ = lean_box(v_res_2430_);
return v_r_2431_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(lean_object* v_a_2432_, uint8_t v___x_2433_, lean_object* v_before_2434_, lean_object* v_after_2435_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(v_a_2432_, v_before_2434_);
if (lean_obj_tag(v___x_2436_) == 0)
{
return v___x_2433_;
}
else
{
lean_object* v_val_2437_; uint8_t v___x_2438_; 
v_val_2437_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_val_2437_);
lean_dec_ref(v___x_2436_);
v___x_2438_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_after_2435_, v_val_2437_);
lean_dec(v_val_2437_);
return v___x_2438_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0___boxed(lean_object* v_a_2439_, lean_object* v___x_2440_, lean_object* v_before_2441_, lean_object* v_after_2442_){
_start:
{
uint8_t v___x_3447__boxed_2443_; uint8_t v_res_2444_; lean_object* v_r_2445_; 
v___x_3447__boxed_2443_ = lean_unbox(v___x_2440_);
v_res_2444_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(v_a_2439_, v___x_3447__boxed_2443_, v_before_2441_, v_after_2442_);
lean_dec(v_after_2442_);
lean_dec(v_before_2441_);
lean_dec(v_a_2439_);
v_r_2445_ = lean_box(v_res_2444_);
return v_r_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4_spec__4___redArg(lean_object* v_lctx_2446_, lean_object* v_localInsts_2447_, lean_object* v_x_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2446_, v_localInsts_2447_, v_x_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2457_ = v___x_2454_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2454_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
if (v_isShared_2458_ == 0)
{
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2455_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
v_a_2463_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___x_2454_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2454_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2463_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4_spec__4___redArg___boxed(lean_object* v_lctx_2471_, lean_object* v_localInsts_2472_, lean_object* v_x_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4_spec__4___redArg(v_lctx_2471_, v_localInsts_2472_, v_x_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
return v_res_2479_;
}
}
static lean_object* _init_l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2481_ = ((lean_object*)(l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___redArg___closed__0));
v___x_2482_ = l_Lean_stringToMessageData(v___x_2481_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___redArg(lean_object* v_goal_2483_, lean_object* v_action_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
lean_object* v___x_2490_; lean_object* v_mctx_2491_; lean_object* v___x_2492_; 
v___x_2490_ = lean_st_ref_get(v___y_2486_);
v_mctx_2491_ = lean_ctor_get(v___x_2490_, 0);
lean_inc_ref(v_mctx_2491_);
lean_dec(v___x_2490_);
v___x_2492_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2491_, v_goal_2483_);
if (lean_obj_tag(v___x_2492_) == 1)
{
lean_object* v_val_2493_; lean_object* v_options_2494_; lean_object* v_lctx_2495_; lean_object* v_localInstances_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v_fst_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
lean_dec(v_goal_2483_);
v_val_2493_ = lean_ctor_get(v___x_2492_, 0);
lean_inc(v_val_2493_);
lean_dec_ref(v___x_2492_);
v_options_2494_ = lean_ctor_get(v___y_2487_, 2);
v_lctx_2495_ = lean_ctor_get(v_val_2493_, 1);
v_localInstances_2496_ = lean_ctor_get(v_val_2493_, 4);
lean_inc_ref(v_localInstances_2496_);
v___x_2497_ = lean_box(1);
lean_inc_ref(v_options_2494_);
v___x_2498_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2498_, 0, v_options_2494_);
lean_ctor_set(v___x_2498_, 1, v___x_2497_);
lean_ctor_set(v___x_2498_, 2, v___x_2497_);
lean_inc_ref(v_lctx_2495_);
v___x_2499_ = l_Lean_LocalContext_sanitizeNames(v_lctx_2495_, v___x_2498_);
v_fst_2500_ = lean_ctor_get(v___x_2499_, 0);
lean_inc_n(v_fst_2500_, 2);
lean_dec_ref(v___x_2499_);
v___x_2501_ = lean_apply_2(v_action_2484_, v_fst_2500_, v_val_2493_);
v___x_2502_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4_spec__4___redArg(v_fst_2500_, v_localInstances_2496_, v___x_2501_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
return v___x_2502_;
}
else
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
lean_dec(v___x_2492_);
lean_dec_ref(v_action_2484_);
v___x_2503_ = lean_obj_once(&l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___redArg___closed__1, &l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___redArg___closed__1_once, _init_l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___redArg___closed__1);
v___x_2504_ = l_Lean_MessageData_ofName(v_goal_2483_);
v___x_2505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2503_);
lean_ctor_set(v___x_2505_, 1, v___x_2504_);
v___x_2506_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_2505_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
return v___x_2506_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___redArg___boxed(lean_object* v_goal_2507_, lean_object* v_action_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___redArg(v_goal_2507_, v_action_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
return v_res_2514_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__2(lean_object* v_mvarId_2515_, lean_object* v_g_u2080_2516_){
_start:
{
uint8_t v___x_2517_; 
v___x_2517_ = l_Lean_instBEqMVarId_beq(v_g_u2080_2516_, v_mvarId_2515_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__2___boxed(lean_object* v_mvarId_2518_, lean_object* v_g_u2080_2519_){
_start:
{
uint8_t v_res_2520_; lean_object* v_r_2521_; 
v_res_2520_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__2(v_mvarId_2518_, v_g_u2080_2519_);
lean_dec(v_g_u2080_2519_);
lean_dec(v_mvarId_2518_);
v_r_2521_ = lean_box(v_res_2520_);
return v_r_2521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__3(lean_object* v___y_2522_, lean_object* v___f_2523_, lean_object* v___f_2524_, uint8_t v_useAfter_2525_, lean_object* v_v_2526_, uint8_t v___y_2527_, uint8_t v___x_2528_, lean_object* v_toInteractiveGoalCore_2529_, lean_object* v_userName_x3f_2530_, lean_object* v_goalPrefix_2531_, lean_object* v_mvarId_2532_, lean_object* v_isInserted_x3f_2533_, lean_object* v_isRemoved_x3f_2534_, lean_object* v___lctx_u2081_2535_, lean_object* v___md_u2081_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
uint8_t v___x_2542_; 
lean_inc(v___y_2522_);
v___x_2542_ = l_List_any___redArg(v___y_2522_, v___f_2523_);
if (v___x_2542_ == 0)
{
lean_object* v___x_2543_; 
v___x_2543_ = l_List_find_x3f___redArg(v___f_2524_, v___y_2522_);
if (lean_obj_tag(v___x_2543_) == 1)
{
lean_object* v_val_2544_; lean_object* v___x_2545_; 
lean_dec(v_isRemoved_x3f_2534_);
lean_dec(v_isInserted_x3f_2533_);
lean_dec(v_mvarId_2532_);
lean_dec_ref(v_goalPrefix_2531_);
lean_dec(v_userName_x3f_2530_);
lean_dec_ref(v_toInteractiveGoalCore_2529_);
v_val_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_val_2544_);
lean_dec_ref(v___x_2543_);
v___x_2545_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(v_useAfter_2525_, v_val_2544_, v_v_2526_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
return v___x_2545_;
}
else
{
lean_dec(v___x_2543_);
lean_dec(v_v_2526_);
if (v___y_2527_ == 0)
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
lean_dec(v_isRemoved_x3f_2534_);
v___x_2546_ = lean_box(v___x_2528_);
v___x_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2546_);
v___x_2548_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2548_, 0, v_toInteractiveGoalCore_2529_);
lean_ctor_set(v___x_2548_, 1, v_userName_x3f_2530_);
lean_ctor_set(v___x_2548_, 2, v_goalPrefix_2531_);
lean_ctor_set(v___x_2548_, 3, v_mvarId_2532_);
lean_ctor_set(v___x_2548_, 4, v_isInserted_x3f_2533_);
lean_ctor_set(v___x_2548_, 5, v___x_2547_);
v___x_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2548_);
return v___x_2549_;
}
else
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
lean_dec(v_isInserted_x3f_2533_);
v___x_2550_ = lean_box(v___x_2528_);
v___x_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2550_);
v___x_2552_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2552_, 0, v_toInteractiveGoalCore_2529_);
lean_ctor_set(v___x_2552_, 1, v_userName_x3f_2530_);
lean_ctor_set(v___x_2552_, 2, v_goalPrefix_2531_);
lean_ctor_set(v___x_2552_, 3, v_mvarId_2532_);
lean_ctor_set(v___x_2552_, 4, v___x_2551_);
lean_ctor_set(v___x_2552_, 5, v_isRemoved_x3f_2534_);
v___x_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2552_);
return v___x_2553_;
}
}
}
else
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
lean_dec(v_isInserted_x3f_2533_);
lean_dec(v_v_2526_);
lean_dec_ref(v___f_2524_);
lean_dec(v___y_2522_);
v___x_2554_ = lean_box(0);
v___x_2555_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2555_, 0, v_toInteractiveGoalCore_2529_);
lean_ctor_set(v___x_2555_, 1, v_userName_x3f_2530_);
lean_ctor_set(v___x_2555_, 2, v_goalPrefix_2531_);
lean_ctor_set(v___x_2555_, 3, v_mvarId_2532_);
lean_ctor_set(v___x_2555_, 4, v___x_2554_);
lean_ctor_set(v___x_2555_, 5, v_isRemoved_x3f_2534_);
v___x_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2555_);
return v___x_2556_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__3___boxed(lean_object** _args){
lean_object* v___y_2557_ = _args[0];
lean_object* v___f_2558_ = _args[1];
lean_object* v___f_2559_ = _args[2];
lean_object* v_useAfter_2560_ = _args[3];
lean_object* v_v_2561_ = _args[4];
lean_object* v___y_2562_ = _args[5];
lean_object* v___x_2563_ = _args[6];
lean_object* v_toInteractiveGoalCore_2564_ = _args[7];
lean_object* v_userName_x3f_2565_ = _args[8];
lean_object* v_goalPrefix_2566_ = _args[9];
lean_object* v_mvarId_2567_ = _args[10];
lean_object* v_isInserted_x3f_2568_ = _args[11];
lean_object* v_isRemoved_x3f_2569_ = _args[12];
lean_object* v___lctx_u2081_2570_ = _args[13];
lean_object* v___md_u2081_2571_ = _args[14];
lean_object* v___y_2572_ = _args[15];
lean_object* v___y_2573_ = _args[16];
lean_object* v___y_2574_ = _args[17];
lean_object* v___y_2575_ = _args[18];
lean_object* v___y_2576_ = _args[19];
_start:
{
uint8_t v_useAfter_boxed_2577_; uint8_t v___y_3560__boxed_2578_; uint8_t v___x_3561__boxed_2579_; lean_object* v_res_2580_; 
v_useAfter_boxed_2577_ = lean_unbox(v_useAfter_2560_);
v___y_3560__boxed_2578_ = lean_unbox(v___y_2562_);
v___x_3561__boxed_2579_ = lean_unbox(v___x_2563_);
v_res_2580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__3(v___y_2557_, v___f_2558_, v___f_2559_, v_useAfter_boxed_2577_, v_v_2561_, v___y_3560__boxed_2578_, v___x_3561__boxed_2579_, v_toInteractiveGoalCore_2564_, v_userName_x3f_2565_, v_goalPrefix_2566_, v_mvarId_2567_, v_isInserted_x3f_2568_, v_isRemoved_x3f_2569_, v___lctx_u2081_2570_, v___md_u2081_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___md_u2081_2571_);
lean_dec_ref(v___lctx_u2081_2570_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5(uint8_t v___y_2581_, lean_object* v_a_2582_, lean_object* v___y_2583_, uint8_t v_useAfter_2584_, uint8_t v___x_2585_, size_t v_sz_2586_, size_t v_i_2587_, lean_object* v_bs_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
uint8_t v___x_2594_; 
v___x_2594_ = lean_usize_dec_lt(v_i_2587_, v_sz_2586_);
if (v___x_2594_ == 0)
{
lean_object* v___x_2595_; 
lean_dec(v___y_2583_);
lean_dec(v_a_2582_);
v___x_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2595_, 0, v_bs_2588_);
return v___x_2595_;
}
else
{
lean_object* v_v_2596_; lean_object* v_toInteractiveGoalCore_2597_; lean_object* v_userName_x3f_2598_; lean_object* v_goalPrefix_2599_; lean_object* v_mvarId_2600_; lean_object* v_isInserted_x3f_2601_; lean_object* v_isRemoved_x3f_2602_; uint8_t v___x_2603_; lean_object* v___x_2604_; lean_object* v___f_2605_; lean_object* v___x_2606_; lean_object* v___f_2607_; lean_object* v___f_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___f_2612_; lean_object* v___x_2613_; 
v_v_2596_ = lean_array_uget_borrowed(v_bs_2588_, v_i_2587_);
v_toInteractiveGoalCore_2597_ = lean_ctor_get(v_v_2596_, 0);
v_userName_x3f_2598_ = lean_ctor_get(v_v_2596_, 1);
v_goalPrefix_2599_ = lean_ctor_get(v_v_2596_, 2);
v_mvarId_2600_ = lean_ctor_get(v_v_2596_, 3);
v_isInserted_x3f_2601_ = lean_ctor_get(v_v_2596_, 4);
v_isRemoved_x3f_2602_ = lean_ctor_get(v_v_2596_, 5);
v___x_2603_ = 0;
v___x_2604_ = lean_box(v___x_2603_);
lean_inc(v_a_2582_);
v___f_2605_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2605_, 0, v_a_2582_);
lean_closure_set(v___f_2605_, 1, v___x_2604_);
v___x_2606_ = lean_box(v___y_2581_);
lean_inc_n(v_mvarId_2600_, 4);
v___f_2607_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2607_, 0, v___x_2606_);
lean_closure_set(v___f_2607_, 1, v___f_2605_);
lean_closure_set(v___f_2607_, 2, v_mvarId_2600_);
v___f_2608_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__2___boxed), 2, 1);
lean_closure_set(v___f_2608_, 0, v_mvarId_2600_);
v___x_2609_ = lean_box(v_useAfter_2584_);
v___x_2610_ = lean_box(v___y_2581_);
v___x_2611_ = lean_box(v___x_2585_);
lean_inc(v_isRemoved_x3f_2602_);
lean_inc(v_isInserted_x3f_2601_);
lean_inc_ref(v_goalPrefix_2599_);
lean_inc(v_userName_x3f_2598_);
lean_inc_ref(v_toInteractiveGoalCore_2597_);
lean_inc(v_v_2596_);
lean_inc(v___y_2583_);
v___f_2612_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__3___boxed), 20, 13);
lean_closure_set(v___f_2612_, 0, v___y_2583_);
lean_closure_set(v___f_2612_, 1, v___f_2608_);
lean_closure_set(v___f_2612_, 2, v___f_2607_);
lean_closure_set(v___f_2612_, 3, v___x_2609_);
lean_closure_set(v___f_2612_, 4, v_v_2596_);
lean_closure_set(v___f_2612_, 5, v___x_2610_);
lean_closure_set(v___f_2612_, 6, v___x_2611_);
lean_closure_set(v___f_2612_, 7, v_toInteractiveGoalCore_2597_);
lean_closure_set(v___f_2612_, 8, v_userName_x3f_2598_);
lean_closure_set(v___f_2612_, 9, v_goalPrefix_2599_);
lean_closure_set(v___f_2612_, 10, v_mvarId_2600_);
lean_closure_set(v___f_2612_, 11, v_isInserted_x3f_2601_);
lean_closure_set(v___f_2612_, 12, v_isRemoved_x3f_2602_);
v___x_2613_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___redArg(v_mvarId_2600_, v___f_2612_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; lean_object* v___x_2615_; lean_object* v_bs_x27_2616_; size_t v___x_2617_; size_t v___x_2618_; lean_object* v___x_2619_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc(v_a_2614_);
lean_dec_ref(v___x_2613_);
v___x_2615_ = lean_unsigned_to_nat(0u);
v_bs_x27_2616_ = lean_array_uset(v_bs_2588_, v_i_2587_, v___x_2615_);
v___x_2617_ = ((size_t)1ULL);
v___x_2618_ = lean_usize_add(v_i_2587_, v___x_2617_);
v___x_2619_ = lean_array_uset(v_bs_x27_2616_, v_i_2587_, v_a_2614_);
v_i_2587_ = v___x_2618_;
v_bs_2588_ = v___x_2619_;
goto _start;
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_dec_ref(v_bs_2588_);
lean_dec(v___y_2583_);
lean_dec(v_a_2582_);
v_a_2621_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2613_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2613_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5___boxed(lean_object* v___y_2629_, lean_object* v_a_2630_, lean_object* v___y_2631_, lean_object* v_useAfter_2632_, lean_object* v___x_2633_, lean_object* v_sz_2634_, lean_object* v_i_2635_, lean_object* v_bs_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
uint8_t v___y_3617__boxed_2642_; uint8_t v_useAfter_boxed_2643_; uint8_t v___x_3620__boxed_2644_; size_t v_sz_boxed_2645_; size_t v_i_boxed_2646_; lean_object* v_res_2647_; 
v___y_3617__boxed_2642_ = lean_unbox(v___y_2629_);
v_useAfter_boxed_2643_ = lean_unbox(v_useAfter_2632_);
v___x_3620__boxed_2644_ = lean_unbox(v___x_2633_);
v_sz_boxed_2645_ = lean_unbox_usize(v_sz_2634_);
lean_dec(v_sz_2634_);
v_i_boxed_2646_ = lean_unbox_usize(v_i_2635_);
lean_dec(v_i_2635_);
v_res_2647_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5(v___y_3617__boxed_2642_, v_a_2630_, v___y_2631_, v_useAfter_boxed_2643_, v___x_3620__boxed_2644_, v_sz_boxed_2645_, v_i_boxed_2646_, v_bs_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_diffInteractiveGoals(uint8_t v_useAfter_2648_, lean_object* v_info_2649_, lean_object* v_igs_u2081_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_){
_start:
{
lean_object* v_options_2656_; lean_object* v___x_2657_; uint8_t v___x_2658_; lean_object* v___y_2660_; 
v_options_2656_ = lean_ctor_get(v_a_2653_, 2);
v___x_2657_ = l___private_Lean_Widget_Diff_0__Lean_Widget_showTacticDiff;
v___x_2658_ = l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(v_options_2656_, v___x_2657_);
if (v___x_2658_ == 0)
{
lean_object* v___x_2692_; 
lean_dec_ref(v_info_2649_);
v___x_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2692_, 0, v_igs_u2081_2650_);
return v___x_2692_;
}
else
{
if (v_useAfter_2648_ == 0)
{
lean_object* v_goalsAfter_2693_; 
v_goalsAfter_2693_ = lean_ctor_get(v_info_2649_, 4);
lean_inc(v_goalsAfter_2693_);
v___y_2660_ = v_goalsAfter_2693_;
goto v___jp_2659_;
}
else
{
lean_object* v_goalsBefore_2694_; 
v_goalsBefore_2694_ = lean_ctor_get(v_info_2649_, 2);
lean_inc(v_goalsBefore_2694_);
v___y_2660_ = v_goalsBefore_2694_;
goto v___jp_2659_;
}
}
v___jp_2659_:
{
lean_object* v_goalsBefore_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v_goalsBefore_2661_ = lean_ctor_get(v_info_2649_, 2);
lean_inc(v_goalsBefore_2661_);
lean_dec_ref(v_info_2649_);
v___x_2662_ = lean_box(1);
v___x_2663_ = l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(v___x_2662_, v_goalsBefore_2661_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v_a_2664_; size_t v_sz_2665_; size_t v___x_2666_; lean_object* v___x_2667_; 
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
lean_inc(v_a_2664_);
lean_dec_ref(v___x_2663_);
v_sz_2665_ = lean_array_size(v_igs_u2081_2650_);
v___x_2666_ = ((size_t)0ULL);
v___x_2667_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__5(v_useAfter_2648_, v_a_2664_, v___y_2660_, v_useAfter_2648_, v___x_2658_, v_sz_2665_, v___x_2666_, v_igs_u2081_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2667_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2667_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
v_a_2676_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2667_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2667_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_dec(v___y_2660_);
lean_dec_ref(v_igs_u2081_2650_);
v_a_2684_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2663_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2663_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_diffInteractiveGoals___boxed(lean_object* v_useAfter_2695_, lean_object* v_info_2696_, lean_object* v_igs_u2081_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_){
_start:
{
uint8_t v_useAfter_boxed_2703_; lean_object* v_res_2704_; 
v_useAfter_boxed_2703_ = lean_unbox(v_useAfter_2695_);
v_res_2704_ = l_Lean_Widget_diffInteractiveGoals(v_useAfter_boxed_2703_, v_info_2696_, v_igs_u2081_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_);
lean_dec(v_a_2701_);
lean_dec_ref(v_a_2700_);
lean_dec(v_a_2699_);
lean_dec_ref(v_a_2698_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2(lean_object* v_00_u03b4_2705_, lean_object* v_t_2706_, lean_object* v_k_2707_){
_start:
{
lean_object* v___x_2708_; 
v___x_2708_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(v_t_2706_, v_k_2707_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___boxed(lean_object* v_00_u03b4_2709_, lean_object* v_t_2710_, lean_object* v_k_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2(v_00_u03b4_2709_, v_t_2710_, v_k_2711_);
lean_dec(v_k_2711_);
lean_dec(v_t_2710_);
return v_res_2712_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3(lean_object* v_00_u03b2_2713_, lean_object* v_k_2714_, lean_object* v_t_2715_){
_start:
{
uint8_t v___x_2716_; 
v___x_2716_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_k_2714_, v_t_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___boxed(lean_object* v_00_u03b2_2717_, lean_object* v_k_2718_, lean_object* v_t_2719_){
_start:
{
uint8_t v_res_2720_; lean_object* v_r_2721_; 
v_res_2720_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3(v_00_u03b2_2717_, v_k_2718_, v_t_2719_);
lean_dec(v_t_2719_);
lean_dec(v_k_2718_);
v_r_2721_ = lean_box(v_res_2720_);
return v_r_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4_spec__4(lean_object* v_00_u03b1_2722_, lean_object* v_lctx_2723_, lean_object* v_localInsts_2724_, lean_object* v_x_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v___x_2731_; 
v___x_2731_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4_spec__4___redArg(v_lctx_2723_, v_localInsts_2724_, v_x_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4_spec__4___boxed(lean_object* v_00_u03b1_2732_, lean_object* v_lctx_2733_, lean_object* v_localInsts_2734_, lean_object* v_x_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4_spec__4(v_00_u03b1_2732_, v_lctx_2733_, v_localInsts_2734_, v_x_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4(lean_object* v_00_u03b1_2742_, lean_object* v_goal_2743_, lean_object* v_action_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___redArg(v_goal_2743_, v_action_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4___boxed(lean_object* v_00_u03b1_2751_, lean_object* v_goal_2752_, lean_object* v_action_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__4(v_00_u03b1_2751_, v_goal_2752_, v_action_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
return v_res_2759_;
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
