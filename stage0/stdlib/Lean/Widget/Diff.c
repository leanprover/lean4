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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_SubExpr_Pos_pushNaryArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_SubExpr_Pos_pushNthBindingDomain(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Expr_getForallBodyMaxDepth(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_getFVarFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_pushNthBindingBody(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getForallBinderNames(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_pushBindingBody(lean_object*);
lean_object* l_Lean_SubExpr_Pos_pushBindingDomain(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_SubExpr_Pos_pushProj(lean_object*);
lean_object* l_Lean_MetavarContext_findDecl_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_LocalContext_sanitizeNames(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
extern lean_object* l_Lean_SubExpr_Pos_root;
lean_object* l_Lean_Widget_SubexprInfo_withDiffTag(uint8_t, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarIdSet_ofArray(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_toString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "showTacticDiff"};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(169, 112, 244, 47, 27, 57, 231, 91)}};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "When true, interactive goals for tactics will be decorated with diffing information. "};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__4_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__4_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__4_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__4_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__6_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__6_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__6_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__7_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__6_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__7_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__7_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__8_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Widget"};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__8_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__8_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__9_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__7_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__8_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(238, 115, 46, 200, 151, 151, 185, 65)}};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__9_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__9_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__10_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Diff"};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__10_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__10_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__11_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__9_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__10_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(236, 91, 159, 25, 73, 43, 233, 107)}};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__11_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__11_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__12_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__11_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(109, 1, 7, 240, 141, 39, 57, 92)}};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__12_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__12_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__13_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__12_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__6_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(216, 146, 105, 179, 45, 202, 141, 145)}};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__13_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__13_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__14_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__13_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__8_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(68, 86, 104, 123, 239, 160, 152, 136)}};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__14_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__14_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__15_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__14_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 44, 177, 75, 219, 90, 236, 185)}};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__15_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__15_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_showTacticDiff;
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "should not happen"};
static const lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__0 = (const lean_object*)&l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__0_value;
static lean_once_cell_t l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unknown goal "};
static const lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8(lean_object*, uint8_t, lean_object*, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7(uint8_t, lean_object*, lean_object*, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_diffInteractiveGoals(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_diffInteractiveGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_72_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_));
v___x_73_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_));
v___x_74_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__15_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_));
v___x_75_ = l_Lean_Option_register___at___00__private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__spec__0(v___x_72_, v___x_73_, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4____boxed(lean_object* v_a_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l___private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_();
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx___impl(uint8_t v_x_78_){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = lean_box(v_x_78_);
v___x_80_ = lean_obj_tag_nat(v___x_79_);
lean_dec(v___x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx___impl___boxed(lean_object* v_x_81_){
_start:
{
uint8_t v_x_4__boxed_82_; lean_object* v_res_83_; 
v_x_4__boxed_82_ = lean_unbox(v_x_81_);
v_res_83_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx___impl(v_x_4__boxed_82_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___redArg(lean_object* v_k_84_){
_start:
{
lean_inc(v_k_84_);
return v_k_84_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___redArg___boxed(lean_object* v_k_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___redArg(v_k_85_);
lean_dec(v_k_85_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim(lean_object* v_motive_87_, lean_object* v_ctorIdx_88_, uint8_t v_t_89_, lean_object* v_h_90_, lean_object* v_k_91_){
_start:
{
lean_inc(v_k_91_);
return v_k_91_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___boxed(lean_object* v_motive_92_, lean_object* v_ctorIdx_93_, lean_object* v_t_94_, lean_object* v_h_95_, lean_object* v_k_96_){
_start:
{
uint8_t v_t_boxed_97_; lean_object* v_res_98_; 
v_t_boxed_97_ = lean_unbox(v_t_94_);
v_res_98_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim(v_motive_92_, v_ctorIdx_93_, v_t_boxed_97_, v_h_95_, v_k_96_);
lean_dec(v_k_96_);
lean_dec(v_ctorIdx_93_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___redArg(lean_object* v_change_99_){
_start:
{
lean_inc(v_change_99_);
return v_change_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___redArg___boxed(lean_object* v_change_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___redArg(v_change_100_);
lean_dec(v_change_100_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim(lean_object* v_motive_102_, uint8_t v_t_103_, lean_object* v_h_104_, lean_object* v_change_105_){
_start:
{
lean_inc(v_change_105_);
return v_change_105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___boxed(lean_object* v_motive_106_, lean_object* v_t_107_, lean_object* v_h_108_, lean_object* v_change_109_){
_start:
{
uint8_t v_t_boxed_110_; lean_object* v_res_111_; 
v_t_boxed_110_ = lean_unbox(v_t_107_);
v_res_111_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim(v_motive_106_, v_t_boxed_110_, v_h_108_, v_change_109_);
lean_dec(v_change_109_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___redArg(lean_object* v_delete_112_){
_start:
{
lean_inc(v_delete_112_);
return v_delete_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___redArg___boxed(lean_object* v_delete_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___redArg(v_delete_113_);
lean_dec(v_delete_113_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim(lean_object* v_motive_115_, uint8_t v_t_116_, lean_object* v_h_117_, lean_object* v_delete_118_){
_start:
{
lean_inc(v_delete_118_);
return v_delete_118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___boxed(lean_object* v_motive_119_, lean_object* v_t_120_, lean_object* v_h_121_, lean_object* v_delete_122_){
_start:
{
uint8_t v_t_boxed_123_; lean_object* v_res_124_; 
v_t_boxed_123_ = lean_unbox(v_t_120_);
v_res_124_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim(v_motive_119_, v_t_boxed_123_, v_h_121_, v_delete_122_);
lean_dec(v_delete_122_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___redArg(lean_object* v_insert_125_){
_start:
{
lean_inc(v_insert_125_);
return v_insert_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___redArg___boxed(lean_object* v_insert_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___redArg(v_insert_126_);
lean_dec(v_insert_126_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim(lean_object* v_motive_128_, uint8_t v_t_129_, lean_object* v_h_130_, lean_object* v_insert_131_){
_start:
{
lean_inc(v_insert_131_);
return v_insert_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___boxed(lean_object* v_motive_132_, lean_object* v_t_133_, lean_object* v_h_134_, lean_object* v_insert_135_){
_start:
{
uint8_t v_t_boxed_136_; lean_object* v_res_137_; 
v_t_boxed_136_ = lean_unbox(v_t_133_);
v_res_137_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim(v_motive_132_, v_t_boxed_136_, v_h_134_, v_insert_135_);
lean_dec(v_insert_135_);
return v_res_137_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag(uint8_t v_x_138_, uint8_t v_x_139_){
_start:
{
if (v_x_138_ == 0)
{
switch(v_x_139_)
{
case 0:
{
uint8_t v___x_140_; 
v___x_140_ = 1;
return v___x_140_;
}
case 1:
{
uint8_t v___x_141_; 
v___x_141_ = 3;
return v___x_141_;
}
default: 
{
uint8_t v___x_142_; 
v___x_142_ = 5;
return v___x_142_;
}
}
}
else
{
switch(v_x_139_)
{
case 0:
{
uint8_t v___x_143_; 
v___x_143_ = 0;
return v___x_143_;
}
case 1:
{
uint8_t v___x_144_; 
v___x_144_ = 2;
return v___x_144_;
}
default: 
{
uint8_t v___x_145_; 
v___x_145_ = 4;
return v___x_145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag___boxed(lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
uint8_t v_x_49__boxed_148_; uint8_t v_x_50__boxed_149_; uint8_t v_res_150_; lean_object* v_r_151_; 
v_x_49__boxed_148_ = lean_unbox(v_x_146_);
v_x_50__boxed_149_ = lean_unbox(v_x_147_);
v_res_150_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag(v_x_49__boxed_148_, v_x_50__boxed_149_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString(uint8_t v_x_155_){
_start:
{
switch(v_x_155_)
{
case 0:
{
lean_object* v___x_156_; 
v___x_156_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__0));
return v___x_156_;
}
case 1:
{
lean_object* v___x_157_; 
v___x_157_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__1));
return v___x_157_;
}
default: 
{
lean_object* v___x_158_; 
v___x_158_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__2));
return v___x_158_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___boxed(lean_object* v_x_159_){
_start:
{
uint8_t v_x_31__boxed_160_; lean_object* v_res_161_; 
v_x_31__boxed_160_ = lean_unbox(v_x_159_);
v_res_161_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString(v_x_31__boxed_160_);
return v_res_161_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0(lean_object* v_x_167_, lean_object* v_y_168_){
_start:
{
uint8_t v___x_169_; 
v___x_169_ = lean_nat_dec_lt(v_x_167_, v_y_168_);
if (v___x_169_ == 0)
{
uint8_t v___x_170_; 
v___x_170_ = lean_nat_dec_eq(v_x_167_, v_y_168_);
if (v___x_170_ == 0)
{
uint8_t v___x_171_; 
v___x_171_ = 2;
return v___x_171_;
}
else
{
uint8_t v___x_172_; 
v___x_172_ = 1;
return v___x_172_;
}
}
else
{
uint8_t v___x_173_; 
v___x_173_ = 0;
return v___x_173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0___boxed(lean_object* v_x_174_, lean_object* v_y_175_){
_start:
{
uint8_t v_res_176_; lean_object* v_r_177_; 
v_res_176_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0(v_x_174_, v_y_175_);
lean_dec(v_y_175_);
lean_dec(v_x_174_);
v_r_177_ = lean_box(v_res_176_);
return v_r_177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1(uint8_t v_b_u2082_178_, lean_object* v_x_179_){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_box(v_b_u2082_178_);
v___x_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1___boxed(lean_object* v_b_u2082_182_, lean_object* v_x_183_){
_start:
{
uint8_t v_b_u2082_boxed_184_; lean_object* v_res_185_; 
v_b_u2082_boxed_184_ = lean_unbox(v_b_u2082_182_);
v_res_185_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1(v_b_u2082_boxed_184_, v_x_183_);
lean_dec(v_x_183_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2(lean_object* v___f_186_, lean_object* v_t_187_, lean_object* v_a_188_, uint8_t v_b_u2082_189_){
_start:
{
lean_object* v___x_190_; lean_object* v___f_191_; lean_object* v___x_192_; 
v___x_190_ = lean_box(v_b_u2082_189_);
v___f_191_ = lean_alloc_closure((void*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1___boxed), 2, 1);
lean_closure_set(v___f_191_, 0, v___x_190_);
v___x_192_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v___f_186_, v_a_188_, v___f_191_, v_t_187_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2___boxed(lean_object* v___f_193_, lean_object* v_t_194_, lean_object* v_a_195_, lean_object* v_b_u2082_196_){
_start:
{
uint8_t v_b_u2082_boxed_197_; lean_object* v_res_198_; 
v_b_u2082_boxed_197_ = lean_unbox(v_b_u2082_196_);
v_res_198_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2(v___f_193_, v_t_194_, v_a_195_, v_b_u2082_boxed_197_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__5(lean_object* v___f_199_, lean_object* v___f_200_, lean_object* v_a_201_, lean_object* v_b_202_){
_start:
{
lean_object* v_changesBefore_203_; lean_object* v_changesAfter_204_; lean_object* v_changesBefore_205_; lean_object* v_changesAfter_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_215_; 
v_changesBefore_203_ = lean_ctor_get(v_a_201_, 0);
lean_inc(v_changesBefore_203_);
v_changesAfter_204_ = lean_ctor_get(v_a_201_, 1);
lean_inc(v_changesAfter_204_);
lean_dec_ref(v_a_201_);
v_changesBefore_205_ = lean_ctor_get(v_b_202_, 0);
v_changesAfter_206_ = lean_ctor_get(v_b_202_, 1);
v_isSharedCheck_215_ = !lean_is_exclusive(v_b_202_);
if (v_isSharedCheck_215_ == 0)
{
v___x_208_ = v_b_202_;
v_isShared_209_ = v_isSharedCheck_215_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_changesAfter_206_);
lean_inc(v_changesBefore_205_);
lean_dec(v_b_202_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_215_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_210_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_199_, v_changesBefore_203_, v_changesBefore_205_);
v___x_211_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_200_, v_changesAfter_204_, v_changesAfter_206_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 1, v___x_211_);
lean_ctor_set(v___x_208_, 0, v___x_210_);
v___x_213_ = v___x_208_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_210_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0(lean_object* v_x_225_){
_start:
{
lean_object* v_fst_226_; lean_object* v_snd_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v_fst_226_ = lean_ctor_get(v_x_225_, 0);
v_snd_227_ = lean_ctor_get(v_x_225_, 1);
v___x_228_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__0));
v___x_229_ = l_Lean_SubExpr_Pos_toString(v_fst_226_);
v___x_230_ = lean_string_append(v___x_228_, v___x_229_);
lean_dec_ref(v___x_229_);
v___x_231_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__1));
v___x_232_ = lean_string_append(v___x_230_, v___x_231_);
v___x_233_ = lean_unbox(v_snd_227_);
v___x_234_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString(v___x_233_);
v___x_235_ = lean_string_append(v___x_232_, v___x_234_);
lean_dec_ref(v___x_234_);
v___x_236_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__2));
v___x_237_ = lean_string_append(v___x_235_, v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___boxed(lean_object* v_x_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0(v_x_238_);
lean_dec_ref(v_x_238_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1(lean_object* v_x1_240_, uint8_t v_x2_241_, lean_object* v_x3_242_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_243_ = lean_box(v_x2_241_);
v___x_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_244_, 0, v_x1_240_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v_x3_242_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1___boxed(lean_object* v_x1_246_, lean_object* v_x2_247_, lean_object* v_x3_248_){
_start:
{
uint8_t v_x2_245__boxed_249_; lean_object* v_res_250_; 
v_x2_245__boxed_249_ = lean_unbox(v_x2_247_);
v_res_250_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1(v_x1_246_, v_x2_245__boxed_249_, v_x3_248_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2(lean_object* v___f_270_, lean_object* v___f_271_, lean_object* v_p_272_){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_273_ = lean_box(0);
v___x_274_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__9));
v___x_275_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_274_, v___f_270_, v___x_273_, v_p_272_);
v___x_276_ = l_List_mapTR_loop___redArg(v___f_271_, v___x_275_, v___x_273_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3(lean_object* v_f_279_, lean_object* v___f_280_, lean_object* v_x_281_){
_start:
{
lean_object* v_changesBefore_282_; lean_object* v_changesAfter_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v_changesBefore_282_ = lean_ctor_get(v_x_281_, 0);
lean_inc(v_changesBefore_282_);
v_changesAfter_283_ = lean_ctor_get(v_x_281_, 1);
lean_inc(v_changesAfter_283_);
lean_dec_ref(v_x_281_);
v___x_284_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__0));
lean_inc_ref(v_f_279_);
v___x_285_ = lean_apply_1(v_f_279_, v_changesBefore_282_);
lean_inc_ref(v___f_280_);
v___x_286_ = l_List_toString___redArg(v___f_280_, v___x_285_);
v___x_287_ = lean_string_append(v___x_284_, v___x_286_);
lean_dec_ref(v___x_286_);
v___x_288_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__1));
v___x_289_ = lean_string_append(v___x_287_, v___x_288_);
v___x_290_ = lean_apply_1(v_f_279_, v_changesAfter_283_);
v___x_291_ = l_List_toString___redArg(v___f_280_, v___x_290_);
v___x_292_ = lean_string_append(v___x_289_, v___x_291_);
lean_dec_ref(v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(lean_object* v_k_303_, lean_object* v_v_304_, lean_object* v_t_305_){
_start:
{
if (lean_obj_tag(v_t_305_) == 0)
{
lean_object* v_size_306_; lean_object* v_k_307_; lean_object* v_v_308_; lean_object* v_l_309_; lean_object* v_r_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_591_; 
v_size_306_ = lean_ctor_get(v_t_305_, 0);
v_k_307_ = lean_ctor_get(v_t_305_, 1);
v_v_308_ = lean_ctor_get(v_t_305_, 2);
v_l_309_ = lean_ctor_get(v_t_305_, 3);
v_r_310_ = lean_ctor_get(v_t_305_, 4);
v_isSharedCheck_591_ = !lean_is_exclusive(v_t_305_);
if (v_isSharedCheck_591_ == 0)
{
v___x_312_ = v_t_305_;
v_isShared_313_ = v_isSharedCheck_591_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_r_310_);
lean_inc(v_l_309_);
lean_inc(v_v_308_);
lean_inc(v_k_307_);
lean_inc(v_size_306_);
lean_dec(v_t_305_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_591_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
uint8_t v___x_314_; 
v___x_314_ = lean_nat_dec_lt(v_k_303_, v_k_307_);
if (v___x_314_ == 0)
{
uint8_t v___x_315_; 
v___x_315_ = lean_nat_dec_eq(v_k_303_, v_k_307_);
if (v___x_315_ == 0)
{
lean_object* v_impl_316_; lean_object* v___x_317_; 
lean_dec(v_size_306_);
v_impl_316_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_k_303_, v_v_304_, v_r_310_);
v___x_317_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_309_) == 0)
{
lean_object* v_size_318_; lean_object* v_size_319_; lean_object* v_k_320_; lean_object* v_v_321_; lean_object* v_l_322_; lean_object* v_r_323_; lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v_size_318_ = lean_ctor_get(v_l_309_, 0);
v_size_319_ = lean_ctor_get(v_impl_316_, 0);
v_k_320_ = lean_ctor_get(v_impl_316_, 1);
v_v_321_ = lean_ctor_get(v_impl_316_, 2);
v_l_322_ = lean_ctor_get(v_impl_316_, 3);
lean_inc(v_l_322_);
v_r_323_ = lean_ctor_get(v_impl_316_, 4);
v___x_324_ = lean_unsigned_to_nat(3u);
v___x_325_ = lean_nat_mul(v___x_324_, v_size_318_);
v___x_326_ = lean_nat_dec_lt(v___x_325_, v_size_319_);
lean_dec(v___x_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_330_; 
lean_dec(v_l_322_);
v___x_327_ = lean_nat_add(v___x_317_, v_size_318_);
v___x_328_ = lean_nat_add(v___x_327_, v_size_319_);
lean_dec(v___x_327_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 4, v_impl_316_);
lean_ctor_set(v___x_312_, 0, v___x_328_);
v___x_330_ = v___x_312_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_328_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_k_307_);
lean_ctor_set(v_reuseFailAlloc_331_, 2, v_v_308_);
lean_ctor_set(v_reuseFailAlloc_331_, 3, v_l_309_);
lean_ctor_set(v_reuseFailAlloc_331_, 4, v_impl_316_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
else
{
lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_395_; 
lean_inc(v_r_323_);
lean_inc(v_v_321_);
lean_inc(v_k_320_);
lean_inc(v_size_319_);
v_isSharedCheck_395_ = !lean_is_exclusive(v_impl_316_);
if (v_isSharedCheck_395_ == 0)
{
lean_object* v_unused_396_; lean_object* v_unused_397_; lean_object* v_unused_398_; lean_object* v_unused_399_; lean_object* v_unused_400_; 
v_unused_396_ = lean_ctor_get(v_impl_316_, 4);
lean_dec(v_unused_396_);
v_unused_397_ = lean_ctor_get(v_impl_316_, 3);
lean_dec(v_unused_397_);
v_unused_398_ = lean_ctor_get(v_impl_316_, 2);
lean_dec(v_unused_398_);
v_unused_399_ = lean_ctor_get(v_impl_316_, 1);
lean_dec(v_unused_399_);
v_unused_400_ = lean_ctor_get(v_impl_316_, 0);
lean_dec(v_unused_400_);
v___x_333_ = v_impl_316_;
v_isShared_334_ = v_isSharedCheck_395_;
goto v_resetjp_332_;
}
else
{
lean_dec(v_impl_316_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_395_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v_size_335_; lean_object* v_k_336_; lean_object* v_v_337_; lean_object* v_l_338_; lean_object* v_r_339_; lean_object* v_size_340_; lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v_size_335_ = lean_ctor_get(v_l_322_, 0);
v_k_336_ = lean_ctor_get(v_l_322_, 1);
v_v_337_ = lean_ctor_get(v_l_322_, 2);
v_l_338_ = lean_ctor_get(v_l_322_, 3);
v_r_339_ = lean_ctor_get(v_l_322_, 4);
v_size_340_ = lean_ctor_get(v_r_323_, 0);
v___x_341_ = lean_unsigned_to_nat(2u);
v___x_342_ = lean_nat_mul(v___x_341_, v_size_340_);
v___x_343_ = lean_nat_dec_lt(v_size_335_, v___x_342_);
lean_dec(v___x_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_371_; 
lean_inc(v_r_339_);
lean_inc(v_l_338_);
lean_inc(v_v_337_);
lean_inc(v_k_336_);
v_isSharedCheck_371_ = !lean_is_exclusive(v_l_322_);
if (v_isSharedCheck_371_ == 0)
{
lean_object* v_unused_372_; lean_object* v_unused_373_; lean_object* v_unused_374_; lean_object* v_unused_375_; lean_object* v_unused_376_; 
v_unused_372_ = lean_ctor_get(v_l_322_, 4);
lean_dec(v_unused_372_);
v_unused_373_ = lean_ctor_get(v_l_322_, 3);
lean_dec(v_unused_373_);
v_unused_374_ = lean_ctor_get(v_l_322_, 2);
lean_dec(v_unused_374_);
v_unused_375_ = lean_ctor_get(v_l_322_, 1);
lean_dec(v_unused_375_);
v_unused_376_ = lean_ctor_get(v_l_322_, 0);
lean_dec(v_unused_376_);
v___x_345_ = v_l_322_;
v_isShared_346_ = v_isSharedCheck_371_;
goto v_resetjp_344_;
}
else
{
lean_dec(v_l_322_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_371_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v___y_352_; lean_object* v___y_361_; 
v___x_347_ = lean_nat_add(v___x_317_, v_size_318_);
v___x_348_ = lean_nat_add(v___x_347_, v_size_319_);
lean_dec(v_size_319_);
if (lean_obj_tag(v_l_338_) == 0)
{
lean_object* v_size_369_; 
v_size_369_ = lean_ctor_get(v_l_338_, 0);
lean_inc(v_size_369_);
v___y_361_ = v_size_369_;
goto v___jp_360_;
}
else
{
lean_object* v___x_370_; 
v___x_370_ = lean_unsigned_to_nat(0u);
v___y_361_ = v___x_370_;
goto v___jp_360_;
}
v___jp_349_:
{
lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_353_ = lean_nat_add(v___y_350_, v___y_352_);
lean_dec(v___y_352_);
lean_dec(v___y_350_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 4, v_r_323_);
lean_ctor_set(v___x_345_, 3, v_r_339_);
lean_ctor_set(v___x_345_, 2, v_v_321_);
lean_ctor_set(v___x_345_, 1, v_k_320_);
lean_ctor_set(v___x_345_, 0, v___x_353_);
v___x_355_ = v___x_345_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_353_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_k_320_);
lean_ctor_set(v_reuseFailAlloc_359_, 2, v_v_321_);
lean_ctor_set(v_reuseFailAlloc_359_, 3, v_r_339_);
lean_ctor_set(v_reuseFailAlloc_359_, 4, v_r_323_);
v___x_355_ = v_reuseFailAlloc_359_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
lean_object* v___x_357_; 
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 4, v___x_355_);
lean_ctor_set(v___x_333_, 3, v___y_351_);
lean_ctor_set(v___x_333_, 2, v_v_337_);
lean_ctor_set(v___x_333_, 1, v_k_336_);
lean_ctor_set(v___x_333_, 0, v___x_348_);
v___x_357_ = v___x_333_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_k_336_);
lean_ctor_set(v_reuseFailAlloc_358_, 2, v_v_337_);
lean_ctor_set(v_reuseFailAlloc_358_, 3, v___y_351_);
lean_ctor_set(v_reuseFailAlloc_358_, 4, v___x_355_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
v___jp_360_:
{
lean_object* v___x_362_; lean_object* v___x_364_; 
v___x_362_ = lean_nat_add(v___x_347_, v___y_361_);
lean_dec(v___y_361_);
lean_dec(v___x_347_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 4, v_l_338_);
lean_ctor_set(v___x_312_, 0, v___x_362_);
v___x_364_ = v___x_312_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_362_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_k_307_);
lean_ctor_set(v_reuseFailAlloc_368_, 2, v_v_308_);
lean_ctor_set(v_reuseFailAlloc_368_, 3, v_l_309_);
lean_ctor_set(v_reuseFailAlloc_368_, 4, v_l_338_);
v___x_364_ = v_reuseFailAlloc_368_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_365_; 
v___x_365_ = lean_nat_add(v___x_317_, v_size_340_);
if (lean_obj_tag(v_r_339_) == 0)
{
lean_object* v_size_366_; 
v_size_366_ = lean_ctor_get(v_r_339_, 0);
lean_inc(v_size_366_);
v___y_350_ = v___x_365_;
v___y_351_ = v___x_364_;
v___y_352_ = v_size_366_;
goto v___jp_349_;
}
else
{
lean_object* v___x_367_; 
v___x_367_ = lean_unsigned_to_nat(0u);
v___y_350_ = v___x_365_;
v___y_351_ = v___x_364_;
v___y_352_ = v___x_367_;
goto v___jp_349_;
}
}
}
}
}
else
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_381_; 
lean_del_object(v___x_312_);
v___x_377_ = lean_nat_add(v___x_317_, v_size_318_);
v___x_378_ = lean_nat_add(v___x_377_, v_size_319_);
lean_dec(v_size_319_);
v___x_379_ = lean_nat_add(v___x_377_, v_size_335_);
lean_dec(v___x_377_);
lean_inc_ref(v_l_309_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 4, v_l_322_);
lean_ctor_set(v___x_333_, 3, v_l_309_);
lean_ctor_set(v___x_333_, 2, v_v_308_);
lean_ctor_set(v___x_333_, 1, v_k_307_);
lean_ctor_set(v___x_333_, 0, v___x_379_);
v___x_381_ = v___x_333_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_379_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_k_307_);
lean_ctor_set(v_reuseFailAlloc_394_, 2, v_v_308_);
lean_ctor_set(v_reuseFailAlloc_394_, 3, v_l_309_);
lean_ctor_set(v_reuseFailAlloc_394_, 4, v_l_322_);
v___x_381_ = v_reuseFailAlloc_394_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
v_isSharedCheck_388_ = !lean_is_exclusive(v_l_309_);
if (v_isSharedCheck_388_ == 0)
{
lean_object* v_unused_389_; lean_object* v_unused_390_; lean_object* v_unused_391_; lean_object* v_unused_392_; lean_object* v_unused_393_; 
v_unused_389_ = lean_ctor_get(v_l_309_, 4);
lean_dec(v_unused_389_);
v_unused_390_ = lean_ctor_get(v_l_309_, 3);
lean_dec(v_unused_390_);
v_unused_391_ = lean_ctor_get(v_l_309_, 2);
lean_dec(v_unused_391_);
v_unused_392_ = lean_ctor_get(v_l_309_, 1);
lean_dec(v_unused_392_);
v_unused_393_ = lean_ctor_get(v_l_309_, 0);
lean_dec(v_unused_393_);
v___x_383_ = v_l_309_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_dec(v_l_309_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 4, v_r_323_);
lean_ctor_set(v___x_383_, 3, v___x_381_);
lean_ctor_set(v___x_383_, 2, v_v_321_);
lean_ctor_set(v___x_383_, 1, v_k_320_);
lean_ctor_set(v___x_383_, 0, v___x_378_);
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_378_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v_k_320_);
lean_ctor_set(v_reuseFailAlloc_387_, 2, v_v_321_);
lean_ctor_set(v_reuseFailAlloc_387_, 3, v___x_381_);
lean_ctor_set(v_reuseFailAlloc_387_, 4, v_r_323_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_401_; 
v_l_401_ = lean_ctor_get(v_impl_316_, 3);
lean_inc(v_l_401_);
if (lean_obj_tag(v_l_401_) == 0)
{
lean_object* v_r_402_; lean_object* v_k_403_; lean_object* v_v_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_427_; 
v_r_402_ = lean_ctor_get(v_impl_316_, 4);
v_k_403_ = lean_ctor_get(v_impl_316_, 1);
v_v_404_ = lean_ctor_get(v_impl_316_, 2);
v_isSharedCheck_427_ = !lean_is_exclusive(v_impl_316_);
if (v_isSharedCheck_427_ == 0)
{
lean_object* v_unused_428_; lean_object* v_unused_429_; 
v_unused_428_ = lean_ctor_get(v_impl_316_, 3);
lean_dec(v_unused_428_);
v_unused_429_ = lean_ctor_get(v_impl_316_, 0);
lean_dec(v_unused_429_);
v___x_406_ = v_impl_316_;
v_isShared_407_ = v_isSharedCheck_427_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_r_402_);
lean_inc(v_v_404_);
lean_inc(v_k_403_);
lean_dec(v_impl_316_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_427_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v_k_408_; lean_object* v_v_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_423_; 
v_k_408_ = lean_ctor_get(v_l_401_, 1);
v_v_409_ = lean_ctor_get(v_l_401_, 2);
v_isSharedCheck_423_ = !lean_is_exclusive(v_l_401_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; lean_object* v_unused_425_; lean_object* v_unused_426_; 
v_unused_424_ = lean_ctor_get(v_l_401_, 4);
lean_dec(v_unused_424_);
v_unused_425_ = lean_ctor_get(v_l_401_, 3);
lean_dec(v_unused_425_);
v_unused_426_ = lean_ctor_get(v_l_401_, 0);
lean_dec(v_unused_426_);
v___x_411_ = v_l_401_;
v_isShared_412_ = v_isSharedCheck_423_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_v_409_);
lean_inc(v_k_408_);
lean_dec(v_l_401_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_423_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_413_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_402_, 2);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 4, v_r_402_);
lean_ctor_set(v___x_411_, 3, v_r_402_);
lean_ctor_set(v___x_411_, 2, v_v_308_);
lean_ctor_set(v___x_411_, 1, v_k_307_);
lean_ctor_set(v___x_411_, 0, v___x_317_);
v___x_415_ = v___x_411_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_k_307_);
lean_ctor_set(v_reuseFailAlloc_422_, 2, v_v_308_);
lean_ctor_set(v_reuseFailAlloc_422_, 3, v_r_402_);
lean_ctor_set(v_reuseFailAlloc_422_, 4, v_r_402_);
v___x_415_ = v_reuseFailAlloc_422_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
lean_object* v___x_417_; 
lean_inc(v_r_402_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 3, v_r_402_);
lean_ctor_set(v___x_406_, 0, v___x_317_);
v___x_417_ = v___x_406_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_k_403_);
lean_ctor_set(v_reuseFailAlloc_421_, 2, v_v_404_);
lean_ctor_set(v_reuseFailAlloc_421_, 3, v_r_402_);
lean_ctor_set(v_reuseFailAlloc_421_, 4, v_r_402_);
v___x_417_ = v_reuseFailAlloc_421_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
lean_object* v___x_419_; 
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 4, v___x_417_);
lean_ctor_set(v___x_312_, 3, v___x_415_);
lean_ctor_set(v___x_312_, 2, v_v_409_);
lean_ctor_set(v___x_312_, 1, v_k_408_);
lean_ctor_set(v___x_312_, 0, v___x_413_);
v___x_419_ = v___x_312_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_413_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_k_408_);
lean_ctor_set(v_reuseFailAlloc_420_, 2, v_v_409_);
lean_ctor_set(v_reuseFailAlloc_420_, 3, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_420_, 4, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
}
}
else
{
lean_object* v_r_430_; 
v_r_430_ = lean_ctor_get(v_impl_316_, 4);
lean_inc(v_r_430_);
if (lean_obj_tag(v_r_430_) == 0)
{
lean_object* v_k_431_; lean_object* v_v_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_443_; 
v_k_431_ = lean_ctor_get(v_impl_316_, 1);
v_v_432_ = lean_ctor_get(v_impl_316_, 2);
v_isSharedCheck_443_ = !lean_is_exclusive(v_impl_316_);
if (v_isSharedCheck_443_ == 0)
{
lean_object* v_unused_444_; lean_object* v_unused_445_; lean_object* v_unused_446_; 
v_unused_444_ = lean_ctor_get(v_impl_316_, 4);
lean_dec(v_unused_444_);
v_unused_445_ = lean_ctor_get(v_impl_316_, 3);
lean_dec(v_unused_445_);
v_unused_446_ = lean_ctor_get(v_impl_316_, 0);
lean_dec(v_unused_446_);
v___x_434_ = v_impl_316_;
v_isShared_435_ = v_isSharedCheck_443_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_v_432_);
lean_inc(v_k_431_);
lean_dec(v_impl_316_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_443_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_436_ = lean_unsigned_to_nat(3u);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 4, v_l_401_);
lean_ctor_set(v___x_434_, 2, v_v_308_);
lean_ctor_set(v___x_434_, 1, v_k_307_);
lean_ctor_set(v___x_434_, 0, v___x_317_);
v___x_438_ = v___x_434_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_k_307_);
lean_ctor_set(v_reuseFailAlloc_442_, 2, v_v_308_);
lean_ctor_set(v_reuseFailAlloc_442_, 3, v_l_401_);
lean_ctor_set(v_reuseFailAlloc_442_, 4, v_l_401_);
v___x_438_ = v_reuseFailAlloc_442_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_440_; 
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 4, v_r_430_);
lean_ctor_set(v___x_312_, 3, v___x_438_);
lean_ctor_set(v___x_312_, 2, v_v_432_);
lean_ctor_set(v___x_312_, 1, v_k_431_);
lean_ctor_set(v___x_312_, 0, v___x_436_);
v___x_440_ = v___x_312_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_k_431_);
lean_ctor_set(v_reuseFailAlloc_441_, 2, v_v_432_);
lean_ctor_set(v_reuseFailAlloc_441_, 3, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_441_, 4, v_r_430_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
else
{
lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_447_ = lean_unsigned_to_nat(2u);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 4, v_impl_316_);
lean_ctor_set(v___x_312_, 3, v_r_430_);
lean_ctor_set(v___x_312_, 0, v___x_447_);
v___x_449_ = v___x_312_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_447_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v_k_307_);
lean_ctor_set(v_reuseFailAlloc_450_, 2, v_v_308_);
lean_ctor_set(v_reuseFailAlloc_450_, 3, v_r_430_);
lean_ctor_set(v_reuseFailAlloc_450_, 4, v_impl_316_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
}
else
{
lean_object* v___x_452_; 
lean_dec(v_v_308_);
lean_dec(v_k_307_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 2, v_v_304_);
lean_ctor_set(v___x_312_, 1, v_k_303_);
v___x_452_ = v___x_312_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_size_306_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_k_303_);
lean_ctor_set(v_reuseFailAlloc_453_, 2, v_v_304_);
lean_ctor_set(v_reuseFailAlloc_453_, 3, v_l_309_);
lean_ctor_set(v_reuseFailAlloc_453_, 4, v_r_310_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
else
{
lean_object* v_impl_454_; lean_object* v___x_455_; 
lean_dec(v_size_306_);
v_impl_454_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_k_303_, v_v_304_, v_l_309_);
v___x_455_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_310_) == 0)
{
lean_object* v_size_456_; lean_object* v_size_457_; lean_object* v_k_458_; lean_object* v_v_459_; lean_object* v_l_460_; lean_object* v_r_461_; lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
v_size_456_ = lean_ctor_get(v_r_310_, 0);
v_size_457_ = lean_ctor_get(v_impl_454_, 0);
v_k_458_ = lean_ctor_get(v_impl_454_, 1);
v_v_459_ = lean_ctor_get(v_impl_454_, 2);
v_l_460_ = lean_ctor_get(v_impl_454_, 3);
v_r_461_ = lean_ctor_get(v_impl_454_, 4);
lean_inc(v_r_461_);
v___x_462_ = lean_unsigned_to_nat(3u);
v___x_463_ = lean_nat_mul(v___x_462_, v_size_456_);
v___x_464_ = lean_nat_dec_lt(v___x_463_, v_size_457_);
lean_dec(v___x_463_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_468_; 
lean_dec(v_r_461_);
v___x_465_ = lean_nat_add(v___x_455_, v_size_457_);
v___x_466_ = lean_nat_add(v___x_465_, v_size_456_);
lean_dec(v___x_465_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 3, v_impl_454_);
lean_ctor_set(v___x_312_, 0, v___x_466_);
v___x_468_ = v___x_312_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_k_307_);
lean_ctor_set(v_reuseFailAlloc_469_, 2, v_v_308_);
lean_ctor_set(v_reuseFailAlloc_469_, 3, v_impl_454_);
lean_ctor_set(v_reuseFailAlloc_469_, 4, v_r_310_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
else
{
lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_535_; 
lean_inc(v_l_460_);
lean_inc(v_v_459_);
lean_inc(v_k_458_);
lean_inc(v_size_457_);
v_isSharedCheck_535_ = !lean_is_exclusive(v_impl_454_);
if (v_isSharedCheck_535_ == 0)
{
lean_object* v_unused_536_; lean_object* v_unused_537_; lean_object* v_unused_538_; lean_object* v_unused_539_; lean_object* v_unused_540_; 
v_unused_536_ = lean_ctor_get(v_impl_454_, 4);
lean_dec(v_unused_536_);
v_unused_537_ = lean_ctor_get(v_impl_454_, 3);
lean_dec(v_unused_537_);
v_unused_538_ = lean_ctor_get(v_impl_454_, 2);
lean_dec(v_unused_538_);
v_unused_539_ = lean_ctor_get(v_impl_454_, 1);
lean_dec(v_unused_539_);
v_unused_540_ = lean_ctor_get(v_impl_454_, 0);
lean_dec(v_unused_540_);
v___x_471_ = v_impl_454_;
v_isShared_472_ = v_isSharedCheck_535_;
goto v_resetjp_470_;
}
else
{
lean_dec(v_impl_454_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_535_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v_size_473_; lean_object* v_size_474_; lean_object* v_k_475_; lean_object* v_v_476_; lean_object* v_l_477_; lean_object* v_r_478_; lean_object* v___x_479_; lean_object* v___x_480_; uint8_t v___x_481_; 
v_size_473_ = lean_ctor_get(v_l_460_, 0);
v_size_474_ = lean_ctor_get(v_r_461_, 0);
v_k_475_ = lean_ctor_get(v_r_461_, 1);
v_v_476_ = lean_ctor_get(v_r_461_, 2);
v_l_477_ = lean_ctor_get(v_r_461_, 3);
v_r_478_ = lean_ctor_get(v_r_461_, 4);
v___x_479_ = lean_unsigned_to_nat(2u);
v___x_480_ = lean_nat_mul(v___x_479_, v_size_473_);
v___x_481_ = lean_nat_dec_lt(v_size_474_, v___x_480_);
lean_dec(v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_510_; 
lean_inc(v_r_478_);
lean_inc(v_l_477_);
lean_inc(v_v_476_);
lean_inc(v_k_475_);
v_isSharedCheck_510_ = !lean_is_exclusive(v_r_461_);
if (v_isSharedCheck_510_ == 0)
{
lean_object* v_unused_511_; lean_object* v_unused_512_; lean_object* v_unused_513_; lean_object* v_unused_514_; lean_object* v_unused_515_; 
v_unused_511_ = lean_ctor_get(v_r_461_, 4);
lean_dec(v_unused_511_);
v_unused_512_ = lean_ctor_get(v_r_461_, 3);
lean_dec(v_unused_512_);
v_unused_513_ = lean_ctor_get(v_r_461_, 2);
lean_dec(v_unused_513_);
v_unused_514_ = lean_ctor_get(v_r_461_, 1);
lean_dec(v_unused_514_);
v_unused_515_ = lean_ctor_get(v_r_461_, 0);
lean_dec(v_unused_515_);
v___x_483_ = v_r_461_;
v_isShared_484_ = v_isSharedCheck_510_;
goto v_resetjp_482_;
}
else
{
lean_dec(v_r_461_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_510_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___x_498_; lean_object* v___y_500_; 
v___x_485_ = lean_nat_add(v___x_455_, v_size_457_);
lean_dec(v_size_457_);
v___x_486_ = lean_nat_add(v___x_485_, v_size_456_);
lean_dec(v___x_485_);
v___x_498_ = lean_nat_add(v___x_455_, v_size_473_);
if (lean_obj_tag(v_l_477_) == 0)
{
lean_object* v_size_508_; 
v_size_508_ = lean_ctor_get(v_l_477_, 0);
lean_inc(v_size_508_);
v___y_500_ = v_size_508_;
goto v___jp_499_;
}
else
{
lean_object* v___x_509_; 
v___x_509_ = lean_unsigned_to_nat(0u);
v___y_500_ = v___x_509_;
goto v___jp_499_;
}
v___jp_487_:
{
lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_491_ = lean_nat_add(v___y_488_, v___y_490_);
lean_dec(v___y_490_);
lean_dec(v___y_488_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 4, v_r_310_);
lean_ctor_set(v___x_483_, 3, v_r_478_);
lean_ctor_set(v___x_483_, 2, v_v_308_);
lean_ctor_set(v___x_483_, 1, v_k_307_);
lean_ctor_set(v___x_483_, 0, v___x_491_);
v___x_493_ = v___x_483_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_491_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v_k_307_);
lean_ctor_set(v_reuseFailAlloc_497_, 2, v_v_308_);
lean_ctor_set(v_reuseFailAlloc_497_, 3, v_r_478_);
lean_ctor_set(v_reuseFailAlloc_497_, 4, v_r_310_);
v___x_493_ = v_reuseFailAlloc_497_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
lean_object* v___x_495_; 
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 4, v___x_493_);
lean_ctor_set(v___x_471_, 3, v___y_489_);
lean_ctor_set(v___x_471_, 2, v_v_476_);
lean_ctor_set(v___x_471_, 1, v_k_475_);
lean_ctor_set(v___x_471_, 0, v___x_486_);
v___x_495_ = v___x_471_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_k_475_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v_v_476_);
lean_ctor_set(v_reuseFailAlloc_496_, 3, v___y_489_);
lean_ctor_set(v_reuseFailAlloc_496_, 4, v___x_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
v___jp_499_:
{
lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_501_ = lean_nat_add(v___x_498_, v___y_500_);
lean_dec(v___y_500_);
lean_dec(v___x_498_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 4, v_l_477_);
lean_ctor_set(v___x_312_, 3, v_l_460_);
lean_ctor_set(v___x_312_, 2, v_v_459_);
lean_ctor_set(v___x_312_, 1, v_k_458_);
lean_ctor_set(v___x_312_, 0, v___x_501_);
v___x_503_ = v___x_312_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_k_458_);
lean_ctor_set(v_reuseFailAlloc_507_, 2, v_v_459_);
lean_ctor_set(v_reuseFailAlloc_507_, 3, v_l_460_);
lean_ctor_set(v_reuseFailAlloc_507_, 4, v_l_477_);
v___x_503_ = v_reuseFailAlloc_507_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_504_; 
v___x_504_ = lean_nat_add(v___x_455_, v_size_456_);
if (lean_obj_tag(v_r_478_) == 0)
{
lean_object* v_size_505_; 
v_size_505_ = lean_ctor_get(v_r_478_, 0);
lean_inc(v_size_505_);
v___y_488_ = v___x_504_;
v___y_489_ = v___x_503_;
v___y_490_ = v_size_505_;
goto v___jp_487_;
}
else
{
lean_object* v___x_506_; 
v___x_506_ = lean_unsigned_to_nat(0u);
v___y_488_ = v___x_504_;
v___y_489_ = v___x_503_;
v___y_490_ = v___x_506_;
goto v___jp_487_;
}
}
}
}
}
else
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_521_; 
lean_del_object(v___x_312_);
v___x_516_ = lean_nat_add(v___x_455_, v_size_457_);
lean_dec(v_size_457_);
v___x_517_ = lean_nat_add(v___x_516_, v_size_456_);
lean_dec(v___x_516_);
v___x_518_ = lean_nat_add(v___x_455_, v_size_456_);
v___x_519_ = lean_nat_add(v___x_518_, v_size_474_);
lean_dec(v___x_518_);
lean_inc_ref(v_r_310_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 4, v_r_310_);
lean_ctor_set(v___x_471_, 3, v_r_461_);
lean_ctor_set(v___x_471_, 2, v_v_308_);
lean_ctor_set(v___x_471_, 1, v_k_307_);
lean_ctor_set(v___x_471_, 0, v___x_519_);
v___x_521_ = v___x_471_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_519_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v_k_307_);
lean_ctor_set(v_reuseFailAlloc_534_, 2, v_v_308_);
lean_ctor_set(v_reuseFailAlloc_534_, 3, v_r_461_);
lean_ctor_set(v_reuseFailAlloc_534_, 4, v_r_310_);
v___x_521_ = v_reuseFailAlloc_534_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
v_isSharedCheck_528_ = !lean_is_exclusive(v_r_310_);
if (v_isSharedCheck_528_ == 0)
{
lean_object* v_unused_529_; lean_object* v_unused_530_; lean_object* v_unused_531_; lean_object* v_unused_532_; lean_object* v_unused_533_; 
v_unused_529_ = lean_ctor_get(v_r_310_, 4);
lean_dec(v_unused_529_);
v_unused_530_ = lean_ctor_get(v_r_310_, 3);
lean_dec(v_unused_530_);
v_unused_531_ = lean_ctor_get(v_r_310_, 2);
lean_dec(v_unused_531_);
v_unused_532_ = lean_ctor_get(v_r_310_, 1);
lean_dec(v_unused_532_);
v_unused_533_ = lean_ctor_get(v_r_310_, 0);
lean_dec(v_unused_533_);
v___x_523_ = v_r_310_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_dec(v_r_310_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 4, v___x_521_);
lean_ctor_set(v___x_523_, 3, v_l_460_);
lean_ctor_set(v___x_523_, 2, v_v_459_);
lean_ctor_set(v___x_523_, 1, v_k_458_);
lean_ctor_set(v___x_523_, 0, v___x_517_);
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_k_458_);
lean_ctor_set(v_reuseFailAlloc_527_, 2, v_v_459_);
lean_ctor_set(v_reuseFailAlloc_527_, 3, v_l_460_);
lean_ctor_set(v_reuseFailAlloc_527_, 4, v___x_521_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_541_; 
v_l_541_ = lean_ctor_get(v_impl_454_, 3);
if (lean_obj_tag(v_l_541_) == 0)
{
lean_object* v_r_542_; lean_object* v_k_543_; lean_object* v_v_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_555_; 
lean_inc_ref(v_l_541_);
v_r_542_ = lean_ctor_get(v_impl_454_, 4);
v_k_543_ = lean_ctor_get(v_impl_454_, 1);
v_v_544_ = lean_ctor_get(v_impl_454_, 2);
v_isSharedCheck_555_ = !lean_is_exclusive(v_impl_454_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; lean_object* v_unused_557_; 
v_unused_556_ = lean_ctor_get(v_impl_454_, 3);
lean_dec(v_unused_556_);
v_unused_557_ = lean_ctor_get(v_impl_454_, 0);
lean_dec(v_unused_557_);
v___x_546_ = v_impl_454_;
v_isShared_547_ = v_isSharedCheck_555_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_r_542_);
lean_inc(v_v_544_);
lean_inc(v_k_543_);
lean_dec(v_impl_454_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_555_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_548_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_542_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 3, v_r_542_);
lean_ctor_set(v___x_546_, 2, v_v_308_);
lean_ctor_set(v___x_546_, 1, v_k_307_);
lean_ctor_set(v___x_546_, 0, v___x_455_);
v___x_550_ = v___x_546_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_455_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_k_307_);
lean_ctor_set(v_reuseFailAlloc_554_, 2, v_v_308_);
lean_ctor_set(v_reuseFailAlloc_554_, 3, v_r_542_);
lean_ctor_set(v_reuseFailAlloc_554_, 4, v_r_542_);
v___x_550_ = v_reuseFailAlloc_554_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_552_; 
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 4, v___x_550_);
lean_ctor_set(v___x_312_, 3, v_l_541_);
lean_ctor_set(v___x_312_, 2, v_v_544_);
lean_ctor_set(v___x_312_, 1, v_k_543_);
lean_ctor_set(v___x_312_, 0, v___x_548_);
v___x_552_ = v___x_312_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_k_543_);
lean_ctor_set(v_reuseFailAlloc_553_, 2, v_v_544_);
lean_ctor_set(v_reuseFailAlloc_553_, 3, v_l_541_);
lean_ctor_set(v_reuseFailAlloc_553_, 4, v___x_550_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
else
{
lean_object* v_r_558_; 
v_r_558_ = lean_ctor_get(v_impl_454_, 4);
lean_inc(v_r_558_);
if (lean_obj_tag(v_r_558_) == 0)
{
lean_object* v_k_559_; lean_object* v_v_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_583_; 
lean_inc(v_l_541_);
v_k_559_ = lean_ctor_get(v_impl_454_, 1);
v_v_560_ = lean_ctor_get(v_impl_454_, 2);
v_isSharedCheck_583_ = !lean_is_exclusive(v_impl_454_);
if (v_isSharedCheck_583_ == 0)
{
lean_object* v_unused_584_; lean_object* v_unused_585_; lean_object* v_unused_586_; 
v_unused_584_ = lean_ctor_get(v_impl_454_, 4);
lean_dec(v_unused_584_);
v_unused_585_ = lean_ctor_get(v_impl_454_, 3);
lean_dec(v_unused_585_);
v_unused_586_ = lean_ctor_get(v_impl_454_, 0);
lean_dec(v_unused_586_);
v___x_562_ = v_impl_454_;
v_isShared_563_ = v_isSharedCheck_583_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_v_560_);
lean_inc(v_k_559_);
lean_dec(v_impl_454_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_583_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v_k_564_; lean_object* v_v_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_579_; 
v_k_564_ = lean_ctor_get(v_r_558_, 1);
v_v_565_ = lean_ctor_get(v_r_558_, 2);
v_isSharedCheck_579_ = !lean_is_exclusive(v_r_558_);
if (v_isSharedCheck_579_ == 0)
{
lean_object* v_unused_580_; lean_object* v_unused_581_; lean_object* v_unused_582_; 
v_unused_580_ = lean_ctor_get(v_r_558_, 4);
lean_dec(v_unused_580_);
v_unused_581_ = lean_ctor_get(v_r_558_, 3);
lean_dec(v_unused_581_);
v_unused_582_ = lean_ctor_get(v_r_558_, 0);
lean_dec(v_unused_582_);
v___x_567_ = v_r_558_;
v_isShared_568_ = v_isSharedCheck_579_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_v_565_);
lean_inc(v_k_564_);
lean_dec(v_r_558_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_579_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v___x_571_; 
v___x_569_ = lean_unsigned_to_nat(3u);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 4, v_l_541_);
lean_ctor_set(v___x_567_, 3, v_l_541_);
lean_ctor_set(v___x_567_, 2, v_v_560_);
lean_ctor_set(v___x_567_, 1, v_k_559_);
lean_ctor_set(v___x_567_, 0, v___x_455_);
v___x_571_ = v___x_567_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_455_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_k_559_);
lean_ctor_set(v_reuseFailAlloc_578_, 2, v_v_560_);
lean_ctor_set(v_reuseFailAlloc_578_, 3, v_l_541_);
lean_ctor_set(v_reuseFailAlloc_578_, 4, v_l_541_);
v___x_571_ = v_reuseFailAlloc_578_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
lean_object* v___x_573_; 
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 4, v_l_541_);
lean_ctor_set(v___x_562_, 2, v_v_308_);
lean_ctor_set(v___x_562_, 1, v_k_307_);
lean_ctor_set(v___x_562_, 0, v___x_455_);
v___x_573_ = v___x_562_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_455_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v_k_307_);
lean_ctor_set(v_reuseFailAlloc_577_, 2, v_v_308_);
lean_ctor_set(v_reuseFailAlloc_577_, 3, v_l_541_);
lean_ctor_set(v_reuseFailAlloc_577_, 4, v_l_541_);
v___x_573_ = v_reuseFailAlloc_577_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
lean_object* v___x_575_; 
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 4, v___x_573_);
lean_ctor_set(v___x_312_, 3, v___x_571_);
lean_ctor_set(v___x_312_, 2, v_v_565_);
lean_ctor_set(v___x_312_, 1, v_k_564_);
lean_ctor_set(v___x_312_, 0, v___x_569_);
v___x_575_ = v___x_312_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_k_564_);
lean_ctor_set(v_reuseFailAlloc_576_, 2, v_v_565_);
lean_ctor_set(v_reuseFailAlloc_576_, 3, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_576_, 4, v___x_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
}
}
else
{
lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_587_ = lean_unsigned_to_nat(2u);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 4, v_r_558_);
lean_ctor_set(v___x_312_, 3, v_impl_454_);
lean_ctor_set(v___x_312_, 0, v___x_587_);
v___x_589_ = v___x_312_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_k_307_);
lean_ctor_set(v_reuseFailAlloc_590_, 2, v_v_308_);
lean_ctor_set(v_reuseFailAlloc_590_, 3, v_impl_454_);
lean_ctor_set(v_reuseFailAlloc_590_, 4, v_r_558_);
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
}
}
}
else
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_unsigned_to_nat(1u);
v___x_593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set(v___x_593_, 1, v_k_303_);
lean_ctor_set(v___x_593_, 2, v_v_304_);
lean_ctor_set(v___x_593_, 3, v_t_305_);
lean_ctor_set(v___x_593_, 4, v_t_305_);
return v___x_593_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange(lean_object* v_p_594_, uint8_t v_d_595_, lean_object* v_00_u03b4_596_){
_start:
{
lean_object* v_changesBefore_597_; lean_object* v_changesAfter_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_607_; 
v_changesBefore_597_ = lean_ctor_get(v_00_u03b4_596_, 0);
v_changesAfter_598_ = lean_ctor_get(v_00_u03b4_596_, 1);
v_isSharedCheck_607_ = !lean_is_exclusive(v_00_u03b4_596_);
if (v_isSharedCheck_607_ == 0)
{
v___x_600_ = v_00_u03b4_596_;
v_isShared_601_ = v_isSharedCheck_607_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_changesAfter_598_);
lean_inc(v_changesBefore_597_);
lean_dec(v_00_u03b4_596_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_607_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_602_ = lean_box(v_d_595_);
v___x_603_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_p_594_, v___x_602_, v_changesBefore_597_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v___x_603_);
v___x_605_ = v___x_600_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_changesAfter_598_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange___boxed(lean_object* v_p_608_, lean_object* v_d_609_, lean_object* v_00_u03b4_610_){
_start:
{
uint8_t v_d_boxed_611_; lean_object* v_res_612_; 
v_d_boxed_611_ = lean_unbox(v_d_609_);
v_res_612_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange(v_p_608_, v_d_boxed_611_, v_00_u03b4_610_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0(lean_object* v_00_u03b2_613_, lean_object* v_k_614_, lean_object* v_v_615_, lean_object* v_t_616_, lean_object* v_hl_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_k_614_, v_v_615_, v_t_616_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertAfterChange(lean_object* v_p_619_, uint8_t v_d_620_, lean_object* v_00_u03b4_621_){
_start:
{
lean_object* v_changesBefore_622_; lean_object* v_changesAfter_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_632_; 
v_changesBefore_622_ = lean_ctor_get(v_00_u03b4_621_, 0);
v_changesAfter_623_ = lean_ctor_get(v_00_u03b4_621_, 1);
v_isSharedCheck_632_ = !lean_is_exclusive(v_00_u03b4_621_);
if (v_isSharedCheck_632_ == 0)
{
v___x_625_ = v_00_u03b4_621_;
v_isShared_626_ = v_isSharedCheck_632_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_changesAfter_623_);
lean_inc(v_changesBefore_622_);
lean_dec(v_00_u03b4_621_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_632_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_630_; 
v___x_627_ = lean_box(v_d_620_);
v___x_628_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_p_619_, v___x_627_, v_changesAfter_623_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v___x_628_);
v___x_630_ = v___x_625_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_changesBefore_622_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v___x_628_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertAfterChange___boxed(lean_object* v_p_633_, lean_object* v_d_634_, lean_object* v_00_u03b4_635_){
_start:
{
uint8_t v_d_boxed_636_; lean_object* v_res_637_; 
v_d_boxed_636_ = lean_unbox(v_d_634_);
v_res_637_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertAfterChange(v_p_633_, v_d_boxed_636_, v_00_u03b4_635_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(lean_object* v_before_638_, lean_object* v_after_639_, uint8_t v_d_640_){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_641_ = lean_box(1);
v___x_642_ = lean_box(v_d_640_);
v___x_643_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_before_638_, v___x_642_, v___x_641_);
v___x_644_ = lean_box(v_d_640_);
v___x_645_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_after_639_, v___x_644_, v___x_641_);
v___x_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_643_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos___boxed(lean_object* v_before_647_, lean_object* v_after_648_, lean_object* v_d_649_){
_start:
{
uint8_t v_d_boxed_650_; lean_object* v_res_651_; 
v_d_boxed_650_ = lean_unbox(v_d_649_);
v_res_651_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v_before_647_, v_after_648_, v_d_boxed_650_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(lean_object* v_before_652_, lean_object* v_after_653_, uint8_t v_d_654_){
_start:
{
lean_object* v_pos_655_; lean_object* v_pos_656_; lean_object* v___x_657_; 
v_pos_655_ = lean_ctor_get(v_before_652_, 1);
lean_inc(v_pos_655_);
lean_dec_ref(v_before_652_);
v_pos_656_ = lean_ctor_get(v_after_653_, 1);
lean_inc(v_pos_656_);
lean_dec_ref(v_after_653_);
v___x_657_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v_pos_655_, v_pos_656_, v_d_654_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange___boxed(lean_object* v_before_658_, lean_object* v_after_659_, lean_object* v_d_660_){
_start:
{
uint8_t v_d_boxed_661_; lean_object* v_res_662_; 
v_d_boxed_661_ = lean_unbox(v_d_660_);
v_res_662_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_658_, v_after_659_, v_d_boxed_661_);
return v_res_662_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(lean_object* v_d_663_){
_start:
{
lean_object* v_changesAfter_664_; 
v_changesAfter_664_ = lean_ctor_get(v_d_663_, 1);
if (lean_obj_tag(v_changesAfter_664_) == 0)
{
uint8_t v___x_665_; 
v___x_665_ = 0;
return v___x_665_;
}
else
{
lean_object* v_changesBefore_666_; 
v_changesBefore_666_ = lean_ctor_get(v_d_663_, 0);
if (lean_obj_tag(v_changesBefore_666_) == 0)
{
uint8_t v___x_667_; 
v___x_667_ = 0;
return v___x_667_;
}
else
{
uint8_t v___x_668_; 
v___x_668_ = 1;
return v___x_668_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty___boxed(lean_object* v_d_669_){
_start:
{
uint8_t v_res_670_; lean_object* v_r_671_; 
v_res_670_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_d_669_);
lean_dec_ref(v_d_669_);
v_r_671_ = lean_box(v_res_670_);
return v_r_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0(lean_object* v_k_672_, lean_object* v_b_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v___x_679_; 
lean_inc(v___y_677_);
lean_inc_ref(v___y_676_);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
v___x_679_ = lean_apply_6(v_k_672_, v_b_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, lean_box(0));
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0___boxed(lean_object* v_k_680_, lean_object* v_b_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0(v_k_680_, v_b_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(lean_object* v_name_688_, uint8_t v_bi_689_, lean_object* v_type_690_, lean_object* v_k_691_, uint8_t v_kind_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v___f_698_; lean_object* v___x_699_; 
v___f_698_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_698_, 0, v_k_691_);
v___x_699_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_688_, v_bi_689_, v_type_690_, v___f_698_, v_kind_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
v_a_708_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_699_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_699_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___boxed(lean_object* v_name_716_, lean_object* v_bi_717_, lean_object* v_type_718_, lean_object* v_k_719_, lean_object* v_kind_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
uint8_t v_bi_boxed_726_; uint8_t v_kind_boxed_727_; lean_object* v_res_728_; 
v_bi_boxed_726_ = lean_unbox(v_bi_717_);
v_kind_boxed_727_ = lean_unbox(v_kind_720_);
v_res_728_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_name_716_, v_bi_boxed_726_, v_type_718_, v_k_719_, v_kind_boxed_727_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6(lean_object* v_00_u03b1_729_, lean_object* v_name_730_, uint8_t v_bi_731_, lean_object* v_type_732_, lean_object* v_k_733_, uint8_t v_kind_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_name_730_, v_bi_731_, v_type_732_, v_k_733_, v_kind_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___boxed(lean_object* v_00_u03b1_741_, lean_object* v_name_742_, lean_object* v_bi_743_, lean_object* v_type_744_, lean_object* v_k_745_, lean_object* v_kind_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
uint8_t v_bi_boxed_752_; uint8_t v_kind_boxed_753_; lean_object* v_res_754_; 
v_bi_boxed_752_ = lean_unbox(v_bi_743_);
v_kind_boxed_753_ = lean_unbox(v_kind_746_);
v_res_754_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6(v_00_u03b1_741_, v_name_742_, v_bi_boxed_752_, v_type_744_, v_k_745_, v_kind_boxed_753_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(lean_object* v_msgData_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v___x_761_; lean_object* v_env_762_; uint8_t v___x_763_; lean_object* v_env_764_; lean_object* v___x_765_; lean_object* v_toCold_766_; lean_object* v_mctx_767_; lean_object* v_lctx_768_; lean_object* v_options_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_761_ = lean_st_ref_get(v___y_759_);
v_env_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc_ref(v_env_762_);
lean_dec(v___x_761_);
v___x_763_ = 0;
v_env_764_ = l_Lean_Environment_setRecordingDeps(v_env_762_, v___x_763_);
v___x_765_ = lean_st_ref_get(v___y_757_);
v_toCold_766_ = lean_ctor_get(v___y_758_, 0);
v_mctx_767_ = lean_ctor_get(v___x_765_, 0);
lean_inc_ref(v_mctx_767_);
lean_dec(v___x_765_);
v_lctx_768_ = lean_ctor_get(v___y_756_, 2);
v_options_769_ = lean_ctor_get(v_toCold_766_, 2);
lean_inc_ref(v_options_769_);
lean_inc_ref(v_lctx_768_);
v___x_770_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_770_, 0, v_env_764_);
lean_ctor_set(v___x_770_, 1, v_mctx_767_);
lean_ctor_set(v___x_770_, 2, v_lctx_768_);
lean_ctor_set(v___x_770_, 3, v_options_769_);
v___x_771_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
lean_ctor_set(v___x_771_, 1, v_msgData_755_);
v___x_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4___boxed(lean_object* v_msgData_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(v_msgData_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(lean_object* v_msg_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_ref_786_; lean_object* v___x_787_; lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_796_; 
v_ref_786_ = lean_ctor_get(v___y_783_, 2);
v___x_787_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(v_msg_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
v_a_788_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_796_ == 0)
{
v___x_790_ = v___x_787_;
v_isShared_791_ = v_isSharedCheck_796_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_787_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_796_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_794_; 
lean_inc(v_ref_786_);
v___x_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_792_, 0, v_ref_786_);
lean_ctor_set(v___x_792_, 1, v_a_788_);
if (v_isShared_791_ == 0)
{
lean_ctor_set_tag(v___x_790_, 1);
lean_ctor_set(v___x_790_, 0, v___x_792_);
v___x_794_ = v___x_790_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg___boxed(lean_object* v_msg_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v_msg_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(lean_object* v_x_804_, lean_object* v_x_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
if (lean_obj_tag(v_x_804_) == 0)
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = l_List_reverse___redArg(v_x_805_);
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
return v___x_812_;
}
else
{
lean_object* v_head_813_; lean_object* v_tail_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_832_; 
v_head_813_ = lean_ctor_get(v_x_804_, 0);
v_tail_814_ = lean_ctor_get(v_x_804_, 1);
v_isSharedCheck_832_ = !lean_is_exclusive(v_x_804_);
if (v_isSharedCheck_832_ == 0)
{
v___x_816_ = v_x_804_;
v_isShared_817_ = v_isSharedCheck_832_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_tail_814_);
lean_inc(v_head_813_);
lean_dec(v_x_804_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_832_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_818_; 
v___x_818_ = l_Lean_Meta_getFVarFromUserName(v_head_813_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_821_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_819_);
lean_dec_ref_known(v___x_818_, 1);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 1, v_x_805_);
lean_ctor_set(v___x_816_, 0, v_a_819_);
v___x_821_ = v___x_816_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_819_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_x_805_);
v___x_821_ = v_reuseFailAlloc_823_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
v_x_804_ = v_tail_814_;
v_x_805_ = v___x_821_;
goto _start;
}
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
lean_del_object(v___x_816_);
lean_dec(v_tail_814_);
lean_dec(v_x_805_);
v_a_824_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_818_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_818_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2___boxed(lean_object* v_x_833_, lean_object* v_x_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(v_x_833_, v_x_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(lean_object* v_upperBound_841_, lean_object* v_before_842_, lean_object* v_a_843_, lean_object* v_b_844_){
_start:
{
uint8_t v___x_846_; 
v___x_846_ = lean_nat_dec_lt(v_a_843_, v_upperBound_841_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; 
lean_dec(v_a_843_);
lean_dec_ref(v_before_842_);
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v_b_844_);
return v___x_847_;
}
else
{
lean_object* v_pos_848_; lean_object* v___x_849_; uint8_t v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v_pos_848_ = lean_ctor_get(v_before_842_, 1);
lean_inc(v_pos_848_);
lean_inc(v_a_843_);
v___x_849_ = l_Lean_SubExpr_Pos_pushNthBindingDomain(v_a_843_, v_pos_848_);
v___x_850_ = 1;
v___x_851_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange(v___x_849_, v___x_850_, v_b_844_);
v___x_852_ = lean_unsigned_to_nat(1u);
v___x_853_ = lean_nat_add(v_a_843_, v___x_852_);
lean_dec(v_a_843_);
v_a_843_ = v___x_853_;
v_b_844_ = v___x_851_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg___boxed(lean_object* v_upperBound_855_, lean_object* v_before_856_, lean_object* v_a_857_, lean_object* v_b_858_, lean_object* v___y_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v_upperBound_855_, v_before_856_, v_a_857_, v_b_858_);
lean_dec(v_upperBound_855_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0(lean_object* v_x_861_, lean_object* v_x_862_){
_start:
{
if (lean_obj_tag(v_x_861_) == 0)
{
lean_object* v___x_863_; 
v___x_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_863_, 0, v_x_862_);
return v___x_863_;
}
else
{
if (lean_obj_tag(v_x_862_) == 0)
{
lean_object* v___x_864_; 
v___x_864_ = lean_box(0);
return v___x_864_;
}
else
{
lean_object* v_head_865_; lean_object* v_tail_866_; lean_object* v_head_867_; lean_object* v_tail_868_; uint8_t v___x_869_; 
v_head_865_ = lean_ctor_get(v_x_861_, 0);
v_tail_866_ = lean_ctor_get(v_x_861_, 1);
v_head_867_ = lean_ctor_get(v_x_862_, 0);
lean_inc(v_head_867_);
v_tail_868_ = lean_ctor_get(v_x_862_, 1);
lean_inc(v_tail_868_);
lean_dec_ref_known(v_x_862_, 2);
v___x_869_ = lean_name_eq(v_head_865_, v_head_867_);
lean_dec(v_head_867_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; 
lean_dec(v_tail_868_);
v___x_870_ = lean_box(0);
return v___x_870_;
}
else
{
v_x_861_ = v_tail_866_;
v_x_862_ = v_tail_868_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0___boxed(lean_object* v_x_872_, lean_object* v_x_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0(v_x_872_, v_x_873_);
lean_dec(v_x_872_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0(lean_object* v_l_u2081_875_, lean_object* v_l_u2082_876_){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_877_ = l_List_reverse___redArg(v_l_u2081_875_);
v___x_878_ = l_List_reverse___redArg(v_l_u2082_876_);
v___x_879_ = l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0(v___x_877_, v___x_878_);
lean_dec(v___x_877_);
if (lean_obj_tag(v___x_879_) == 0)
{
return v___x_879_;
}
else
{
lean_object* v_val_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_888_; 
v_val_880_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_888_ == 0)
{
v___x_882_ = v___x_879_;
v_isShared_883_ = v_isSharedCheck_888_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_val_880_);
lean_dec(v___x_879_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_888_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_884_ = l_List_reverse___redArg(v_val_880_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_884_);
v___x_886_ = v___x_882_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(uint8_t v_b_u2082_889_, lean_object* v_k_890_, lean_object* v_t_891_){
_start:
{
if (lean_obj_tag(v_t_891_) == 0)
{
lean_object* v_size_892_; lean_object* v_k_893_; lean_object* v_v_894_; lean_object* v_l_895_; lean_object* v_r_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_910_; 
v_size_892_ = lean_ctor_get(v_t_891_, 0);
v_k_893_ = lean_ctor_get(v_t_891_, 1);
v_v_894_ = lean_ctor_get(v_t_891_, 2);
v_l_895_ = lean_ctor_get(v_t_891_, 3);
v_r_896_ = lean_ctor_get(v_t_891_, 4);
v_isSharedCheck_910_ = !lean_is_exclusive(v_t_891_);
if (v_isSharedCheck_910_ == 0)
{
v___x_898_ = v_t_891_;
v_isShared_899_ = v_isSharedCheck_910_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_r_896_);
lean_inc(v_l_895_);
lean_inc(v_v_894_);
lean_inc(v_k_893_);
lean_inc(v_size_892_);
lean_dec(v_t_891_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_910_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
uint8_t v___x_900_; 
v___x_900_ = lean_nat_dec_lt(v_k_890_, v_k_893_);
if (v___x_900_ == 0)
{
uint8_t v___x_901_; 
v___x_901_ = lean_nat_dec_eq(v_k_890_, v_k_893_);
if (v___x_901_ == 0)
{
lean_object* v_impl_902_; lean_object* v___x_903_; 
lean_del_object(v___x_898_);
lean_dec(v_size_892_);
v_impl_902_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_889_, v_k_890_, v_r_896_);
v___x_903_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_893_, v_v_894_, v_l_895_, v_impl_902_);
return v___x_903_;
}
else
{
lean_object* v___x_904_; lean_object* v___x_906_; 
lean_dec(v_v_894_);
lean_dec(v_k_893_);
v___x_904_ = lean_box(v_b_u2082_889_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 2, v___x_904_);
lean_ctor_set(v___x_898_, 1, v_k_890_);
v___x_906_ = v___x_898_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_size_892_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_k_890_);
lean_ctor_set(v_reuseFailAlloc_907_, 2, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_907_, 3, v_l_895_);
lean_ctor_set(v_reuseFailAlloc_907_, 4, v_r_896_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
else
{
lean_object* v_impl_908_; lean_object* v___x_909_; 
lean_del_object(v___x_898_);
lean_dec(v_size_892_);
v_impl_908_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_889_, v_k_890_, v_l_895_);
v___x_909_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_893_, v_v_894_, v_impl_908_, v_r_896_);
return v___x_909_;
}
}
}
else
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_911_ = lean_unsigned_to_nat(1u);
v___x_912_ = lean_box(v_b_u2082_889_);
v___x_913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_913_, 0, v___x_911_);
lean_ctor_set(v___x_913_, 1, v_k_890_);
lean_ctor_set(v___x_913_, 2, v___x_912_);
lean_ctor_set(v___x_913_, 3, v_t_891_);
lean_ctor_set(v___x_913_, 4, v_t_891_);
return v___x_913_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg___boxed(lean_object* v_b_u2082_914_, lean_object* v_k_915_, lean_object* v_t_916_){
_start:
{
uint8_t v_b_u2082_boxed_917_; lean_object* v_res_918_; 
v_b_u2082_boxed_917_ = lean_unbox(v_b_u2082_914_);
v_res_918_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_boxed_917_, v_k_915_, v_t_916_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(lean_object* v_init_919_, lean_object* v_x_920_){
_start:
{
if (lean_obj_tag(v_x_920_) == 0)
{
lean_object* v_k_921_; lean_object* v_v_922_; lean_object* v_l_923_; lean_object* v_r_924_; lean_object* v___x_925_; uint8_t v___x_926_; lean_object* v___x_927_; 
v_k_921_ = lean_ctor_get(v_x_920_, 1);
lean_inc(v_k_921_);
v_v_922_ = lean_ctor_get(v_x_920_, 2);
lean_inc(v_v_922_);
v_l_923_ = lean_ctor_get(v_x_920_, 3);
lean_inc(v_l_923_);
v_r_924_ = lean_ctor_get(v_x_920_, 4);
lean_inc(v_r_924_);
lean_dec_ref_known(v_x_920_, 5);
v___x_925_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_init_919_, v_l_923_);
v___x_926_ = lean_unbox(v_v_922_);
lean_dec(v_v_922_);
v___x_927_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v___x_926_, v_k_921_, v___x_925_);
v_init_919_ = v___x_927_;
v_x_920_ = v_r_924_;
goto _start;
}
else
{
return v_init_919_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(lean_object* v_as_929_, size_t v_i_930_, size_t v_stop_931_, lean_object* v_b_932_){
_start:
{
uint8_t v___x_933_; 
v___x_933_ = lean_usize_dec_eq(v_i_930_, v_stop_931_);
if (v___x_933_ == 0)
{
lean_object* v_changesBefore_934_; lean_object* v_changesAfter_935_; lean_object* v___x_936_; lean_object* v_changesBefore_937_; lean_object* v_changesAfter_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_950_; 
v_changesBefore_934_ = lean_ctor_get(v_b_932_, 0);
lean_inc(v_changesBefore_934_);
v_changesAfter_935_ = lean_ctor_get(v_b_932_, 1);
lean_inc(v_changesAfter_935_);
lean_dec_ref(v_b_932_);
v___x_936_ = lean_array_uget(v_as_929_, v_i_930_);
v_changesBefore_937_ = lean_ctor_get(v___x_936_, 0);
v_changesAfter_938_ = lean_ctor_get(v___x_936_, 1);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_950_ == 0)
{
v___x_940_ = v___x_936_;
v_isShared_941_ = v_isSharedCheck_950_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_changesAfter_938_);
lean_inc(v_changesBefore_937_);
lean_dec(v___x_936_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_950_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_945_; 
v___x_942_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesBefore_934_, v_changesBefore_937_);
v___x_943_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesAfter_935_, v_changesAfter_938_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 1, v___x_943_);
lean_ctor_set(v___x_940_, 0, v___x_942_);
v___x_945_ = v___x_940_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v___x_943_);
v___x_945_ = v_reuseFailAlloc_949_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
size_t v___x_946_; size_t v___x_947_; 
v___x_946_ = ((size_t)1ULL);
v___x_947_ = lean_usize_add(v_i_930_, v___x_946_);
v_i_930_ = v___x_947_;
v_b_932_ = v___x_945_;
goto _start;
}
}
}
else
{
return v_b_932_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10___boxed(lean_object* v_as_951_, lean_object* v_i_952_, lean_object* v_stop_953_, lean_object* v_b_954_){
_start:
{
size_t v_i_boxed_955_; size_t v_stop_boxed_956_; lean_object* v_res_957_; 
v_i_boxed_955_ = lean_unbox_usize(v_i_952_);
lean_dec(v_i_952_);
v_stop_boxed_956_ = lean_unbox_usize(v_stop_953_);
lean_dec(v_stop_953_);
v_res_957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_as_951_, v_i_boxed_955_, v_stop_boxed_956_, v_b_954_);
lean_dec_ref(v_as_951_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(lean_object* v_x_958_, lean_object* v_x_959_, lean_object* v_x_960_){
_start:
{
if (lean_obj_tag(v_x_958_) == 5)
{
lean_object* v_fn_961_; lean_object* v_arg_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v_fn_961_ = lean_ctor_get(v_x_958_, 0);
lean_inc_ref(v_fn_961_);
v_arg_962_ = lean_ctor_get(v_x_958_, 1);
lean_inc_ref(v_arg_962_);
lean_dec_ref_known(v_x_958_, 2);
v___x_963_ = lean_array_set(v_x_959_, v_x_960_, v_arg_962_);
v___x_964_ = lean_unsigned_to_nat(1u);
v___x_965_ = lean_nat_sub(v_x_960_, v___x_964_);
lean_dec(v_x_960_);
v_x_958_ = v_fn_961_;
v_x_959_ = v___x_963_;
v_x_960_ = v___x_965_;
goto _start;
}
else
{
lean_object* v___x_967_; 
lean_dec(v_x_960_);
v___x_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_967_, 0, v_x_958_);
lean_ctor_set(v___x_967_, 1, v_x_959_);
return v___x_967_;
}
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0(void){
_start:
{
lean_object* v___x_968_; lean_object* v_dummy_969_; 
v___x_968_ = lean_box(0);
v_dummy_969_ = l_Lean_Expr_sort___override(v___x_968_);
return v_dummy_969_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(lean_object* v_snd_970_, lean_object* v_before_971_, lean_object* v_after_972_, size_t v_sz_973_, size_t v_i_974_, lean_object* v_bs_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
uint8_t v___x_981_; 
v___x_981_ = lean_usize_dec_lt(v_i_974_, v_sz_973_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; 
v___x_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_982_, 0, v_bs_975_);
return v___x_982_;
}
else
{
lean_object* v_v_983_; lean_object* v_fst_984_; lean_object* v_snd_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1015_; 
v_v_983_ = lean_array_uget(v_bs_975_, v_i_974_);
v_fst_984_ = lean_ctor_get(v_v_983_, 0);
v_snd_985_ = lean_ctor_get(v_v_983_, 1);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_v_983_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_987_ = v_v_983_;
v_isShared_988_ = v_isSharedCheck_1015_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_snd_985_);
lean_inc(v_fst_984_);
lean_dec(v_v_983_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1015_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v_pos_989_; lean_object* v_pos_990_; lean_object* v___x_991_; lean_object* v_bs_x27_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_997_; 
v_pos_989_ = lean_ctor_get(v_before_971_, 1);
v_pos_990_ = lean_ctor_get(v_after_972_, 1);
v___x_991_ = lean_unsigned_to_nat(0u);
v_bs_x27_992_ = lean_array_uset(v_bs_975_, v_i_974_, v___x_991_);
v___x_993_ = lean_usize_to_nat(v_i_974_);
v___x_994_ = lean_array_get_size(v_snd_970_);
v___x_995_ = l_Lean_SubExpr_Pos_pushNaryArg(v___x_994_, v___x_993_, v_pos_989_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 1, v___x_995_);
v___x_997_ = v___x_987_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_fst_984_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v___x_995_);
v___x_997_ = v_reuseFailAlloc_1014_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_998_ = l_Lean_SubExpr_Pos_pushNaryArg(v___x_994_, v___x_993_, v_pos_990_);
lean_dec(v___x_993_);
v___x_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_999_, 0, v_snd_985_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_997_, v___x_999_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; size_t v___x_1002_; size_t v___x_1003_; lean_object* v___x_1004_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1002_ = ((size_t)1ULL);
v___x_1003_ = lean_usize_add(v_i_974_, v___x_1002_);
v___x_1004_ = lean_array_uset(v_bs_x27_992_, v_i_974_, v_a_1001_);
v_i_974_ = v___x_1003_;
v_bs_975_ = v___x_1004_;
goto _start;
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
lean_dec_ref(v_bs_x27_992_);
v_a_1006_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_1000_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1000_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
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
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__0));
v___x_1018_ = l_Lean_stringToMessageData(v___x_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0___boxed(lean_object* v_body_1019_, lean_object* v_pos_1020_, lean_object* v_body_1021_, lean_object* v_pos_1022_, lean_object* v_x_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0(v_body_1019_, v_pos_1020_, v_body_1021_, v_pos_1022_, v_x_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec_ref(v_x_1023_);
lean_dec(v_pos_1022_);
lean_dec_ref(v_body_1021_);
lean_dec(v_pos_1020_);
lean_dec_ref(v_body_1019_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(lean_object* v_before_1030_, lean_object* v_after_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v_a_1043_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; uint8_t v___y_1054_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v_a_1073_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v_expr_1114_; 
v_expr_1114_ = lean_ctor_get(v_before_1030_, 0);
if (lean_obj_tag(v_expr_1114_) == 7)
{
lean_object* v_pos_1115_; lean_object* v_binderName_1116_; lean_object* v_binderType_1117_; lean_object* v_body_1118_; uint8_t v_binderInfo_1119_; lean_object* v_expr_1120_; lean_object* v_pos_1121_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; 
v_pos_1115_ = lean_ctor_get(v_before_1030_, 1);
v_binderName_1116_ = lean_ctor_get(v_expr_1114_, 0);
v_binderType_1117_ = lean_ctor_get(v_expr_1114_, 1);
v_body_1118_ = lean_ctor_get(v_expr_1114_, 2);
v_binderInfo_1119_ = lean_ctor_get_uint8(v_expr_1114_, sizeof(void*)*3 + 8);
v_expr_1120_ = lean_ctor_get(v_after_1031_, 0);
v_pos_1121_ = lean_ctor_get(v_after_1031_, 1);
if (lean_obj_tag(v_expr_1120_) == 7)
{
lean_object* v_binderName_1147_; lean_object* v_binderType_1148_; lean_object* v_body_1149_; uint8_t v_binderInfo_1150_; lean_object* v___f_1151_; uint8_t v___y_1153_; uint8_t v___x_1203_; 
v_binderName_1147_ = lean_ctor_get(v_expr_1120_, 0);
v_binderType_1148_ = lean_ctor_get(v_expr_1120_, 1);
v_body_1149_ = lean_ctor_get(v_expr_1120_, 2);
v_binderInfo_1150_ = lean_ctor_get_uint8(v_expr_1120_, sizeof(void*)*3 + 8);
lean_inc(v_pos_1121_);
lean_inc_ref(v_body_1149_);
lean_inc(v_pos_1115_);
lean_inc_ref(v_body_1118_);
v___f_1151_ = lean_alloc_closure((void*)(l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1151_, 0, v_body_1118_);
lean_closure_set(v___f_1151_, 1, v_pos_1115_);
lean_closure_set(v___f_1151_, 2, v_body_1149_);
lean_closure_set(v___f_1151_, 3, v_pos_1121_);
v___x_1203_ = lean_name_eq(v_binderName_1116_, v_binderName_1147_);
if (v___x_1203_ == 0)
{
v___y_1153_ = v___x_1203_;
goto v___jp_1152_;
}
else
{
uint8_t v___x_1204_; 
v___x_1204_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1119_, v_binderInfo_1150_);
v___y_1153_ = v___x_1204_;
goto v___jp_1152_;
}
v___jp_1152_:
{
if (v___y_1153_ == 0)
{
lean_dec_ref(v___f_1151_);
v___y_1123_ = v_a_1032_;
v___y_1124_ = v_a_1033_;
v___y_1125_ = v_a_1034_;
v___y_1126_ = v_a_1035_;
goto v___jp_1122_;
}
else
{
lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1200_; 
lean_inc_ref(v_binderType_1148_);
lean_inc(v_pos_1121_);
lean_inc_ref(v_binderType_1117_);
lean_inc(v_binderName_1116_);
lean_inc(v_pos_1115_);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_before_1030_);
if (v_isSharedCheck_1200_ == 0)
{
lean_object* v_unused_1201_; lean_object* v_unused_1202_; 
v_unused_1201_ = lean_ctor_get(v_before_1030_, 1);
lean_dec(v_unused_1201_);
v_unused_1202_ = lean_ctor_get(v_before_1030_, 0);
lean_dec(v_unused_1202_);
v___x_1155_ = v_before_1030_;
v_isShared_1156_ = v_isSharedCheck_1200_;
goto v_resetjp_1154_;
}
else
{
lean_dec(v_before_1030_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1200_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1197_; 
v_isSharedCheck_1197_ = !lean_is_exclusive(v_after_1031_);
if (v_isSharedCheck_1197_ == 0)
{
lean_object* v_unused_1198_; lean_object* v_unused_1199_; 
v_unused_1198_ = lean_ctor_get(v_after_1031_, 1);
lean_dec(v_unused_1198_);
v_unused_1199_ = lean_ctor_get(v_after_1031_, 0);
lean_dec(v_unused_1199_);
v___x_1158_ = v_after_1031_;
v_isShared_1159_ = v_isSharedCheck_1197_;
goto v_resetjp_1157_;
}
else
{
lean_dec(v_after_1031_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1197_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1160_; lean_object* v___x_1162_; 
v___x_1160_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1115_);
lean_inc_ref(v_binderType_1117_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 1, v___x_1160_);
lean_ctor_set(v___x_1158_, 0, v_binderType_1117_);
v___x_1162_ = v___x_1158_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_binderType_1117_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v___x_1160_);
v___x_1162_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1163_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1121_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 1, v___x_1163_);
lean_ctor_set(v___x_1155_, 0, v_binderType_1148_);
v___x_1165_ = v___x_1155_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_binderType_1148_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1166_; 
v___x_1166_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1162_, v___x_1165_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1194_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1169_ = v___x_1166_;
v_isShared_1170_ = v_isSharedCheck_1194_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1166_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1194_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
uint8_t v___x_1171_; 
v___x_1171_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_a_1167_);
if (v___x_1171_ == 0)
{
lean_object* v_changesBefore_1172_; lean_object* v_changesAfter_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; uint8_t v___x_1176_; lean_object* v___x_1177_; lean_object* v_changesBefore_1178_; lean_object* v_changesAfter_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1191_; 
lean_dec_ref(v___f_1151_);
lean_dec_ref(v_binderType_1117_);
lean_dec(v_binderName_1116_);
v_changesBefore_1172_ = lean_ctor_get(v_a_1167_, 0);
lean_inc(v_changesBefore_1172_);
v_changesAfter_1173_ = lean_ctor_get(v_a_1167_, 1);
lean_inc(v_changesAfter_1173_);
lean_dec(v_a_1167_);
v___x_1174_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1115_);
lean_dec(v_pos_1115_);
v___x_1175_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1121_);
lean_dec(v_pos_1121_);
v___x_1176_ = 0;
v___x_1177_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v___x_1174_, v___x_1175_, v___x_1176_);
v_changesBefore_1178_ = lean_ctor_get(v___x_1177_, 0);
v_changesAfter_1179_ = lean_ctor_get(v___x_1177_, 1);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1181_ = v___x_1177_;
v_isShared_1182_ = v_isSharedCheck_1191_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_changesAfter_1179_);
lean_inc(v_changesBefore_1178_);
lean_dec(v___x_1177_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1191_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1183_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesBefore_1172_, v_changesBefore_1178_);
v___x_1184_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesAfter_1173_, v_changesAfter_1179_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 1, v___x_1184_);
lean_ctor_set(v___x_1181_, 0, v___x_1183_);
v___x_1186_ = v___x_1181_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1183_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
lean_object* v___x_1188_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1186_);
v___x_1188_ = v___x_1169_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1186_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
else
{
uint8_t v___x_1192_; lean_object* v___x_1193_; 
lean_del_object(v___x_1169_);
lean_dec(v_a_1167_);
lean_dec(v_pos_1121_);
lean_dec(v_pos_1115_);
v___x_1192_ = 0;
v___x_1193_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_binderName_1116_, v_binderInfo_1119_, v_binderType_1117_, v___f_1151_, v___x_1192_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
return v___x_1193_;
}
}
}
else
{
lean_dec_ref(v___f_1151_);
lean_dec(v_pos_1121_);
lean_dec_ref(v_binderType_1117_);
lean_dec(v_binderName_1116_);
lean_dec(v_pos_1115_);
return v___x_1166_;
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
v___y_1123_ = v_a_1032_;
v___y_1124_ = v_a_1033_;
v___y_1125_ = v_a_1034_;
v___y_1126_ = v_a_1035_;
goto v___jp_1122_;
}
v___jp_1122_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1127_ = l_Lean_Expr_getForallBinderNames(v_expr_1120_);
v___x_1128_ = l_Lean_Expr_getForallBinderNames(v_expr_1114_);
v___x_1129_ = l_List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0(v___x_1127_, v___x_1128_);
if (lean_obj_tag(v___x_1129_) == 1)
{
lean_object* v_val_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v_val_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_val_1130_);
lean_dec_ref_known(v___x_1129_, 1);
v___x_1131_ = l_List_lengthTR___redArg(v_val_1130_);
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = lean_nat_dec_eq(v___x_1131_, v___x_1132_);
lean_dec(v___x_1131_);
if (v___x_1133_ == 0)
{
lean_inc(v_pos_1115_);
lean_inc_ref(v_expr_1114_);
v___y_1077_ = v_expr_1114_;
v___y_1078_ = v_pos_1115_;
v___y_1079_ = v_val_1130_;
v___y_1080_ = v___y_1123_;
v___y_1081_ = v___y_1124_;
v___y_1082_ = v___y_1125_;
v___y_1083_ = v___y_1126_;
goto v___jp_1076_;
}
else
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1, &l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1);
v___x_1135_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_1134_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_dec_ref_known(v___x_1135_, 1);
lean_inc(v_pos_1115_);
lean_inc_ref(v_expr_1114_);
v___y_1077_ = v_expr_1114_;
v___y_1078_ = v_pos_1115_;
v___y_1079_ = v_val_1130_;
v___y_1080_ = v___y_1123_;
v___y_1081_ = v___y_1124_;
v___y_1082_ = v___y_1125_;
v___y_1083_ = v___y_1126_;
goto v___jp_1076_;
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_dec(v_val_1130_);
lean_dec_ref(v_after_1031_);
lean_dec_ref(v_before_1030_);
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1135_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1135_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
}
else
{
uint8_t v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
lean_dec(v___x_1129_);
v___x_1144_ = 0;
v___x_1145_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1030_, v_after_1031_, v___x_1144_);
v___x_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
return v___x_1146_;
}
}
}
else
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_dec_ref(v_after_1031_);
lean_dec_ref(v_before_1030_);
v___x_1205_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
return v___x_1206_;
}
v___jp_1037_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = lean_unsigned_to_nat(0u);
v___x_1045_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v___y_1038_, v_before_1030_, v___x_1044_, v_a_1043_);
lean_dec(v___y_1038_);
return v___x_1045_;
}
v___jp_1046_:
{
if (v___y_1054_ == 0)
{
lean_object* v___x_1055_; 
lean_dec_ref(v___y_1047_);
v___x_1055_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1052_, v___y_1049_, v___y_1051_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v___x_1056_; 
lean_dec_ref_known(v___x_1055_, 1);
v___x_1056_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___y_1038_ = v___y_1048_;
v___y_1039_ = v___y_1049_;
v___y_1040_ = v___y_1050_;
v___y_1041_ = v___y_1051_;
v___y_1042_ = v___y_1053_;
v_a_1043_ = v___x_1056_;
goto v___jp_1037_;
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
lean_dec(v___y_1048_);
lean_dec_ref(v_before_1030_);
v_a_1057_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_1055_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1055_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
else
{
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1048_);
lean_dec_ref(v_before_1030_);
return v___y_1047_;
}
}
v___jp_1065_:
{
uint8_t v___x_1074_; 
v___x_1074_ = l_Lean_Exception_isInterrupt(v_a_1073_);
if (v___x_1074_ == 0)
{
uint8_t v___x_1075_; 
v___x_1075_ = l_Lean_Exception_isRuntime(v_a_1073_);
v___y_1047_ = v___y_1072_;
v___y_1048_ = v___y_1066_;
v___y_1049_ = v___y_1067_;
v___y_1050_ = v___y_1068_;
v___y_1051_ = v___y_1069_;
v___y_1052_ = v___y_1070_;
v___y_1053_ = v___y_1071_;
v___y_1054_ = v___x_1075_;
goto v___jp_1046_;
}
else
{
lean_dec_ref(v_a_1073_);
v___y_1047_ = v___y_1072_;
v___y_1048_ = v___y_1066_;
v___y_1049_ = v___y_1067_;
v___y_1050_ = v___y_1068_;
v___y_1051_ = v___y_1069_;
v___y_1052_ = v___y_1070_;
v___y_1053_ = v___y_1071_;
v___y_1054_ = v___x_1074_;
goto v___jp_1046_;
}
}
v___jp_1076_:
{
lean_object* v___x_1084_; lean_object* v_body_u2080_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1084_ = l_List_lengthTR___redArg(v___y_1079_);
lean_inc(v___x_1084_);
v_body_u2080_1085_ = l_Lean_Expr_getForallBodyMaxDepth(v___x_1084_, v___y_1077_);
lean_dec_ref(v___y_1077_);
v___x_1086_ = lean_box(0);
v___x_1087_ = l_Lean_Meta_saveState___redArg(v___y_1081_, v___y_1083_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v___x_1089_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v___x_1087_, 1);
v___x_1089_ = l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(v___y_1079_, v___x_1086_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_a_1090_);
lean_dec_ref_known(v___x_1089_, 1);
v___x_1091_ = lean_array_mk(v_a_1090_);
v___x_1092_ = lean_expr_instantiate_rev(v_body_u2080_1085_, v___x_1091_);
lean_dec_ref(v___x_1091_);
lean_dec_ref(v_body_u2080_1085_);
lean_inc(v___x_1084_);
v___x_1093_ = l_Lean_SubExpr_Pos_pushNthBindingBody(v___x_1084_, v___y_1078_);
v___x_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1092_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1094_, v_after_1031_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; 
lean_dec(v_a_1088_);
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v___x_1095_, 1);
v___y_1038_ = v___x_1084_;
v___y_1039_ = v___y_1081_;
v___y_1040_ = v___y_1082_;
v___y_1041_ = v___y_1083_;
v___y_1042_ = v___y_1080_;
v_a_1043_ = v_a_1096_;
goto v___jp_1037_;
}
else
{
lean_object* v_a_1097_; 
v_a_1097_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1097_);
v___y_1066_ = v___x_1084_;
v___y_1067_ = v___y_1081_;
v___y_1068_ = v___y_1082_;
v___y_1069_ = v___y_1083_;
v___y_1070_ = v_a_1088_;
v___y_1071_ = v___y_1080_;
v___y_1072_ = v___x_1095_;
v_a_1073_ = v_a_1097_;
goto v___jp_1065_;
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec_ref(v_body_u2080_1085_);
lean_dec(v___y_1078_);
lean_dec_ref(v_after_1031_);
v_a_1098_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1089_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1089_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
lean_inc(v_a_1098_);
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
v___y_1066_ = v___x_1084_;
v___y_1067_ = v___y_1081_;
v___y_1068_ = v___y_1082_;
v___y_1069_ = v___y_1083_;
v___y_1070_ = v_a_1088_;
v___y_1071_ = v___y_1080_;
v___y_1072_ = v___x_1103_;
v_a_1073_ = v_a_1098_;
goto v___jp_1065_;
}
}
}
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_dec_ref(v_body_u2080_1085_);
lean_dec(v___x_1084_);
lean_dec(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v_after_1031_);
lean_dec_ref(v_before_1030_);
v_a_1106_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1087_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1087_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(lean_object* v_before_1207_, lean_object* v_after_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v_expr_1230_; lean_object* v_pos_1231_; lean_object* v_expr_1232_; lean_object* v_pos_1233_; lean_object* v_e_u2081_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; uint8_t v___x_1242_; 
v_expr_1230_ = lean_ctor_get(v_before_1207_, 0);
v_pos_1231_ = lean_ctor_get(v_before_1207_, 1);
v_expr_1232_ = lean_ctor_get(v_after_1208_, 0);
v_pos_1233_ = lean_ctor_get(v_after_1208_, 1);
v___x_1242_ = lean_expr_eqv(v_expr_1230_, v_expr_1232_);
if (v___x_1242_ == 0)
{
switch(lean_obj_tag(v_expr_1230_))
{
case 10:
{
lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1251_; 
lean_inc_ref(v_expr_1230_);
lean_inc(v_pos_1231_);
v_isSharedCheck_1251_ = !lean_is_exclusive(v_before_1207_);
if (v_isSharedCheck_1251_ == 0)
{
lean_object* v_unused_1252_; lean_object* v_unused_1253_; 
v_unused_1252_ = lean_ctor_get(v_before_1207_, 1);
lean_dec(v_unused_1252_);
v_unused_1253_ = lean_ctor_get(v_before_1207_, 0);
lean_dec(v_unused_1253_);
v___x_1244_ = v_before_1207_;
v_isShared_1245_ = v_isSharedCheck_1251_;
goto v_resetjp_1243_;
}
else
{
lean_dec(v_before_1207_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1251_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v_expr_1246_; lean_object* v___x_1248_; 
v_expr_1246_ = lean_ctor_get(v_expr_1230_, 1);
lean_inc_ref(v_expr_1246_);
lean_dec_ref_known(v_expr_1230_, 2);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v_expr_1246_);
v___x_1248_ = v___x_1244_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_expr_1246_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_pos_1231_);
v___x_1248_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
v_before_1207_ = v___x_1248_;
goto _start;
}
}
}
case 5:
{
switch(lean_obj_tag(v_expr_1232_))
{
case 10:
{
lean_object* v_expr_1254_; 
lean_inc_ref(v_expr_1232_);
lean_inc(v_pos_1233_);
lean_dec_ref(v_after_1208_);
v_expr_1254_ = lean_ctor_get(v_expr_1232_, 1);
lean_inc_ref(v_expr_1254_);
lean_dec_ref_known(v_expr_1232_, 2);
v_e_u2081_1235_ = v_expr_1254_;
v___y_1236_ = v_a_1209_;
v___y_1237_ = v_a_1210_;
v___y_1238_ = v_a_1211_;
v___y_1239_ = v_a_1212_;
goto v___jp_1234_;
}
case 5:
{
lean_object* v_dummy_1255_; lean_object* v_nargs_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v_fst_1261_; lean_object* v_snd_1262_; lean_object* v_nargs_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v_fst_1267_; lean_object* v_snd_1268_; uint8_t v___x_1269_; 
v_dummy_1255_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0, &l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0);
v_nargs_1256_ = l_Lean_Expr_getAppNumArgs(v_expr_1232_);
lean_inc(v_nargs_1256_);
v___x_1257_ = lean_mk_array(v_nargs_1256_, v_dummy_1255_);
v___x_1258_ = lean_unsigned_to_nat(1u);
v___x_1259_ = lean_nat_sub(v_nargs_1256_, v___x_1258_);
lean_dec(v_nargs_1256_);
lean_inc_ref(v_expr_1232_);
v___x_1260_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(v_expr_1232_, v___x_1257_, v___x_1259_);
v_fst_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_fst_1261_);
v_snd_1262_ = lean_ctor_get(v___x_1260_, 1);
lean_inc(v_snd_1262_);
lean_dec_ref(v___x_1260_);
v_nargs_1263_ = l_Lean_Expr_getAppNumArgs(v_expr_1230_);
lean_inc(v_nargs_1263_);
v___x_1264_ = lean_mk_array(v_nargs_1263_, v_dummy_1255_);
v___x_1265_ = lean_nat_sub(v_nargs_1263_, v___x_1258_);
lean_dec(v_nargs_1263_);
lean_inc_ref(v_expr_1230_);
v___x_1266_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(v_expr_1230_, v___x_1264_, v___x_1265_);
v_fst_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_fst_1267_);
v_snd_1268_ = lean_ctor_get(v___x_1266_, 1);
lean_inc(v_snd_1268_);
lean_dec_ref(v___x_1266_);
v___x_1269_ = lean_expr_eqv(v_fst_1261_, v_fst_1267_);
lean_dec(v_fst_1267_);
lean_dec(v_fst_1261_);
if (v___x_1269_ == 0)
{
lean_dec(v_snd_1268_);
lean_dec(v_snd_1262_);
goto v___jp_1222_;
}
else
{
if (v___x_1242_ == 0)
{
lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1270_ = lean_array_get_size(v_snd_1262_);
v___x_1271_ = lean_array_get_size(v_snd_1268_);
v___x_1272_ = lean_nat_dec_eq(v___x_1270_, v___x_1271_);
if (v___x_1272_ == 0)
{
lean_dec(v_snd_1268_);
lean_dec(v_snd_1262_);
goto v___jp_1222_;
}
else
{
if (v___x_1242_ == 0)
{
lean_object* v_args_1273_; size_t v_sz_1274_; size_t v___x_1275_; lean_object* v___x_1276_; 
v_args_1273_ = l_Array_zip___redArg(v_snd_1262_, v_snd_1268_);
lean_dec(v_snd_1268_);
v_sz_1274_ = lean_array_size(v_args_1273_);
v___x_1275_ = ((size_t)0ULL);
v___x_1276_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_1262_, v_before_1207_, v_after_1208_, v_sz_1274_, v___x_1275_, v_args_1273_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
lean_dec_ref(v_after_1208_);
lean_dec_ref(v_before_1207_);
lean_dec(v_snd_1262_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1302_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1279_ = v___x_1276_;
v_isShared_1280_ = v_isSharedCheck_1302_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1276_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1302_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; 
v___x_1281_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___x_1282_ = lean_unsigned_to_nat(0u);
v___x_1283_ = lean_array_get_size(v_a_1277_);
v___x_1284_ = lean_nat_dec_lt(v___x_1282_, v___x_1283_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1286_; 
lean_dec(v_a_1277_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v___x_1281_);
v___x_1286_ = v___x_1279_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
else
{
uint8_t v___x_1288_; 
v___x_1288_ = lean_nat_dec_le(v___x_1283_, v___x_1283_);
if (v___x_1288_ == 0)
{
if (v___x_1284_ == 0)
{
lean_object* v___x_1290_; 
lean_dec(v_a_1277_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v___x_1281_);
v___x_1290_ = v___x_1279_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1281_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
else
{
size_t v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1295_; 
v___x_1292_ = lean_usize_of_nat(v___x_1283_);
v___x_1293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_a_1277_, v___x_1275_, v___x_1292_, v___x_1281_);
lean_dec(v_a_1277_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v___x_1293_);
v___x_1295_ = v___x_1279_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1293_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
else
{
size_t v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1300_; 
v___x_1297_ = lean_usize_of_nat(v___x_1283_);
v___x_1298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_a_1277_, v___x_1275_, v___x_1297_, v___x_1281_);
lean_dec(v_a_1277_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v___x_1298_);
v___x_1300_ = v___x_1279_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1298_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
v_a_1303_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1276_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1276_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
else
{
lean_dec(v_snd_1268_);
lean_dec(v_snd_1262_);
goto v___jp_1222_;
}
}
}
else
{
lean_dec(v_snd_1268_);
lean_dec(v_snd_1262_);
goto v___jp_1222_;
}
}
}
default: 
{
goto v___jp_1226_;
}
}
}
case 7:
{
if (lean_obj_tag(v_expr_1232_) == 10)
{
lean_object* v_expr_1311_; 
lean_inc_ref(v_expr_1232_);
lean_inc(v_pos_1233_);
lean_dec_ref(v_after_1208_);
v_expr_1311_ = lean_ctor_get(v_expr_1232_, 1);
lean_inc_ref(v_expr_1311_);
lean_dec_ref_known(v_expr_1232_, 2);
v_e_u2081_1235_ = v_expr_1311_;
v___y_1236_ = v_a_1209_;
v___y_1237_ = v_a_1210_;
v___y_1238_ = v_a_1211_;
v___y_1239_ = v_a_1212_;
goto v___jp_1234_;
}
else
{
lean_object* v___x_1312_; 
v___x_1312_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(v_before_1207_, v_after_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
return v___x_1312_;
}
}
case 6:
{
switch(lean_obj_tag(v_expr_1232_))
{
case 10:
{
lean_object* v_expr_1313_; 
lean_inc_ref(v_expr_1232_);
lean_inc(v_pos_1233_);
lean_dec_ref(v_after_1208_);
v_expr_1313_ = lean_ctor_get(v_expr_1232_, 1);
lean_inc_ref(v_expr_1313_);
lean_dec_ref_known(v_expr_1232_, 2);
v_e_u2081_1235_ = v_expr_1313_;
v___y_1236_ = v_a_1209_;
v___y_1237_ = v_a_1210_;
v___y_1238_ = v_a_1211_;
v___y_1239_ = v_a_1212_;
goto v___jp_1234_;
}
case 6:
{
lean_object* v_binderName_1314_; lean_object* v_binderType_1315_; lean_object* v_body_1316_; uint8_t v_binderInfo_1317_; lean_object* v_binderName_1318_; lean_object* v_binderType_1319_; lean_object* v_body_1320_; uint8_t v_binderInfo_1321_; uint8_t v___x_1322_; 
v_binderName_1314_ = lean_ctor_get(v_expr_1230_, 0);
v_binderType_1315_ = lean_ctor_get(v_expr_1230_, 1);
v_body_1316_ = lean_ctor_get(v_expr_1230_, 2);
v_binderInfo_1317_ = lean_ctor_get_uint8(v_expr_1230_, sizeof(void*)*3 + 8);
v_binderName_1318_ = lean_ctor_get(v_expr_1232_, 0);
v_binderType_1319_ = lean_ctor_get(v_expr_1232_, 1);
v_body_1320_ = lean_ctor_get(v_expr_1232_, 2);
v_binderInfo_1321_ = lean_ctor_get_uint8(v_expr_1232_, sizeof(void*)*3 + 8);
v___x_1322_ = lean_name_eq(v_binderName_1314_, v_binderName_1318_);
if (v___x_1322_ == 0)
{
goto v___jp_1218_;
}
else
{
if (v___x_1242_ == 0)
{
uint8_t v___x_1323_; 
v___x_1323_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1317_, v_binderInfo_1321_);
if (v___x_1323_ == 0)
{
goto v___jp_1218_;
}
else
{
if (v___x_1242_ == 0)
{
lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1373_; 
lean_inc_ref(v_body_1320_);
lean_inc_ref(v_binderType_1319_);
lean_inc_ref(v_body_1316_);
lean_inc_ref(v_binderType_1315_);
lean_inc(v_pos_1233_);
lean_inc(v_pos_1231_);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_before_1207_);
if (v_isSharedCheck_1373_ == 0)
{
lean_object* v_unused_1374_; lean_object* v_unused_1375_; 
v_unused_1374_ = lean_ctor_get(v_before_1207_, 1);
lean_dec(v_unused_1374_);
v_unused_1375_ = lean_ctor_get(v_before_1207_, 0);
lean_dec(v_unused_1375_);
v___x_1325_ = v_before_1207_;
v_isShared_1326_ = v_isSharedCheck_1373_;
goto v_resetjp_1324_;
}
else
{
lean_dec(v_before_1207_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1373_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1370_; 
v_isSharedCheck_1370_ = !lean_is_exclusive(v_after_1208_);
if (v_isSharedCheck_1370_ == 0)
{
lean_object* v_unused_1371_; lean_object* v_unused_1372_; 
v_unused_1371_ = lean_ctor_get(v_after_1208_, 1);
lean_dec(v_unused_1371_);
v_unused_1372_ = lean_ctor_get(v_after_1208_, 0);
lean_dec(v_unused_1372_);
v___x_1328_ = v_after_1208_;
v_isShared_1329_ = v_isSharedCheck_1370_;
goto v_resetjp_1327_;
}
else
{
lean_dec(v_after_1208_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1370_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1330_; lean_object* v___x_1332_; 
v___x_1330_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1231_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 1, v___x_1330_);
lean_ctor_set(v___x_1328_, 0, v_binderType_1315_);
v___x_1332_ = v___x_1328_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_binderType_1315_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
lean_object* v___x_1333_; lean_object* v___x_1335_; 
v___x_1333_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1233_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 1, v___x_1333_);
lean_ctor_set(v___x_1325_, 0, v_binderType_1319_);
v___x_1335_ = v___x_1325_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_binderType_1319_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
lean_object* v___x_1336_; 
v___x_1336_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1332_, v___x_1335_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1367_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1339_ = v___x_1336_;
v_isShared_1340_ = v_isSharedCheck_1367_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1336_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1367_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
uint8_t v___x_1341_; 
v___x_1341_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_a_1337_);
if (v___x_1341_ == 0)
{
lean_object* v_changesBefore_1342_; lean_object* v_changesAfter_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; lean_object* v___x_1347_; lean_object* v_changesBefore_1348_; lean_object* v_changesAfter_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1361_; 
lean_dec_ref(v_body_1320_);
lean_dec_ref(v_body_1316_);
v_changesBefore_1342_ = lean_ctor_get(v_a_1337_, 0);
lean_inc(v_changesBefore_1342_);
v_changesAfter_1343_ = lean_ctor_get(v_a_1337_, 1);
lean_inc(v_changesAfter_1343_);
lean_dec(v_a_1337_);
v___x_1344_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1231_);
lean_dec(v_pos_1231_);
v___x_1345_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1233_);
lean_dec(v_pos_1233_);
v___x_1346_ = 0;
v___x_1347_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v___x_1344_, v___x_1345_, v___x_1346_);
v_changesBefore_1348_ = lean_ctor_get(v___x_1347_, 0);
v_changesAfter_1349_ = lean_ctor_get(v___x_1347_, 1);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1351_ = v___x_1347_;
v_isShared_1352_ = v_isSharedCheck_1361_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_changesAfter_1349_);
lean_inc(v_changesBefore_1348_);
lean_dec(v___x_1347_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1361_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1356_; 
v___x_1353_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesBefore_1342_, v_changesBefore_1348_);
v___x_1354_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesAfter_1343_, v_changesAfter_1349_);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 1, v___x_1354_);
lean_ctor_set(v___x_1351_, 0, v___x_1353_);
v___x_1356_ = v___x_1351_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
lean_object* v___x_1358_; 
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v___x_1356_);
v___x_1358_ = v___x_1339_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
else
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
lean_del_object(v___x_1339_);
lean_dec(v_a_1337_);
v___x_1362_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1231_);
lean_dec(v_pos_1231_);
v___x_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1363_, 0, v_body_1316_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
v___x_1364_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1233_);
lean_dec(v_pos_1233_);
v___x_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1365_, 0, v_body_1320_);
lean_ctor_set(v___x_1365_, 1, v___x_1364_);
v_before_1207_ = v___x_1363_;
v_after_1208_ = v___x_1365_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_body_1320_);
lean_dec_ref(v_body_1316_);
lean_dec(v_pos_1233_);
lean_dec(v_pos_1231_);
return v___x_1336_;
}
}
}
}
}
}
else
{
goto v___jp_1218_;
}
}
}
else
{
goto v___jp_1218_;
}
}
}
default: 
{
goto v___jp_1226_;
}
}
}
case 11:
{
switch(lean_obj_tag(v_expr_1232_))
{
case 10:
{
lean_object* v_expr_1376_; 
lean_inc_ref(v_expr_1232_);
lean_inc(v_pos_1233_);
lean_dec_ref(v_after_1208_);
v_expr_1376_ = lean_ctor_get(v_expr_1232_, 1);
lean_inc_ref(v_expr_1376_);
lean_dec_ref_known(v_expr_1232_, 2);
v_e_u2081_1235_ = v_expr_1376_;
v___y_1236_ = v_a_1209_;
v___y_1237_ = v_a_1210_;
v___y_1238_ = v_a_1211_;
v___y_1239_ = v_a_1212_;
goto v___jp_1234_;
}
case 11:
{
lean_object* v_typeName_1377_; lean_object* v_idx_1378_; lean_object* v_struct_1379_; lean_object* v_typeName_1380_; lean_object* v_idx_1381_; lean_object* v_struct_1382_; uint8_t v___x_1383_; 
v_typeName_1377_ = lean_ctor_get(v_expr_1230_, 0);
v_idx_1378_ = lean_ctor_get(v_expr_1230_, 1);
v_struct_1379_ = lean_ctor_get(v_expr_1230_, 2);
v_typeName_1380_ = lean_ctor_get(v_expr_1232_, 0);
v_idx_1381_ = lean_ctor_get(v_expr_1232_, 1);
v_struct_1382_ = lean_ctor_get(v_expr_1232_, 2);
v___x_1383_ = lean_name_eq(v_typeName_1377_, v_typeName_1380_);
if (v___x_1383_ == 0)
{
goto v___jp_1214_;
}
else
{
if (v___x_1242_ == 0)
{
uint8_t v___x_1384_; 
v___x_1384_ = lean_nat_dec_eq(v_idx_1378_, v_idx_1381_);
if (v___x_1384_ == 0)
{
goto v___jp_1214_;
}
else
{
if (v___x_1242_ == 0)
{
lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1403_; 
lean_inc_ref(v_struct_1382_);
lean_inc_ref(v_struct_1379_);
lean_inc(v_pos_1233_);
lean_inc(v_pos_1231_);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_before_1207_);
if (v_isSharedCheck_1403_ == 0)
{
lean_object* v_unused_1404_; lean_object* v_unused_1405_; 
v_unused_1404_ = lean_ctor_get(v_before_1207_, 1);
lean_dec(v_unused_1404_);
v_unused_1405_ = lean_ctor_get(v_before_1207_, 0);
lean_dec(v_unused_1405_);
v___x_1386_ = v_before_1207_;
v_isShared_1387_ = v_isSharedCheck_1403_;
goto v_resetjp_1385_;
}
else
{
lean_dec(v_before_1207_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1403_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1400_; 
v_isSharedCheck_1400_ = !lean_is_exclusive(v_after_1208_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; lean_object* v_unused_1402_; 
v_unused_1401_ = lean_ctor_get(v_after_1208_, 1);
lean_dec(v_unused_1401_);
v_unused_1402_ = lean_ctor_get(v_after_1208_, 0);
lean_dec(v_unused_1402_);
v___x_1389_ = v_after_1208_;
v_isShared_1390_ = v_isSharedCheck_1400_;
goto v_resetjp_1388_;
}
else
{
lean_dec(v_after_1208_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1400_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1391_ = l_Lean_SubExpr_Pos_pushProj(v_pos_1231_);
lean_dec(v_pos_1231_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 1, v___x_1391_);
lean_ctor_set(v___x_1389_, 0, v_struct_1379_);
v___x_1393_ = v___x_1389_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_struct_1379_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v___x_1391_);
v___x_1393_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
lean_object* v___x_1394_; lean_object* v___x_1396_; 
v___x_1394_ = l_Lean_SubExpr_Pos_pushProj(v_pos_1233_);
lean_dec(v_pos_1233_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 1, v___x_1394_);
lean_ctor_set(v___x_1386_, 0, v_struct_1382_);
v___x_1396_ = v___x_1386_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_struct_1382_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v___x_1394_);
v___x_1396_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
v_before_1207_ = v___x_1393_;
v_after_1208_ = v___x_1396_;
goto _start;
}
}
}
}
}
else
{
goto v___jp_1214_;
}
}
}
else
{
goto v___jp_1214_;
}
}
}
default: 
{
goto v___jp_1226_;
}
}
}
default: 
{
if (lean_obj_tag(v_expr_1232_) == 10)
{
lean_object* v_expr_1406_; 
lean_inc_ref(v_expr_1232_);
lean_inc(v_pos_1233_);
lean_dec_ref(v_after_1208_);
v_expr_1406_ = lean_ctor_get(v_expr_1232_, 1);
lean_inc_ref(v_expr_1406_);
lean_dec_ref_known(v_expr_1232_, 2);
v_e_u2081_1235_ = v_expr_1406_;
v___y_1236_ = v_a_1209_;
v___y_1237_ = v_a_1210_;
v___y_1238_ = v_a_1211_;
v___y_1239_ = v_a_1212_;
goto v___jp_1234_;
}
else
{
goto v___jp_1226_;
}
}
}
}
else
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
lean_dec_ref(v_after_1208_);
lean_dec_ref(v_before_1207_);
v___x_1407_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___x_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1407_);
return v___x_1408_;
}
v___jp_1214_:
{
uint8_t v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1215_ = 0;
v___x_1216_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1207_, v_after_1208_, v___x_1215_);
v___x_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
return v___x_1217_;
}
v___jp_1218_:
{
uint8_t v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1219_ = 0;
v___x_1220_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1207_, v_after_1208_, v___x_1219_);
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
return v___x_1221_;
}
v___jp_1222_:
{
uint8_t v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1223_ = 0;
v___x_1224_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1207_, v_after_1208_, v___x_1223_);
v___x_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
return v___x_1225_;
}
v___jp_1226_:
{
uint8_t v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1227_ = 0;
v___x_1228_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1207_, v_after_1208_, v___x_1227_);
v___x_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
return v___x_1229_;
}
v___jp_1234_:
{
lean_object* v___x_1240_; 
v___x_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1240_, 0, v_e_u2081_1235_);
lean_ctor_set(v___x_1240_, 1, v_pos_1233_);
v_after_1208_ = v___x_1240_;
v_a_1209_ = v___y_1236_;
v_a_1210_ = v___y_1237_;
v_a_1211_ = v___y_1238_;
v_a_1212_ = v___y_1239_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0(lean_object* v_body_1409_, lean_object* v_pos_1410_, lean_object* v_body_1411_, lean_object* v_pos_1412_, lean_object* v_x_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1419_ = lean_expr_instantiate1(v_body_1409_, v_x_1413_);
v___x_1420_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1410_);
v___x_1421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1419_);
lean_ctor_set(v___x_1421_, 1, v___x_1420_);
v___x_1422_ = lean_expr_instantiate1(v_body_1411_, v_x_1413_);
v___x_1423_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1412_);
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1422_);
lean_ctor_set(v___x_1424_, 1, v___x_1423_);
v___x_1425_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1421_, v___x_1424_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg___boxed(lean_object* v_snd_1426_, lean_object* v_before_1427_, lean_object* v_after_1428_, lean_object* v_sz_1429_, lean_object* v_i_1430_, lean_object* v_bs_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
size_t v_sz_boxed_1437_; size_t v_i_boxed_1438_; lean_object* v_res_1439_; 
v_sz_boxed_1437_ = lean_unbox_usize(v_sz_1429_);
lean_dec(v_sz_1429_);
v_i_boxed_1438_ = lean_unbox_usize(v_i_1430_);
lean_dec(v_i_1430_);
v_res_1439_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_1426_, v_before_1427_, v_after_1428_, v_sz_boxed_1437_, v_i_boxed_1438_, v_bs_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec_ref(v_after_1428_);
lean_dec_ref(v_before_1427_);
lean_dec_ref(v_snd_1426_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___boxed(lean_object* v_before_1440_, lean_object* v_after_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(v_before_1440_, v_after_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_);
lean_dec(v_a_1445_);
lean_dec_ref(v_a_1444_);
lean_dec(v_a_1443_);
lean_dec_ref(v_a_1442_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___boxed(lean_object* v_before_1448_, lean_object* v_after_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v_before_1448_, v_after_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_);
lean_dec(v_a_1453_);
lean_dec_ref(v_a_1452_);
lean_dec(v_a_1451_);
lean_dec_ref(v_a_1450_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1(lean_object* v_upperBound_1456_, lean_object* v_before_1457_, lean_object* v_inst_1458_, lean_object* v_R_1459_, lean_object* v_a_1460_, lean_object* v_b_1461_, lean_object* v_c_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v_upperBound_1456_, v_before_1457_, v_a_1460_, v_b_1461_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___boxed(lean_object* v_upperBound_1469_, lean_object* v_before_1470_, lean_object* v_inst_1471_, lean_object* v_R_1472_, lean_object* v_a_1473_, lean_object* v_b_1474_, lean_object* v_c_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1(v_upperBound_1469_, v_before_1470_, v_inst_1471_, v_R_1472_, v_a_1473_, v_b_1474_, v_c_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v_upperBound_1469_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3(lean_object* v_00_u03b1_1482_, lean_object* v_msg_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v_msg_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___boxed(lean_object* v_00_u03b1_1490_, lean_object* v_msg_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3(v_00_u03b1_1490_, v_msg_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4(uint8_t v_b_u2082_1498_, lean_object* v_k_1499_, lean_object* v_t_1500_, lean_object* v_hl_1501_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_1498_, v_k_1499_, v_t_1500_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___boxed(lean_object* v_b_u2082_1503_, lean_object* v_k_1504_, lean_object* v_t_1505_, lean_object* v_hl_1506_){
_start:
{
uint8_t v_b_u2082_boxed_1507_; lean_object* v_res_1508_; 
v_b_u2082_boxed_1507_ = lean_unbox(v_b_u2082_1503_);
v_res_1508_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4(v_b_u2082_boxed_1507_, v_k_1504_, v_t_1505_, v_hl_1506_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5(lean_object* v_init_1509_, lean_object* v_t_1510_){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_init_1509_, v_t_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9(lean_object* v_snd_1512_, lean_object* v_before_1513_, lean_object* v_after_1514_, lean_object* v_as_1515_, size_t v_sz_1516_, size_t v_i_1517_, lean_object* v_bs_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_1512_, v_before_1513_, v_after_1514_, v_sz_1516_, v_i_1517_, v_bs_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___boxed(lean_object* v_snd_1525_, lean_object* v_before_1526_, lean_object* v_after_1527_, lean_object* v_as_1528_, lean_object* v_sz_1529_, lean_object* v_i_1530_, lean_object* v_bs_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
size_t v_sz_boxed_1537_; size_t v_i_boxed_1538_; lean_object* v_res_1539_; 
v_sz_boxed_1537_ = lean_unbox_usize(v_sz_1529_);
lean_dec(v_sz_1529_);
v_i_boxed_1538_ = lean_unbox_usize(v_i_1530_);
lean_dec(v_i_1530_);
v_res_1539_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9(v_snd_1525_, v_before_1526_, v_after_1527_, v_as_1528_, v_sz_boxed_1537_, v_i_boxed_1538_, v_bs_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec_ref(v_as_1528_);
lean_dec_ref(v_after_1527_);
lean_dec_ref(v_before_1526_);
lean_dec_ref(v_snd_1525_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(lean_object* v_e_u2080_1540_, lean_object* v_e_u2081_1541_, uint8_t v_useAfter_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v___x_1548_; lean_object* v_s_u2080_1549_; lean_object* v_s_u2081_1550_; 
v___x_1548_ = l_Lean_SubExpr_Pos_root;
v_s_u2080_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_u2080_1549_, 0, v_e_u2080_1540_);
lean_ctor_set(v_s_u2080_1549_, 1, v___x_1548_);
v_s_u2081_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_u2081_1550_, 0, v_e_u2081_1541_);
lean_ctor_set(v_s_u2081_1550_, 1, v___x_1548_);
if (v_useAfter_1542_ == 0)
{
lean_object* v___x_1551_; 
v___x_1551_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v_s_u2081_1550_, v_s_u2080_1549_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_);
return v___x_1551_;
}
else
{
lean_object* v___x_1552_; 
v___x_1552_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v_s_u2080_1549_, v_s_u2081_1550_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_);
return v___x_1552_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff___boxed(lean_object* v_e_u2080_1553_, lean_object* v_e_u2081_1554_, lean_object* v_useAfter_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_){
_start:
{
uint8_t v_useAfter_boxed_1561_; lean_object* v_res_1562_; 
v_useAfter_boxed_1561_ = lean_unbox(v_useAfter_1555_);
v_res_1562_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(v_e_u2080_1553_, v_e_u2081_1554_, v_useAfter_boxed_1561_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0(uint8_t v_useAfter_1563_, lean_object* v_info_1564_, uint8_t v_d_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
uint8_t v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1571_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag(v_useAfter_1563_, v_d_1565_);
v___x_1572_ = l_Lean_Widget_SubexprInfo_withDiffTag(v___x_1571_, v_info_1564_);
v___x_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0___boxed(lean_object* v_useAfter_1574_, lean_object* v_info_1575_, lean_object* v_d_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
uint8_t v_useAfter_boxed_1582_; uint8_t v_d_boxed_1583_; lean_object* v_res_1584_; 
v_useAfter_boxed_1582_ = lean_unbox(v_useAfter_1574_);
v_d_boxed_1583_ = lean_unbox(v_d_1576_);
v_res_1584_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0(v_useAfter_boxed_1582_, v_info_1575_, v_d_boxed_1583_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(lean_object* v_f_1585_, lean_object* v_x_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
switch(lean_obj_tag(v_x_1586_))
{
case 0:
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1600_; 
lean_dec_ref(v_f_1585_);
v_a_1592_ = lean_ctor_get(v_x_1586_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v_x_1586_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1594_ = v_x_1586_;
v_isShared_1595_ = v_isSharedCheck_1600_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v_x_1586_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1600_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1598_; 
v___x_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
return v___x_1598_;
}
}
}
case 1:
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1627_; 
v_a_1601_ = lean_ctor_get(v_x_1586_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v_x_1586_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1603_ = v_x_1586_;
v_isShared_1604_ = v_isSharedCheck_1627_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v_x_1586_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1627_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
size_t v_sz_1605_; size_t v___x_1606_; lean_object* v___x_1607_; 
v_sz_1605_ = lean_array_size(v_a_1601_);
v___x_1606_ = ((size_t)0ULL);
v___x_1607_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_1585_, v_sz_1605_, v___x_1606_, v_a_1601_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1618_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1610_ = v___x_1607_;
v_isShared_1611_ = v_isSharedCheck_1618_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1607_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1618_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 0, v_a_1608_);
v___x_1613_ = v___x_1603_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
lean_object* v___x_1615_; 
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v___x_1613_);
v___x_1615_ = v___x_1610_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1613_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_del_object(v___x_1603_);
v_a_1619_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1607_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1607_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
default: 
{
lean_object* v_a_1628_; lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1655_; 
v_a_1628_ = lean_ctor_get(v_x_1586_, 0);
v_a_1629_ = lean_ctor_get(v_x_1586_, 1);
v_isSharedCheck_1655_ = !lean_is_exclusive(v_x_1586_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1631_ = v_x_1586_;
v_isShared_1632_ = v_isSharedCheck_1655_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_inc(v_a_1628_);
lean_dec(v_x_1586_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1655_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1633_; 
lean_inc_ref(v_f_1585_);
lean_inc(v___y_1590_);
lean_inc_ref(v___y_1589_);
lean_inc(v___y_1588_);
lean_inc_ref(v___y_1587_);
v___x_1633_ = lean_apply_6(v_f_1585_, v_a_1628_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, lean_box(0));
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1635_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
lean_dec_ref_known(v___x_1633_, 1);
v___x_1635_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1585_, v_a_1629_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1646_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1638_ = v___x_1635_;
v_isShared_1639_ = v_isSharedCheck_1646_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1635_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1646_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 1, v_a_1636_);
lean_ctor_set(v___x_1631_, 0, v_a_1634_);
v___x_1641_ = v___x_1631_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1634_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1643_; 
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 0, v___x_1641_);
v___x_1643_ = v___x_1638_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1641_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
else
{
lean_dec(v_a_1634_);
lean_del_object(v___x_1631_);
return v___x_1635_;
}
}
else
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
lean_del_object(v___x_1631_);
lean_dec_ref(v_a_1629_);
lean_dec_ref(v_f_1585_);
v_a_1647_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1649_ = v___x_1633_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1633_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1647_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(lean_object* v_f_1656_, size_t v_sz_1657_, size_t v_i_1658_, lean_object* v_bs_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
uint8_t v___x_1665_; 
v___x_1665_ = lean_usize_dec_lt(v_i_1658_, v_sz_1657_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1666_; 
lean_dec_ref(v_f_1656_);
v___x_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1666_, 0, v_bs_1659_);
return v___x_1666_;
}
else
{
lean_object* v_v_1667_; lean_object* v___x_1668_; lean_object* v_bs_x27_1669_; lean_object* v___x_1670_; 
v_v_1667_ = lean_array_uget(v_bs_1659_, v_i_1658_);
v___x_1668_ = lean_unsigned_to_nat(0u);
v_bs_x27_1669_ = lean_array_uset(v_bs_1659_, v_i_1658_, v___x_1668_);
lean_inc_ref(v_f_1656_);
v___x_1670_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1656_, v_v_1667_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; size_t v___x_1672_; size_t v___x_1673_; lean_object* v___x_1674_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1671_);
lean_dec_ref_known(v___x_1670_, 1);
v___x_1672_ = ((size_t)1ULL);
v___x_1673_ = lean_usize_add(v_i_1658_, v___x_1672_);
v___x_1674_ = lean_array_uset(v_bs_x27_1669_, v_i_1658_, v_a_1671_);
v_i_1658_ = v___x_1673_;
v_bs_1659_ = v___x_1674_;
goto _start;
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_dec_ref(v_bs_x27_1669_);
lean_dec_ref(v_f_1656_);
v_a_1676_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1670_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1670_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_1684_, lean_object* v_sz_1685_, lean_object* v_i_1686_, lean_object* v_bs_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
size_t v_sz_boxed_1693_; size_t v_i_boxed_1694_; lean_object* v_res_1695_; 
v_sz_boxed_1693_ = lean_unbox_usize(v_sz_1685_);
lean_dec(v_sz_1685_);
v_i_boxed_1694_ = lean_unbox_usize(v_i_1686_);
lean_dec(v_i_1686_);
v_res_1695_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_1684_, v_sz_boxed_1693_, v_i_boxed_1694_, v_bs_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg___boxed(lean_object* v_f_1696_, lean_object* v_x_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1696_, v_x_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(lean_object* v_t_1704_, lean_object* v_k_1705_){
_start:
{
if (lean_obj_tag(v_t_1704_) == 0)
{
lean_object* v_k_1706_; lean_object* v_v_1707_; lean_object* v_l_1708_; lean_object* v_r_1709_; uint8_t v___x_1710_; 
v_k_1706_ = lean_ctor_get(v_t_1704_, 1);
v_v_1707_ = lean_ctor_get(v_t_1704_, 2);
v_l_1708_ = lean_ctor_get(v_t_1704_, 3);
v_r_1709_ = lean_ctor_get(v_t_1704_, 4);
v___x_1710_ = lean_nat_dec_lt(v_k_1705_, v_k_1706_);
if (v___x_1710_ == 0)
{
uint8_t v___x_1711_; 
v___x_1711_ = lean_nat_dec_eq(v_k_1705_, v_k_1706_);
if (v___x_1711_ == 0)
{
v_t_1704_ = v_r_1709_;
goto _start;
}
else
{
lean_object* v___x_1713_; 
lean_inc(v_v_1707_);
v___x_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1713_, 0, v_v_1707_);
return v___x_1713_;
}
}
else
{
v_t_1704_ = v_l_1708_;
goto _start;
}
}
else
{
lean_object* v___x_1715_; 
v___x_1715_ = lean_box(0);
return v___x_1715_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg___boxed(lean_object* v_t_1716_, lean_object* v_k_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_t_1716_, v_k_1717_);
lean_dec(v_k_1717_);
lean_dec(v_t_1716_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0(lean_object* v_pm_1719_, lean_object* v_merger_1720_, lean_object* v_info_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v_subexprPos_1727_; lean_object* v___x_1728_; 
v_subexprPos_1727_ = lean_ctor_get(v_info_1721_, 1);
v___x_1728_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_pm_1719_, v_subexprPos_1727_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v___x_1729_; 
lean_dec_ref(v_merger_1720_);
v___x_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1729_, 0, v_info_1721_);
return v___x_1729_;
}
else
{
lean_object* v_val_1730_; lean_object* v___x_1731_; 
v_val_1730_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_val_1730_);
lean_dec_ref_known(v___x_1728_, 1);
lean_inc(v___y_1725_);
lean_inc_ref(v___y_1724_);
lean_inc(v___y_1723_);
lean_inc_ref(v___y_1722_);
v___x_1731_ = lean_apply_7(v_merger_1720_, v_info_1721_, v_val_1730_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, lean_box(0));
return v___x_1731_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0___boxed(lean_object* v_pm_1732_, lean_object* v_merger_1733_, lean_object* v_info_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0(v_pm_1732_, v_merger_1733_, v_info_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v_pm_1732_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(lean_object* v_merger_1741_, lean_object* v_pm_1742_, lean_object* v_tt_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
if (lean_obj_tag(v_pm_1742_) == 0)
{
lean_object* v___f_1749_; lean_object* v___x_1750_; 
v___f_1749_ = lean_alloc_closure((void*)(l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1749_, 0, v_pm_1742_);
lean_closure_set(v___f_1749_, 1, v_merger_1741_);
v___x_1750_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v___f_1749_, v_tt_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
return v___x_1750_;
}
else
{
lean_object* v___x_1751_; 
lean_dec_ref(v_merger_1741_);
v___x_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1751_, 0, v_tt_1743_);
return v___x_1751_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___boxed(lean_object* v_merger_1752_, lean_object* v_pm_1753_, lean_object* v_tt_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v_merger_1752_, v_pm_1753_, v_tt_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(uint8_t v_useAfter_1761_, lean_object* v_diff_1762_, lean_object* v_info_u2081_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_){
_start:
{
lean_object* v___x_1769_; lean_object* v___f_1770_; 
v___x_1769_ = lean_box(v_useAfter_1761_);
v___f_1770_ = lean_alloc_closure((void*)(l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1770_, 0, v___x_1769_);
if (v_useAfter_1761_ == 0)
{
lean_object* v_changesBefore_1771_; lean_object* v___x_1772_; 
v_changesBefore_1771_ = lean_ctor_get(v_diff_1762_, 0);
lean_inc(v_changesBefore_1771_);
lean_dec_ref(v_diff_1762_);
v___x_1772_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v___f_1770_, v_changesBefore_1771_, v_info_u2081_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_);
return v___x_1772_;
}
else
{
lean_object* v_changesAfter_1773_; lean_object* v___x_1774_; 
v_changesAfter_1773_ = lean_ctor_get(v_diff_1762_, 1);
lean_inc(v_changesAfter_1773_);
lean_dec_ref(v_diff_1762_);
v___x_1774_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v___f_1770_, v_changesAfter_1773_, v_info_u2081_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_);
return v___x_1774_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___boxed(lean_object* v_useAfter_1775_, lean_object* v_diff_1776_, lean_object* v_info_u2081_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_){
_start:
{
uint8_t v_useAfter_boxed_1783_; lean_object* v_res_1784_; 
v_useAfter_boxed_1783_ = lean_unbox(v_useAfter_1775_);
v_res_1784_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(v_useAfter_boxed_1783_, v_diff_1776_, v_info_u2081_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_);
lean_dec(v_a_1781_);
lean_dec_ref(v_a_1780_);
lean_dec(v_a_1779_);
lean_dec_ref(v_a_1778_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0(lean_object* v_00_u03b1_1785_, lean_object* v_merger_1786_, lean_object* v_pm_1787_, lean_object* v_tt_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v_merger_1786_, v_pm_1787_, v_tt_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___boxed(lean_object* v_00_u03b1_1795_, lean_object* v_merger_1796_, lean_object* v_pm_1797_, lean_object* v_tt_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0(v_00_u03b1_1795_, v_merger_1796_, v_pm_1797_, v_tt_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0(lean_object* v_00_u03b4_1805_, lean_object* v_t_1806_, lean_object* v_k_1807_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_t_1806_, v_k_1807_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___boxed(lean_object* v_00_u03b4_1809_, lean_object* v_t_1810_, lean_object* v_k_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0(v_00_u03b4_1809_, v_t_1810_, v_k_1811_);
lean_dec(v_k_1811_);
lean_dec(v_t_1810_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1(lean_object* v_00_u03b1_1813_, lean_object* v_00_u03b2_1814_, lean_object* v_f_1815_, lean_object* v_x_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v___x_1822_; 
v___x_1822_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1815_, v_x_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1823_, lean_object* v_00_u03b2_1824_, lean_object* v_f_1825_, lean_object* v_x_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1(v_00_u03b1_1823_, v_00_u03b2_1824_, v_f_1825_, v_x_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1833_, lean_object* v_00_u03b2_1834_, lean_object* v_f_1835_, size_t v_sz_1836_, size_t v_i_1837_, lean_object* v_bs_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_1835_, v_sz_1836_, v_i_1837_, v_bs_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1845_, lean_object* v_00_u03b2_1846_, lean_object* v_f_1847_, lean_object* v_sz_1848_, lean_object* v_i_1849_, lean_object* v_bs_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
size_t v_sz_boxed_1856_; size_t v_i_boxed_1857_; lean_object* v_res_1858_; 
v_sz_boxed_1856_ = lean_unbox_usize(v_sz_1848_);
lean_dec(v_sz_1848_);
v_i_boxed_1857_ = lean_unbox_usize(v_i_1849_);
lean_dec(v_i_1849_);
v_res_1858_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2(v_00_u03b1_1845_, v_00_u03b2_1846_, v_f_1847_, v_sz_boxed_1856_, v_i_boxed_1857_, v_bs_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(lean_object* v_e_1859_, lean_object* v___y_1860_){
_start:
{
uint8_t v___x_1862_; 
v___x_1862_ = l_Lean_Expr_hasMVar(v_e_1859_);
if (v___x_1862_ == 0)
{
lean_object* v___x_1863_; 
v___x_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1863_, 0, v_e_1859_);
return v___x_1863_;
}
else
{
lean_object* v___x_1864_; lean_object* v_mctx_1865_; lean_object* v___x_1866_; lean_object* v_fst_1867_; lean_object* v_snd_1868_; lean_object* v___x_1869_; lean_object* v_cache_1870_; lean_object* v_zetaDeltaFVarIds_1871_; lean_object* v_postponed_1872_; lean_object* v_diag_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1882_; 
v___x_1864_ = lean_st_ref_get(v___y_1860_);
v_mctx_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc_ref(v_mctx_1865_);
lean_dec(v___x_1864_);
v___x_1866_ = l_Lean_instantiateMVarsCore(v_mctx_1865_, v_e_1859_);
v_fst_1867_ = lean_ctor_get(v___x_1866_, 0);
lean_inc(v_fst_1867_);
v_snd_1868_ = lean_ctor_get(v___x_1866_, 1);
lean_inc(v_snd_1868_);
lean_dec_ref(v___x_1866_);
v___x_1869_ = lean_st_ref_take(v___y_1860_);
v_cache_1870_ = lean_ctor_get(v___x_1869_, 1);
v_zetaDeltaFVarIds_1871_ = lean_ctor_get(v___x_1869_, 2);
v_postponed_1872_ = lean_ctor_get(v___x_1869_, 3);
v_diag_1873_ = lean_ctor_get(v___x_1869_, 4);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1882_ == 0)
{
lean_object* v_unused_1883_; 
v_unused_1883_ = lean_ctor_get(v___x_1869_, 0);
lean_dec(v_unused_1883_);
v___x_1875_ = v___x_1869_;
v_isShared_1876_ = v_isSharedCheck_1882_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_diag_1873_);
lean_inc(v_postponed_1872_);
lean_inc(v_zetaDeltaFVarIds_1871_);
lean_inc(v_cache_1870_);
lean_dec(v___x_1869_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1882_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v_snd_1868_);
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_snd_1868_);
lean_ctor_set(v_reuseFailAlloc_1881_, 1, v_cache_1870_);
lean_ctor_set(v_reuseFailAlloc_1881_, 2, v_zetaDeltaFVarIds_1871_);
lean_ctor_set(v_reuseFailAlloc_1881_, 3, v_postponed_1872_);
lean_ctor_set(v_reuseFailAlloc_1881_, 4, v_diag_1873_);
v___x_1878_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1879_ = lean_st_ref_put(v___y_1860_, v___x_1878_);
v___x_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1880_, 0, v_fst_1867_);
return v___x_1880_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg___boxed(lean_object* v_e_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_e_1884_, v___y_1885_);
lean_dec(v___y_1885_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0(lean_object* v_e_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_e_1888_, v___y_1890_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___boxed(lean_object* v_e_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0(v_e_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
return v_res_1901_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1(void){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__0));
v___x_1904_ = l_Lean_stringToMessageData(v___x_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(uint8_t v_useAfter_1905_, lean_object* v_t_u2080_1906_, lean_object* v_h_u2081_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_){
_start:
{
lean_object* v_names_1913_; lean_object* v_fvarIds_1914_; lean_object* v_type_1915_; lean_object* v_val_x3f_1916_; lean_object* v_isInstance_x3f_1917_; lean_object* v_isType_x3f_1918_; lean_object* v_isInserted_x3f_1919_; lean_object* v_isRemoved_x3f_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1975_; 
v_names_1913_ = lean_ctor_get(v_h_u2081_1907_, 0);
v_fvarIds_1914_ = lean_ctor_get(v_h_u2081_1907_, 1);
v_type_1915_ = lean_ctor_get(v_h_u2081_1907_, 2);
v_val_x3f_1916_ = lean_ctor_get(v_h_u2081_1907_, 3);
v_isInstance_x3f_1917_ = lean_ctor_get(v_h_u2081_1907_, 4);
v_isType_x3f_1918_ = lean_ctor_get(v_h_u2081_1907_, 5);
v_isInserted_x3f_1919_ = lean_ctor_get(v_h_u2081_1907_, 6);
v_isRemoved_x3f_1920_ = lean_ctor_get(v_h_u2081_1907_, 7);
v_isSharedCheck_1975_ = !lean_is_exclusive(v_h_u2081_1907_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1922_ = v_h_u2081_1907_;
v_isShared_1923_ = v_isSharedCheck_1975_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_isRemoved_x3f_1920_);
lean_inc(v_isInserted_x3f_1919_);
lean_inc(v_isType_x3f_1918_);
lean_inc(v_isInstance_x3f_1917_);
lean_inc(v_val_x3f_1916_);
lean_inc(v_type_1915_);
lean_inc(v_fvarIds_1914_);
lean_inc(v_names_1913_);
lean_dec(v_h_u2081_1907_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1975_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___y_1925_; lean_object* v___x_1965_; lean_object* v___x_1966_; uint8_t v___x_1967_; 
v___x_1965_ = lean_unsigned_to_nat(0u);
v___x_1966_ = lean_array_get_size(v_fvarIds_1914_);
v___x_1967_ = lean_nat_dec_lt(v___x_1965_, v___x_1966_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
lean_del_object(v___x_1922_);
lean_dec(v_isRemoved_x3f_1920_);
lean_dec(v_isInserted_x3f_1919_);
lean_dec(v_isType_x3f_1918_);
lean_dec(v_isInstance_x3f_1917_);
lean_dec(v_val_x3f_1916_);
lean_dec_ref(v_type_1915_);
lean_dec_ref(v_fvarIds_1914_);
lean_dec_ref(v_names_1913_);
lean_dec_ref(v_t_u2080_1906_);
v___x_1968_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1);
v___x_1969_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_1968_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
return v___x_1969_;
}
else
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1970_ = lean_array_fget_borrowed(v_fvarIds_1914_, v___x_1965_);
lean_inc(v___x_1970_);
v___x_1971_ = l_Lean_Expr_fvar___override(v___x_1970_);
lean_inc(v_a_1911_);
lean_inc_ref(v_a_1910_);
lean_inc(v_a_1909_);
lean_inc_ref(v_a_1908_);
v___x_1972_ = lean_infer_type(v___x_1971_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; lean_object* v___x_1974_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_a_1973_);
lean_dec_ref_known(v___x_1972_, 1);
v___x_1974_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_a_1973_, v_a_1909_);
v___y_1925_ = v___x_1974_;
goto v___jp_1924_;
}
else
{
v___y_1925_ = v___x_1972_;
goto v___jp_1924_;
}
}
v___jp_1924_:
{
if (lean_obj_tag(v___y_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1927_; 
v_a_1926_ = lean_ctor_get(v___y_1925_, 0);
lean_inc(v_a_1926_);
lean_dec_ref_known(v___y_1925_, 1);
v___x_1927_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(v_t_u2080_1906_, v_a_1926_, v_useAfter_1905_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1929_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref_known(v___x_1927_, 1);
v___x_1929_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(v_useAfter_1905_, v_a_1928_, v_type_1915_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1940_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1932_ = v___x_1929_;
v_isShared_1933_ = v_isSharedCheck_1940_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1929_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1940_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 2, v_a_1930_);
v___x_1935_ = v___x_1922_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_names_1913_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_fvarIds_1914_);
lean_ctor_set(v_reuseFailAlloc_1939_, 2, v_a_1930_);
lean_ctor_set(v_reuseFailAlloc_1939_, 3, v_val_x3f_1916_);
lean_ctor_set(v_reuseFailAlloc_1939_, 4, v_isInstance_x3f_1917_);
lean_ctor_set(v_reuseFailAlloc_1939_, 5, v_isType_x3f_1918_);
lean_ctor_set(v_reuseFailAlloc_1939_, 6, v_isInserted_x3f_1919_);
lean_ctor_set(v_reuseFailAlloc_1939_, 7, v_isRemoved_x3f_1920_);
v___x_1935_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
lean_object* v___x_1937_; 
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v___x_1935_);
v___x_1937_ = v___x_1932_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1935_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
lean_del_object(v___x_1922_);
lean_dec(v_isRemoved_x3f_1920_);
lean_dec(v_isInserted_x3f_1919_);
lean_dec(v_isType_x3f_1918_);
lean_dec(v_isInstance_x3f_1917_);
lean_dec(v_val_x3f_1916_);
lean_dec_ref(v_fvarIds_1914_);
lean_dec_ref(v_names_1913_);
v_a_1941_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1929_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1929_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_del_object(v___x_1922_);
lean_dec(v_isRemoved_x3f_1920_);
lean_dec(v_isInserted_x3f_1919_);
lean_dec(v_isType_x3f_1918_);
lean_dec(v_isInstance_x3f_1917_);
lean_dec(v_val_x3f_1916_);
lean_dec_ref(v_type_1915_);
lean_dec_ref(v_fvarIds_1914_);
lean_dec_ref(v_names_1913_);
v_a_1949_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1927_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1927_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_del_object(v___x_1922_);
lean_dec(v_isRemoved_x3f_1920_);
lean_dec(v_isInserted_x3f_1919_);
lean_dec(v_isType_x3f_1918_);
lean_dec(v_isInstance_x3f_1917_);
lean_dec(v_val_x3f_1916_);
lean_dec_ref(v_type_1915_);
lean_dec_ref(v_fvarIds_1914_);
lean_dec_ref(v_names_1913_);
lean_dec_ref(v_t_u2080_1906_);
v_a_1957_ = lean_ctor_get(v___y_1925_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___y_1925_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___y_1925_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___y_1925_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___boxed(lean_object* v_useAfter_1976_, lean_object* v_t_u2080_1977_, lean_object* v_h_u2081_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_){
_start:
{
uint8_t v_useAfter_boxed_1984_; lean_object* v_res_1985_; 
v_useAfter_boxed_1984_ = lean_unbox(v_useAfter_1976_);
v_res_1985_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(v_useAfter_boxed_1984_, v_t_u2080_1977_, v_h_u2081_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
lean_dec(v_a_1982_);
lean_dec_ref(v_a_1981_);
lean_dec(v_a_1980_);
lean_dec_ref(v_a_1979_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(lean_object* v_ctx_u2080_1989_, uint8_t v_useAfter_1990_, lean_object* v_h_u2081_1991_, lean_object* v___x_1992_, lean_object* v___x_1993_, lean_object* v_as_1994_, size_t v_sz_1995_, size_t v_i_1996_, lean_object* v_b_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
uint8_t v___x_2003_; 
v___x_2003_ = lean_usize_dec_lt(v_i_1996_, v_sz_1995_);
if (v___x_2003_ == 0)
{
lean_object* v___x_2004_; 
lean_dec_ref(v___x_1993_);
lean_dec_ref(v___x_1992_);
lean_dec_ref(v_h_u2081_1991_);
v___x_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2004_, 0, v_b_1997_);
return v___x_2004_;
}
else
{
lean_object* v_a_2005_; lean_object* v_fst_2006_; lean_object* v_snd_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2103_; 
lean_dec_ref(v_b_1997_);
v_a_2005_ = lean_array_uget(v_as_1994_, v_i_1996_);
v_fst_2006_ = lean_ctor_get(v_a_2005_, 0);
v_snd_2007_ = lean_ctor_get(v_a_2005_, 1);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_a_2005_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2009_ = v_a_2005_;
v_isShared_2010_ = v_isSharedCheck_2103_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_snd_2007_);
lean_inc(v_fst_2006_);
lean_dec(v_a_2005_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2103_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2011_; uint8_t v___x_2012_; 
v___x_2011_ = lean_box(0);
v___x_2012_ = l_Lean_LocalContext_contains(v_ctx_u2080_1989_, v_snd_2007_);
lean_dec(v_snd_2007_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2013_ = lean_box(0);
v___x_2014_ = l_Lean_Name_str___override(v___x_2013_, v_fst_2006_);
v___x_2015_ = l_Lean_LocalContext_findFromUserName_x3f(v_ctx_u2080_1989_, v___x_2014_);
lean_dec(v___x_2014_);
if (lean_obj_tag(v___x_2015_) == 1)
{
lean_object* v_val_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2054_; 
lean_dec_ref(v___x_1993_);
lean_dec_ref(v___x_1992_);
v_val_2016_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2018_ = v___x_2015_;
v_isShared_2019_ = v_isSharedCheck_2054_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_val_2016_);
lean_dec(v___x_2015_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2054_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = l_Lean_LocalDecl_type(v_val_2016_);
lean_dec(v_val_2016_);
v___x_2021_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v___x_2020_, v___y_1999_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2023_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2022_);
lean_dec_ref_known(v___x_2021_, 1);
v___x_2023_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(v_useAfter_1990_, v_a_2022_, v_h_u2081_1991_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2037_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2026_ = v___x_2023_;
v_isShared_2027_ = v_isSharedCheck_2037_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2023_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2037_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v_a_2024_);
v___x_2029_ = v___x_2018_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
lean_object* v___x_2031_; 
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 1, v___x_2011_);
lean_ctor_set(v___x_2009_, 0, v___x_2029_);
v___x_2031_ = v___x_2009_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2029_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v___x_2011_);
v___x_2031_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
lean_object* v___x_2033_; 
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v___x_2031_);
v___x_2033_ = v___x_2026_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_del_object(v___x_2018_);
lean_del_object(v___x_2009_);
v_a_2038_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2023_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2023_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
else
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
lean_del_object(v___x_2018_);
lean_del_object(v___x_2009_);
lean_dec_ref(v_h_u2081_1991_);
v_a_2046_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2048_ = v___x_2021_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2021_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2049_ == 0)
{
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_2046_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
}
else
{
lean_dec(v___x_2015_);
if (v_useAfter_1990_ == 0)
{
lean_object* v_type_2055_; lean_object* v_val_x3f_2056_; lean_object* v_isInstance_x3f_2057_; lean_object* v_isType_x3f_2058_; lean_object* v_isInserted_x3f_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2073_; 
v_type_2055_ = lean_ctor_get(v_h_u2081_1991_, 2);
v_val_x3f_2056_ = lean_ctor_get(v_h_u2081_1991_, 3);
v_isInstance_x3f_2057_ = lean_ctor_get(v_h_u2081_1991_, 4);
v_isType_x3f_2058_ = lean_ctor_get(v_h_u2081_1991_, 5);
v_isInserted_x3f_2059_ = lean_ctor_get(v_h_u2081_1991_, 6);
v_isSharedCheck_2073_ = !lean_is_exclusive(v_h_u2081_1991_);
if (v_isSharedCheck_2073_ == 0)
{
lean_object* v_unused_2074_; lean_object* v_unused_2075_; lean_object* v_unused_2076_; 
v_unused_2074_ = lean_ctor_get(v_h_u2081_1991_, 7);
lean_dec(v_unused_2074_);
v_unused_2075_ = lean_ctor_get(v_h_u2081_1991_, 1);
lean_dec(v_unused_2075_);
v_unused_2076_ = lean_ctor_get(v_h_u2081_1991_, 0);
lean_dec(v_unused_2076_);
v___x_2061_ = v_h_u2081_1991_;
v_isShared_2062_ = v_isSharedCheck_2073_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_isInserted_x3f_2059_);
lean_inc(v_isType_x3f_2058_);
lean_inc(v_isInstance_x3f_2057_);
lean_inc(v_val_x3f_2056_);
lean_inc(v_type_2055_);
lean_dec(v_h_u2081_1991_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2073_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2066_; 
v___x_2063_ = lean_box(v___x_2003_);
v___x_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 7, v___x_2064_);
lean_ctor_set(v___x_2061_, 1, v___x_1993_);
lean_ctor_set(v___x_2061_, 0, v___x_1992_);
v___x_2066_ = v___x_2061_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_2072_, 2, v_type_2055_);
lean_ctor_set(v_reuseFailAlloc_2072_, 3, v_val_x3f_2056_);
lean_ctor_set(v_reuseFailAlloc_2072_, 4, v_isInstance_x3f_2057_);
lean_ctor_set(v_reuseFailAlloc_2072_, 5, v_isType_x3f_2058_);
lean_ctor_set(v_reuseFailAlloc_2072_, 6, v_isInserted_x3f_2059_);
lean_ctor_set(v_reuseFailAlloc_2072_, 7, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 1, v___x_2011_);
lean_ctor_set(v___x_2009_, 0, v___x_2067_);
v___x_2069_ = v___x_2009_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2067_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v___x_2011_);
v___x_2069_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2070_; 
v___x_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
return v___x_2070_;
}
}
}
}
else
{
lean_object* v_type_2077_; lean_object* v_val_x3f_2078_; lean_object* v_isInstance_x3f_2079_; lean_object* v_isType_x3f_2080_; lean_object* v_isRemoved_x3f_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2095_; 
v_type_2077_ = lean_ctor_get(v_h_u2081_1991_, 2);
v_val_x3f_2078_ = lean_ctor_get(v_h_u2081_1991_, 3);
v_isInstance_x3f_2079_ = lean_ctor_get(v_h_u2081_1991_, 4);
v_isType_x3f_2080_ = lean_ctor_get(v_h_u2081_1991_, 5);
v_isRemoved_x3f_2081_ = lean_ctor_get(v_h_u2081_1991_, 7);
v_isSharedCheck_2095_ = !lean_is_exclusive(v_h_u2081_1991_);
if (v_isSharedCheck_2095_ == 0)
{
lean_object* v_unused_2096_; lean_object* v_unused_2097_; lean_object* v_unused_2098_; 
v_unused_2096_ = lean_ctor_get(v_h_u2081_1991_, 6);
lean_dec(v_unused_2096_);
v_unused_2097_ = lean_ctor_get(v_h_u2081_1991_, 1);
lean_dec(v_unused_2097_);
v_unused_2098_ = lean_ctor_get(v_h_u2081_1991_, 0);
lean_dec(v_unused_2098_);
v___x_2083_ = v_h_u2081_1991_;
v_isShared_2084_ = v_isSharedCheck_2095_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_isRemoved_x3f_2081_);
lean_inc(v_isType_x3f_2080_);
lean_inc(v_isInstance_x3f_2079_);
lean_inc(v_val_x3f_2078_);
lean_inc(v_type_2077_);
lean_dec(v_h_u2081_1991_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2095_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2088_; 
v___x_2085_ = lean_box(v___x_2003_);
v___x_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 6, v___x_2086_);
lean_ctor_set(v___x_2083_, 1, v___x_1993_);
lean_ctor_set(v___x_2083_, 0, v___x_1992_);
v___x_2088_ = v___x_2083_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_2094_, 2, v_type_2077_);
lean_ctor_set(v_reuseFailAlloc_2094_, 3, v_val_x3f_2078_);
lean_ctor_set(v_reuseFailAlloc_2094_, 4, v_isInstance_x3f_2079_);
lean_ctor_set(v_reuseFailAlloc_2094_, 5, v_isType_x3f_2080_);
lean_ctor_set(v_reuseFailAlloc_2094_, 6, v___x_2086_);
lean_ctor_set(v_reuseFailAlloc_2094_, 7, v_isRemoved_x3f_2081_);
v___x_2088_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 1, v___x_2011_);
lean_ctor_set(v___x_2009_, 0, v___x_2089_);
v___x_2091_ = v___x_2009_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v___x_2011_);
v___x_2091_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2092_; 
v___x_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
return v___x_2092_;
}
}
}
}
}
}
else
{
lean_object* v___x_2099_; size_t v___x_2100_; size_t v___x_2101_; 
lean_del_object(v___x_2009_);
lean_dec(v_fst_2006_);
v___x_2099_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___closed__0));
v___x_2100_ = ((size_t)1ULL);
v___x_2101_ = lean_usize_add(v_i_1996_, v___x_2100_);
v_i_1996_ = v___x_2101_;
v_b_1997_ = v___x_2099_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___boxed(lean_object* v_ctx_u2080_2104_, lean_object* v_useAfter_2105_, lean_object* v_h_u2081_2106_, lean_object* v___x_2107_, lean_object* v___x_2108_, lean_object* v_as_2109_, lean_object* v_sz_2110_, lean_object* v_i_2111_, lean_object* v_b_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
uint8_t v_useAfter_boxed_2118_; size_t v_sz_boxed_2119_; size_t v_i_boxed_2120_; lean_object* v_res_2121_; 
v_useAfter_boxed_2118_ = lean_unbox(v_useAfter_2105_);
v_sz_boxed_2119_ = lean_unbox_usize(v_sz_2110_);
lean_dec(v_sz_2110_);
v_i_boxed_2120_ = lean_unbox_usize(v_i_2111_);
lean_dec(v_i_2111_);
v_res_2121_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(v_ctx_u2080_2104_, v_useAfter_boxed_2118_, v_h_u2081_2106_, v___x_2107_, v___x_2108_, v_as_2109_, v_sz_boxed_2119_, v_i_boxed_2120_, v_b_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec_ref(v_as_2109_);
lean_dec_ref(v_ctx_u2080_2104_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(uint8_t v_useAfter_2122_, lean_object* v_ctx_u2080_2123_, lean_object* v_h_u2081_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_){
_start:
{
lean_object* v_names_2130_; lean_object* v_fvarIds_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; size_t v_sz_2134_; size_t v___x_2135_; lean_object* v___x_2136_; 
v_names_2130_ = lean_ctor_get(v_h_u2081_2124_, 0);
v_fvarIds_2131_ = lean_ctor_get(v_h_u2081_2124_, 1);
v___x_2132_ = l_Array_zip___redArg(v_names_2130_, v_fvarIds_2131_);
v___x_2133_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___closed__0));
v_sz_2134_ = lean_array_size(v___x_2132_);
v___x_2135_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_2131_);
lean_inc_ref(v_names_2130_);
lean_inc_ref(v_h_u2081_2124_);
v___x_2136_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(v_ctx_u2080_2123_, v_useAfter_2122_, v_h_u2081_2124_, v_names_2130_, v_fvarIds_2131_, v___x_2132_, v_sz_2134_, v___x_2135_, v___x_2133_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_);
lean_dec_ref(v___x_2132_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2149_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2139_ = v___x_2136_;
v_isShared_2140_ = v_isSharedCheck_2149_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2136_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2149_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v_fst_2141_; 
v_fst_2141_ = lean_ctor_get(v_a_2137_, 0);
lean_inc(v_fst_2141_);
lean_dec(v_a_2137_);
if (lean_obj_tag(v_fst_2141_) == 0)
{
lean_object* v___x_2143_; 
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v_h_u2081_2124_);
v___x_2143_ = v___x_2139_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_h_u2081_2124_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
else
{
lean_object* v_val_2145_; lean_object* v___x_2147_; 
lean_dec_ref(v_h_u2081_2124_);
v_val_2145_ = lean_ctor_get(v_fst_2141_, 0);
lean_inc(v_val_2145_);
lean_dec_ref_known(v_fst_2141_, 1);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v_val_2145_);
v___x_2147_ = v___x_2139_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_val_2145_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
else
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
lean_dec_ref(v_h_u2081_2124_);
v_a_2150_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2136_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2136_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2150_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle___boxed(lean_object* v_useAfter_2158_, lean_object* v_ctx_u2080_2159_, lean_object* v_h_u2081_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_){
_start:
{
uint8_t v_useAfter_boxed_2166_; lean_object* v_res_2167_; 
v_useAfter_boxed_2166_ = lean_unbox(v_useAfter_2158_);
v_res_2167_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(v_useAfter_boxed_2166_, v_ctx_u2080_2159_, v_h_u2081_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
lean_dec(v_a_2164_);
lean_dec_ref(v_a_2163_);
lean_dec(v_a_2162_);
lean_dec_ref(v_a_2161_);
lean_dec_ref(v_ctx_u2080_2159_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(uint8_t v_useAfter_2168_, lean_object* v_lctx_u2080_2169_, size_t v_sz_2170_, size_t v_i_2171_, lean_object* v_bs_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
uint8_t v___x_2178_; 
v___x_2178_ = lean_usize_dec_lt(v_i_2171_, v_sz_2170_);
if (v___x_2178_ == 0)
{
lean_object* v___x_2179_; 
v___x_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2179_, 0, v_bs_2172_);
return v___x_2179_;
}
else
{
lean_object* v_v_2180_; lean_object* v___x_2181_; lean_object* v_bs_x27_2182_; lean_object* v___x_2183_; 
v_v_2180_ = lean_array_uget(v_bs_2172_, v_i_2171_);
v___x_2181_ = lean_unsigned_to_nat(0u);
v_bs_x27_2182_ = lean_array_uset(v_bs_2172_, v_i_2171_, v___x_2181_);
v___x_2183_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(v_useAfter_2168_, v_lctx_u2080_2169_, v_v_2180_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; size_t v___x_2185_; size_t v___x_2186_; lean_object* v___x_2187_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_a_2184_);
lean_dec_ref_known(v___x_2183_, 1);
v___x_2185_ = ((size_t)1ULL);
v___x_2186_ = lean_usize_add(v_i_2171_, v___x_2185_);
v___x_2187_ = lean_array_uset(v_bs_x27_2182_, v_i_2171_, v_a_2184_);
v_i_2171_ = v___x_2186_;
v_bs_2172_ = v___x_2187_;
goto _start;
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_dec_ref(v_bs_x27_2182_);
v_a_2189_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2183_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2183_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0___boxed(lean_object* v_useAfter_2197_, lean_object* v_lctx_u2080_2198_, lean_object* v_sz_2199_, lean_object* v_i_2200_, lean_object* v_bs_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
uint8_t v_useAfter_boxed_2207_; size_t v_sz_boxed_2208_; size_t v_i_boxed_2209_; lean_object* v_res_2210_; 
v_useAfter_boxed_2207_ = lean_unbox(v_useAfter_2197_);
v_sz_boxed_2208_ = lean_unbox_usize(v_sz_2199_);
lean_dec(v_sz_2199_);
v_i_boxed_2209_ = lean_unbox_usize(v_i_2200_);
lean_dec(v_i_2200_);
v_res_2210_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(v_useAfter_boxed_2207_, v_lctx_u2080_2198_, v_sz_boxed_2208_, v_i_boxed_2209_, v_bs_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec_ref(v_lctx_u2080_2198_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(uint8_t v_useAfter_2211_, lean_object* v_lctx_u2080_2212_, lean_object* v_hs_u2081_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_){
_start:
{
size_t v_sz_2219_; size_t v___x_2220_; lean_object* v___x_2221_; 
v_sz_2219_ = lean_array_size(v_hs_u2081_2213_);
v___x_2220_ = ((size_t)0ULL);
v___x_2221_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(v_useAfter_2211_, v_lctx_u2080_2212_, v_sz_2219_, v___x_2220_, v_hs_u2081_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses___boxed(lean_object* v_useAfter_2222_, lean_object* v_lctx_u2080_2223_, lean_object* v_hs_u2081_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_){
_start:
{
uint8_t v_useAfter_boxed_2230_; lean_object* v_res_2231_; 
v_useAfter_boxed_2230_ = lean_unbox(v_useAfter_2222_);
v_res_2231_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(v_useAfter_boxed_2230_, v_lctx_u2080_2223_, v_hs_u2081_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
lean_dec(v_a_2228_);
lean_dec_ref(v_a_2227_);
lean_dec(v_a_2226_);
lean_dec_ref(v_a_2225_);
lean_dec_ref(v_lctx_u2080_2223_);
return v_res_2231_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2(void){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__1));
v___x_2237_ = l_Lean_stringToMessageData(v___x_2236_);
return v___x_2237_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4(void){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__3));
v___x_2240_ = l_Lean_stringToMessageData(v___x_2239_);
return v___x_2240_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6(void){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2242_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__5));
v___x_2243_ = l_Lean_stringToMessageData(v___x_2242_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(uint8_t v_useAfter_2244_, lean_object* v_g_u2080_2245_, lean_object* v_i_u2081_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_){
_start:
{
lean_object* v___x_2252_; lean_object* v_mctx_2253_; lean_object* v___x_2254_; 
v___x_2252_ = lean_st_ref_get(v_a_2248_);
v_mctx_2253_ = lean_ctor_get(v___x_2252_, 0);
lean_inc_ref(v_mctx_2253_);
lean_dec(v___x_2252_);
v___x_2254_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2253_, v_g_u2080_2245_);
lean_dec_ref(v_mctx_2253_);
if (lean_obj_tag(v___x_2254_) == 1)
{
lean_object* v_val_2255_; lean_object* v_lctx_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v_toInteractiveGoalCore_2261_; lean_object* v_fst_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2359_; 
v_val_2255_ = lean_ctor_get(v___x_2254_, 0);
lean_inc(v_val_2255_);
lean_dec_ref_known(v___x_2254_, 1);
v_lctx_2256_ = lean_ctor_get(v_val_2255_, 1);
lean_inc_ref(v_lctx_2256_);
lean_dec(v_val_2255_);
v___x_2257_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2249_);
v___x_2258_ = lean_box(1);
v___x_2259_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2257_);
lean_ctor_set(v___x_2259_, 1, v___x_2258_);
lean_ctor_set(v___x_2259_, 2, v___x_2258_);
v___x_2260_ = l_Lean_LocalContext_sanitizeNames(v_lctx_2256_, v___x_2259_);
v_toInteractiveGoalCore_2261_ = lean_ctor_get(v_i_u2081_2246_, 0);
lean_inc_ref(v_toInteractiveGoalCore_2261_);
v_fst_2262_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2359_ == 0)
{
lean_object* v_unused_2360_; 
v_unused_2360_ = lean_ctor_get(v___x_2260_, 1);
lean_dec(v_unused_2360_);
v___x_2264_ = v___x_2260_;
v_isShared_2265_ = v_isSharedCheck_2359_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_fst_2262_);
lean_dec(v___x_2260_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2359_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v_userName_x3f_2266_; lean_object* v_goalPrefix_2267_; lean_object* v_mvarId_2268_; lean_object* v_isRemoved_x3f_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2356_; 
v_userName_x3f_2266_ = lean_ctor_get(v_i_u2081_2246_, 1);
v_goalPrefix_2267_ = lean_ctor_get(v_i_u2081_2246_, 2);
v_mvarId_2268_ = lean_ctor_get(v_i_u2081_2246_, 3);
v_isRemoved_x3f_2269_ = lean_ctor_get(v_i_u2081_2246_, 5);
v_isSharedCheck_2356_ = !lean_is_exclusive(v_i_u2081_2246_);
if (v_isSharedCheck_2356_ == 0)
{
lean_object* v_unused_2357_; lean_object* v_unused_2358_; 
v_unused_2357_ = lean_ctor_get(v_i_u2081_2246_, 4);
lean_dec(v_unused_2357_);
v_unused_2358_ = lean_ctor_get(v_i_u2081_2246_, 0);
lean_dec(v_unused_2358_);
v___x_2271_ = v_i_u2081_2246_;
v_isShared_2272_ = v_isSharedCheck_2356_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_isRemoved_x3f_2269_);
lean_inc(v_mvarId_2268_);
lean_inc(v_goalPrefix_2267_);
lean_inc(v_userName_x3f_2266_);
lean_dec(v_i_u2081_2246_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2356_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v_hyps_2273_; lean_object* v_type_2274_; lean_object* v_ctx_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2355_; 
v_hyps_2273_ = lean_ctor_get(v_toInteractiveGoalCore_2261_, 0);
v_type_2274_ = lean_ctor_get(v_toInteractiveGoalCore_2261_, 1);
v_ctx_2275_ = lean_ctor_get(v_toInteractiveGoalCore_2261_, 2);
v_isSharedCheck_2355_ = !lean_is_exclusive(v_toInteractiveGoalCore_2261_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2277_ = v_toInteractiveGoalCore_2261_;
v_isShared_2278_ = v_isSharedCheck_2355_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_ctx_2275_);
lean_inc(v_type_2274_);
lean_inc(v_hyps_2273_);
lean_dec(v_toInteractiveGoalCore_2261_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2355_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2279_; 
v___x_2279_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(v_useAfter_2244_, v_fst_2262_, v_hyps_2273_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_);
lean_dec(v_fst_2262_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref_known(v___x_2279_, 1);
v___x_2281_ = l_Lean_Expr_mvar___override(v_g_u2080_2245_);
lean_inc(v_a_2250_);
lean_inc_ref(v_a_2249_);
lean_inc(v_a_2248_);
lean_inc_ref(v_a_2247_);
v___x_2282_ = lean_infer_type(v___x_2281_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v___x_2284_; lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2338_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2283_);
lean_dec_ref_known(v___x_2282_, 1);
v___x_2284_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_a_2283_, v_a_2248_);
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2287_ = v___x_2284_;
v_isShared_2288_ = v_isSharedCheck_2338_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2284_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2338_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2289_; lean_object* v_mctx_2290_; lean_object* v___x_2291_; 
v___x_2289_ = lean_st_ref_get(v_a_2248_);
v_mctx_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc_ref(v_mctx_2290_);
lean_dec(v___x_2289_);
v___x_2291_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2290_, v_mvarId_2268_);
lean_dec_ref(v_mctx_2290_);
if (lean_obj_tag(v___x_2291_) == 1)
{
lean_object* v_val_2292_; lean_object* v_type_2293_; lean_object* v___x_2294_; lean_object* v_a_2295_; lean_object* v___x_2296_; 
lean_del_object(v___x_2287_);
lean_del_object(v___x_2264_);
v_val_2292_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_val_2292_);
lean_dec_ref_known(v___x_2291_, 1);
v_type_2293_ = lean_ctor_get(v_val_2292_, 2);
lean_inc_ref(v_type_2293_);
lean_dec(v_val_2292_);
v___x_2294_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_type_2293_, v_a_2248_);
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
lean_dec_ref(v___x_2294_);
v___x_2296_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(v_a_2285_, v_a_2295_, v_useAfter_2244_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; lean_object* v___x_2298_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_a_2297_);
lean_dec_ref_known(v___x_2296_, 1);
v___x_2298_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(v_useAfter_2244_, v_a_2297_, v_type_2274_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2313_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2301_ = v___x_2298_;
v_isShared_2302_ = v_isSharedCheck_2313_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2298_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2313_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 1, v_a_2299_);
lean_ctor_set(v___x_2277_, 0, v_a_2280_);
v___x_2304_ = v___x_2277_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2280_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v_a_2299_);
lean_ctor_set(v_reuseFailAlloc_2312_, 2, v_ctx_2275_);
v___x_2304_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
lean_object* v___x_2305_; lean_object* v___x_2307_; 
v___x_2305_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__0));
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 4, v___x_2305_);
lean_ctor_set(v___x_2271_, 0, v___x_2304_);
v___x_2307_ = v___x_2271_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2304_);
lean_ctor_set(v_reuseFailAlloc_2311_, 1, v_userName_x3f_2266_);
lean_ctor_set(v_reuseFailAlloc_2311_, 2, v_goalPrefix_2267_);
lean_ctor_set(v_reuseFailAlloc_2311_, 3, v_mvarId_2268_);
lean_ctor_set(v_reuseFailAlloc_2311_, 4, v___x_2305_);
lean_ctor_set(v_reuseFailAlloc_2311_, 5, v_isRemoved_x3f_2269_);
v___x_2307_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
lean_object* v___x_2309_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v___x_2307_);
v___x_2309_ = v___x_2301_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2307_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_dec(v_a_2280_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_ctx_2275_);
lean_del_object(v___x_2271_);
lean_dec(v_isRemoved_x3f_2269_);
lean_dec(v_mvarId_2268_);
lean_dec_ref(v_goalPrefix_2267_);
lean_dec(v_userName_x3f_2266_);
v_a_2314_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2298_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2298_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
lean_dec(v_a_2280_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_ctx_2275_);
lean_dec_ref(v_type_2274_);
lean_del_object(v___x_2271_);
lean_dec(v_isRemoved_x3f_2269_);
lean_dec(v_mvarId_2268_);
lean_dec_ref(v_goalPrefix_2267_);
lean_dec(v_userName_x3f_2266_);
v_a_2322_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2324_ = v___x_2296_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2296_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2325_ == 0)
{
v___x_2327_ = v___x_2324_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2322_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
else
{
lean_object* v___x_2330_; lean_object* v___x_2332_; 
lean_dec(v___x_2291_);
lean_dec(v_a_2285_);
lean_dec(v_a_2280_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_ctx_2275_);
lean_dec_ref(v_type_2274_);
lean_del_object(v___x_2271_);
lean_dec(v_isRemoved_x3f_2269_);
lean_dec_ref(v_goalPrefix_2267_);
lean_dec(v_userName_x3f_2266_);
v___x_2330_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2);
if (v_isShared_2288_ == 0)
{
lean_ctor_set_tag(v___x_2287_, 1);
lean_ctor_set(v___x_2287_, 0, v_mvarId_2268_);
v___x_2332_ = v___x_2287_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_mvarId_2268_);
v___x_2332_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
lean_object* v___x_2334_; 
if (v_isShared_2265_ == 0)
{
lean_ctor_set_tag(v___x_2264_, 7);
lean_ctor_set(v___x_2264_, 1, v___x_2332_);
lean_ctor_set(v___x_2264_, 0, v___x_2330_);
v___x_2334_ = v___x_2264_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2330_);
lean_ctor_set(v_reuseFailAlloc_2336_, 1, v___x_2332_);
v___x_2334_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
lean_object* v___x_2335_; 
v___x_2335_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_2334_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_);
return v___x_2335_;
}
}
}
}
}
else
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2346_; 
lean_dec(v_a_2280_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_ctx_2275_);
lean_dec_ref(v_type_2274_);
lean_del_object(v___x_2271_);
lean_dec(v_isRemoved_x3f_2269_);
lean_dec(v_mvarId_2268_);
lean_dec_ref(v_goalPrefix_2267_);
lean_dec(v_userName_x3f_2266_);
lean_del_object(v___x_2264_);
v_a_2339_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2341_ = v___x_2282_;
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2282_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2344_; 
if (v_isShared_2342_ == 0)
{
v___x_2344_ = v___x_2341_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2339_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
lean_del_object(v___x_2277_);
lean_dec_ref(v_ctx_2275_);
lean_dec_ref(v_type_2274_);
lean_del_object(v___x_2271_);
lean_dec(v_isRemoved_x3f_2269_);
lean_dec(v_mvarId_2268_);
lean_dec_ref(v_goalPrefix_2267_);
lean_dec(v_userName_x3f_2266_);
lean_del_object(v___x_2264_);
lean_dec(v_g_u2080_2245_);
v_a_2347_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2279_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2279_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
lean_dec(v___x_2254_);
lean_dec_ref(v_i_u2081_2246_);
v___x_2361_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4);
v___x_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2362_, 0, v_g_u2080_2245_);
v___x_2363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2361_);
lean_ctor_set(v___x_2363_, 1, v___x_2362_);
v___x_2364_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6);
v___x_2365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2363_);
lean_ctor_set(v___x_2365_, 1, v___x_2364_);
v___x_2366_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_2365_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_);
return v___x_2366_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___boxed(lean_object* v_useAfter_2367_, lean_object* v_g_u2080_2368_, lean_object* v_i_u2081_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_){
_start:
{
uint8_t v_useAfter_boxed_2375_; lean_object* v_res_2376_; 
v_useAfter_boxed_2375_ = lean_unbox(v_useAfter_2367_);
v_res_2376_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(v_useAfter_boxed_2375_, v_g_u2080_2368_, v_i_u2081_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_);
lean_dec(v_a_2373_);
lean_dec_ref(v_a_2372_);
lean_dec(v_a_2371_);
lean_dec_ref(v_a_2370_);
return v_res_2376_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(lean_object* v_opts_2377_, lean_object* v_opt_2378_){
_start:
{
lean_object* v_name_2379_; lean_object* v_defValue_2380_; lean_object* v_map_2381_; lean_object* v___x_2382_; 
v_name_2379_ = lean_ctor_get(v_opt_2378_, 0);
v_defValue_2380_ = lean_ctor_get(v_opt_2378_, 1);
v_map_2381_ = lean_ctor_get(v_opts_2377_, 0);
v___x_2382_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2381_, v_name_2379_);
if (lean_obj_tag(v___x_2382_) == 0)
{
uint8_t v___x_2383_; 
v___x_2383_ = lean_unbox(v_defValue_2380_);
return v___x_2383_;
}
else
{
lean_object* v_val_2384_; 
v_val_2384_ = lean_ctor_get(v___x_2382_, 0);
lean_inc(v_val_2384_);
lean_dec_ref_known(v___x_2382_, 1);
if (lean_obj_tag(v_val_2384_) == 1)
{
uint8_t v_v_2385_; 
v_v_2385_ = lean_ctor_get_uint8(v_val_2384_, 0);
lean_dec_ref_known(v_val_2384_, 0);
return v_v_2385_;
}
else
{
uint8_t v___x_2386_; 
lean_dec(v_val_2384_);
v___x_2386_ = lean_unbox(v_defValue_2380_);
return v___x_2386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0___boxed(lean_object* v_opts_2387_, lean_object* v_opt_2388_){
_start:
{
uint8_t v_res_2389_; lean_object* v_r_2390_; 
v_res_2389_ = l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(v_opts_2387_, v_opt_2388_);
lean_dec_ref(v_opt_2388_);
lean_dec_ref(v_opts_2387_);
v_r_2390_ = lean_box(v_res_2389_);
return v_r_2390_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(lean_object* v_x_2391_, lean_object* v_x_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
if (lean_obj_tag(v_x_2392_) == 0)
{
lean_object* v___x_2398_; 
v___x_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2398_, 0, v_x_2391_);
return v___x_2398_;
}
else
{
lean_object* v_head_2399_; lean_object* v_tail_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v_head_2399_ = lean_ctor_get(v_x_2392_, 0);
lean_inc_n(v_head_2399_, 2);
v_tail_2400_ = lean_ctor_get(v_x_2392_, 1);
lean_inc(v_tail_2400_);
lean_dec_ref_known(v_x_2392_, 2);
v___x_2401_ = l_Lean_Expr_mvar___override(v_head_2399_);
v___x_2402_ = l_Lean_Meta_getMVars(v___x_2401_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_a_2403_);
lean_dec_ref_known(v___x_2402_, 1);
v___x_2404_ = l_Lean_MVarIdSet_ofArray(v_a_2403_);
lean_dec(v_a_2403_);
v___x_2405_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_head_2399_, v___x_2404_, v_x_2391_);
v_x_2391_ = v___x_2405_;
v_x_2392_ = v_tail_2400_;
goto _start;
}
else
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2414_; 
lean_dec(v_tail_2400_);
lean_dec(v_head_2399_);
lean_dec(v_x_2391_);
v_a_2407_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2409_ = v___x_2402_;
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2402_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
if (v_isShared_2410_ == 0)
{
v___x_2412_ = v___x_2409_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_a_2407_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1___boxed(lean_object* v_x_2415_, lean_object* v_x_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(v_x_2415_, v_x_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(lean_object* v_lctx_2423_, lean_object* v_localInsts_2424_, lean_object* v_x_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v___x_2431_; 
v___x_2431_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2423_, v_localInsts_2424_, v_x_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2439_; 
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v___x_2431_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2431_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2435_ == 0)
{
v___x_2437_ = v___x_2434_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2432_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
v_a_2440_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2431_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2431_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg___boxed(lean_object* v_lctx_2448_, lean_object* v_localInsts_2449_, lean_object* v_x_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(v_lctx_2448_, v_localInsts_2449_, v_x_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
return v_res_2456_;
}
}
static lean_object* _init_l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2458_ = ((lean_object*)(l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__0));
v___x_2459_ = l_Lean_stringToMessageData(v___x_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(lean_object* v_goal_2460_, lean_object* v_action_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v___x_2467_; lean_object* v_mctx_2468_; lean_object* v___x_2469_; 
v___x_2467_ = lean_st_ref_get(v___y_2463_);
v_mctx_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc_ref(v_mctx_2468_);
lean_dec(v___x_2467_);
v___x_2469_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2468_, v_goal_2460_);
lean_dec_ref(v_mctx_2468_);
if (lean_obj_tag(v___x_2469_) == 1)
{
lean_object* v_val_2470_; lean_object* v_lctx_2471_; lean_object* v_localInstances_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v_fst_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
lean_dec(v_goal_2460_);
v_val_2470_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_val_2470_);
lean_dec_ref_known(v___x_2469_, 1);
v_lctx_2471_ = lean_ctor_get(v_val_2470_, 1);
v_localInstances_2472_ = lean_ctor_get(v_val_2470_, 4);
lean_inc_ref(v_localInstances_2472_);
v___x_2473_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2464_);
v___x_2474_ = lean_box(1);
v___x_2475_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2473_);
lean_ctor_set(v___x_2475_, 1, v___x_2474_);
lean_ctor_set(v___x_2475_, 2, v___x_2474_);
lean_inc_ref(v_lctx_2471_);
v___x_2476_ = l_Lean_LocalContext_sanitizeNames(v_lctx_2471_, v___x_2475_);
v_fst_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc_n(v_fst_2477_, 2);
lean_dec_ref(v___x_2476_);
v___x_2478_ = lean_apply_2(v_action_2461_, v_fst_2477_, v_val_2470_);
v___x_2479_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(v_fst_2477_, v_localInstances_2472_, v___x_2478_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
return v___x_2479_;
}
else
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
lean_dec(v___x_2469_);
lean_dec_ref(v_action_2461_);
v___x_2480_ = lean_obj_once(&l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1, &l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1_once, _init_l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1);
v___x_2481_ = l_Lean_MessageData_ofName(v_goal_2460_);
v___x_2482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2480_);
lean_ctor_set(v___x_2482_, 1, v___x_2481_);
v___x_2483_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_2482_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
return v___x_2483_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___boxed(lean_object* v_goal_2484_, lean_object* v_action_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(v_goal_2484_, v_action_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
return v_res_2491_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4(lean_object* v___x_2492_, lean_object* v_x_2493_){
_start:
{
if (lean_obj_tag(v_x_2493_) == 0)
{
uint8_t v___x_2494_; 
v___x_2494_ = 0;
return v___x_2494_;
}
else
{
lean_object* v_head_2495_; lean_object* v_tail_2496_; uint8_t v___x_2497_; 
v_head_2495_ = lean_ctor_get(v_x_2493_, 0);
v_tail_2496_ = lean_ctor_get(v_x_2493_, 1);
v___x_2497_ = l_Lean_instBEqMVarId_beq(v_head_2495_, v___x_2492_);
if (v___x_2497_ == 0)
{
v_x_2493_ = v_tail_2496_;
goto _start;
}
else
{
return v___x_2497_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4___boxed(lean_object* v___x_2499_, lean_object* v_x_2500_){
_start:
{
uint8_t v_res_2501_; lean_object* v_r_2502_; 
v_res_2501_ = l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4(v___x_2499_, v_x_2500_);
lean_dec(v_x_2500_);
lean_dec(v___x_2499_);
v_r_2502_ = lean_box(v_res_2501_);
return v_r_2502_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(lean_object* v_t_2503_, lean_object* v_k_2504_){
_start:
{
if (lean_obj_tag(v_t_2503_) == 0)
{
lean_object* v_k_2505_; lean_object* v_v_2506_; lean_object* v_l_2507_; lean_object* v_r_2508_; uint8_t v___x_2509_; 
v_k_2505_ = lean_ctor_get(v_t_2503_, 1);
v_v_2506_ = lean_ctor_get(v_t_2503_, 2);
v_l_2507_ = lean_ctor_get(v_t_2503_, 3);
v_r_2508_ = lean_ctor_get(v_t_2503_, 4);
v___x_2509_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2504_, v_k_2505_);
switch(v___x_2509_)
{
case 0:
{
v_t_2503_ = v_l_2507_;
goto _start;
}
case 1:
{
lean_object* v___x_2511_; 
lean_inc(v_v_2506_);
v___x_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2511_, 0, v_v_2506_);
return v___x_2511_;
}
default: 
{
v_t_2503_ = v_r_2508_;
goto _start;
}
}
}
else
{
lean_object* v___x_2513_; 
v___x_2513_ = lean_box(0);
return v___x_2513_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg___boxed(lean_object* v_t_2514_, lean_object* v_k_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(v_t_2514_, v_k_2515_);
lean_dec(v_k_2515_);
lean_dec(v_t_2514_);
return v_res_2516_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(lean_object* v_k_2517_, lean_object* v_t_2518_){
_start:
{
if (lean_obj_tag(v_t_2518_) == 0)
{
lean_object* v_k_2519_; lean_object* v_l_2520_; lean_object* v_r_2521_; uint8_t v___x_2522_; 
v_k_2519_ = lean_ctor_get(v_t_2518_, 1);
v_l_2520_ = lean_ctor_get(v_t_2518_, 3);
v_r_2521_ = lean_ctor_get(v_t_2518_, 4);
v___x_2522_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2517_, v_k_2519_);
switch(v___x_2522_)
{
case 0:
{
v_t_2518_ = v_l_2520_;
goto _start;
}
case 1:
{
uint8_t v___x_2524_; 
v___x_2524_ = 1;
return v___x_2524_;
}
default: 
{
v_t_2518_ = v_r_2521_;
goto _start;
}
}
}
else
{
uint8_t v___x_2526_; 
v___x_2526_ = 0;
return v___x_2526_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg___boxed(lean_object* v_k_2527_, lean_object* v_t_2528_){
_start:
{
uint8_t v_res_2529_; lean_object* v_r_2530_; 
v_res_2529_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_k_2527_, v_t_2528_);
lean_dec(v_t_2528_);
lean_dec(v_k_2527_);
v_r_2530_ = lean_box(v_res_2529_);
return v_r_2530_;
}
}
LEAN_EXPORT uint8_t l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(lean_object* v_a_2531_, uint8_t v___x_2532_, lean_object* v_before_2533_, lean_object* v_after_2534_){
_start:
{
lean_object* v___x_2535_; 
v___x_2535_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(v_a_2531_, v_before_2533_);
if (lean_obj_tag(v___x_2535_) == 0)
{
return v___x_2532_;
}
else
{
lean_object* v_val_2536_; uint8_t v___x_2537_; 
v_val_2536_ = lean_ctor_get(v___x_2535_, 0);
lean_inc(v_val_2536_);
lean_dec_ref_known(v___x_2535_, 1);
v___x_2537_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_after_2534_, v_val_2536_);
lean_dec(v_val_2536_);
return v___x_2537_;
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0___boxed(lean_object* v_a_2538_, lean_object* v___x_2539_, lean_object* v_before_2540_, lean_object* v_after_2541_){
_start:
{
uint8_t v___x_3274__boxed_2542_; uint8_t v_res_2543_; lean_object* v_r_2544_; 
v___x_3274__boxed_2542_ = lean_unbox(v___x_2539_);
v_res_2543_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(v_a_2538_, v___x_3274__boxed_2542_, v_before_2540_, v_after_2541_);
lean_dec(v_after_2541_);
lean_dec(v_before_2540_);
lean_dec(v_a_2538_);
v_r_2544_ = lean_box(v_res_2543_);
return v_r_2544_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5(uint8_t v_useAfter_2545_, lean_object* v_a_2546_, lean_object* v___x_2547_, lean_object* v_x_2548_){
_start:
{
if (lean_obj_tag(v_x_2548_) == 0)
{
lean_object* v___x_2549_; 
v___x_2549_ = lean_box(0);
return v___x_2549_;
}
else
{
lean_object* v_head_2550_; lean_object* v_tail_2551_; uint8_t v___y_2553_; uint8_t v___x_2556_; 
v_head_2550_ = lean_ctor_get(v_x_2548_, 0);
v_tail_2551_ = lean_ctor_get(v_x_2548_, 1);
v___x_2556_ = 0;
if (v_useAfter_2545_ == 0)
{
uint8_t v___x_2557_; 
v___x_2557_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(v_a_2546_, v___x_2556_, v___x_2547_, v_head_2550_);
v___y_2553_ = v___x_2557_;
goto v___jp_2552_;
}
else
{
uint8_t v___x_2558_; 
v___x_2558_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(v_a_2546_, v___x_2556_, v_head_2550_, v___x_2547_);
v___y_2553_ = v___x_2558_;
goto v___jp_2552_;
}
v___jp_2552_:
{
if (v___y_2553_ == 0)
{
v_x_2548_ = v_tail_2551_;
goto _start;
}
else
{
lean_object* v___x_2555_; 
lean_inc(v_head_2550_);
v___x_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2555_, 0, v_head_2550_);
return v___x_2555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___boxed(lean_object* v_useAfter_2559_, lean_object* v_a_2560_, lean_object* v___x_2561_, lean_object* v_x_2562_){
_start:
{
uint8_t v_useAfter_boxed_2563_; lean_object* v_res_2564_; 
v_useAfter_boxed_2563_ = lean_unbox(v_useAfter_2559_);
v_res_2564_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5(v_useAfter_boxed_2563_, v_a_2560_, v___x_2561_, v_x_2562_);
lean_dec(v_x_2562_);
lean_dec(v___x_2561_);
lean_dec(v_a_2560_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0(lean_object* v_mvarId_2565_, lean_object* v___y_2566_, uint8_t v_useAfter_2567_, lean_object* v_a_2568_, lean_object* v_v_2569_, uint8_t v___x_2570_, lean_object* v_toInteractiveGoalCore_2571_, lean_object* v_userName_x3f_2572_, lean_object* v_goalPrefix_2573_, lean_object* v_isInserted_x3f_2574_, lean_object* v_isRemoved_x3f_2575_, lean_object* v___lctx_u2081_2576_, lean_object* v___md_u2081_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
uint8_t v___x_2583_; 
v___x_2583_ = l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4(v_mvarId_2565_, v___y_2566_);
if (v___x_2583_ == 0)
{
lean_object* v___x_2584_; 
v___x_2584_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5(v_useAfter_2567_, v_a_2568_, v_mvarId_2565_, v___y_2566_);
if (lean_obj_tag(v___x_2584_) == 1)
{
lean_object* v_val_2585_; lean_object* v___x_2586_; 
lean_dec(v_isRemoved_x3f_2575_);
lean_dec(v_isInserted_x3f_2574_);
lean_dec_ref(v_goalPrefix_2573_);
lean_dec(v_userName_x3f_2572_);
lean_dec_ref(v_toInteractiveGoalCore_2571_);
lean_dec(v_mvarId_2565_);
v_val_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_val_2585_);
lean_dec_ref_known(v___x_2584_, 1);
v___x_2586_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(v_useAfter_2567_, v_val_2585_, v_v_2569_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
return v___x_2586_;
}
else
{
lean_dec(v___x_2584_);
lean_dec(v_v_2569_);
if (v_useAfter_2567_ == 0)
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
lean_dec(v_isRemoved_x3f_2575_);
v___x_2587_ = lean_box(v___x_2570_);
v___x_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
v___x_2589_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2589_, 0, v_toInteractiveGoalCore_2571_);
lean_ctor_set(v___x_2589_, 1, v_userName_x3f_2572_);
lean_ctor_set(v___x_2589_, 2, v_goalPrefix_2573_);
lean_ctor_set(v___x_2589_, 3, v_mvarId_2565_);
lean_ctor_set(v___x_2589_, 4, v_isInserted_x3f_2574_);
lean_ctor_set(v___x_2589_, 5, v___x_2588_);
v___x_2590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
return v___x_2590_;
}
else
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
lean_dec(v_isInserted_x3f_2574_);
v___x_2591_ = lean_box(v___x_2570_);
v___x_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
v___x_2593_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2593_, 0, v_toInteractiveGoalCore_2571_);
lean_ctor_set(v___x_2593_, 1, v_userName_x3f_2572_);
lean_ctor_set(v___x_2593_, 2, v_goalPrefix_2573_);
lean_ctor_set(v___x_2593_, 3, v_mvarId_2565_);
lean_ctor_set(v___x_2593_, 4, v___x_2592_);
lean_ctor_set(v___x_2593_, 5, v_isRemoved_x3f_2575_);
v___x_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
return v___x_2594_;
}
}
}
else
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
lean_dec(v_isInserted_x3f_2574_);
lean_dec(v_v_2569_);
v___x_2595_ = lean_box(0);
v___x_2596_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2596_, 0, v_toInteractiveGoalCore_2571_);
lean_ctor_set(v___x_2596_, 1, v_userName_x3f_2572_);
lean_ctor_set(v___x_2596_, 2, v_goalPrefix_2573_);
lean_ctor_set(v___x_2596_, 3, v_mvarId_2565_);
lean_ctor_set(v___x_2596_, 4, v___x_2595_);
lean_ctor_set(v___x_2596_, 5, v_isRemoved_x3f_2575_);
v___x_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2596_);
return v___x_2597_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0___boxed(lean_object** _args){
lean_object* v_mvarId_2598_ = _args[0];
lean_object* v___y_2599_ = _args[1];
lean_object* v_useAfter_2600_ = _args[2];
lean_object* v_a_2601_ = _args[3];
lean_object* v_v_2602_ = _args[4];
lean_object* v___x_2603_ = _args[5];
lean_object* v_toInteractiveGoalCore_2604_ = _args[6];
lean_object* v_userName_x3f_2605_ = _args[7];
lean_object* v_goalPrefix_2606_ = _args[8];
lean_object* v_isInserted_x3f_2607_ = _args[9];
lean_object* v_isRemoved_x3f_2608_ = _args[10];
lean_object* v___lctx_u2081_2609_ = _args[11];
lean_object* v___md_u2081_2610_ = _args[12];
lean_object* v___y_2611_ = _args[13];
lean_object* v___y_2612_ = _args[14];
lean_object* v___y_2613_ = _args[15];
lean_object* v___y_2614_ = _args[16];
lean_object* v___y_2615_ = _args[17];
_start:
{
uint8_t v_useAfter_boxed_2616_; uint8_t v___x_3316__boxed_2617_; lean_object* v_res_2618_; 
v_useAfter_boxed_2616_ = lean_unbox(v_useAfter_2600_);
v___x_3316__boxed_2617_ = lean_unbox(v___x_2603_);
v_res_2618_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0(v_mvarId_2598_, v___y_2599_, v_useAfter_boxed_2616_, v_a_2601_, v_v_2602_, v___x_3316__boxed_2617_, v_toInteractiveGoalCore_2604_, v_userName_x3f_2605_, v_goalPrefix_2606_, v_isInserted_x3f_2607_, v_isRemoved_x3f_2608_, v___lctx_u2081_2609_, v___md_u2081_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec_ref(v___md_u2081_2610_);
lean_dec_ref(v___lctx_u2081_2609_);
lean_dec(v_a_2601_);
lean_dec(v___y_2599_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8(lean_object* v___y_2619_, uint8_t v_useAfter_2620_, lean_object* v_a_2621_, uint8_t v___x_2622_, size_t v_sz_2623_, size_t v_i_2624_, lean_object* v_bs_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
uint8_t v___x_2631_; 
v___x_2631_ = lean_usize_dec_lt(v_i_2624_, v_sz_2623_);
if (v___x_2631_ == 0)
{
lean_object* v___x_2632_; 
lean_dec(v_a_2621_);
lean_dec(v___y_2619_);
v___x_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2632_, 0, v_bs_2625_);
return v___x_2632_;
}
else
{
lean_object* v_v_2633_; lean_object* v_toInteractiveGoalCore_2634_; lean_object* v_userName_x3f_2635_; lean_object* v_goalPrefix_2636_; lean_object* v_mvarId_2637_; lean_object* v_isInserted_x3f_2638_; lean_object* v_isRemoved_x3f_2639_; lean_object* v___x_2640_; lean_object* v_bs_x27_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___f_2644_; lean_object* v___x_2645_; 
v_v_2633_ = lean_array_uget(v_bs_2625_, v_i_2624_);
v_toInteractiveGoalCore_2634_ = lean_ctor_get(v_v_2633_, 0);
lean_inc_ref(v_toInteractiveGoalCore_2634_);
v_userName_x3f_2635_ = lean_ctor_get(v_v_2633_, 1);
lean_inc(v_userName_x3f_2635_);
v_goalPrefix_2636_ = lean_ctor_get(v_v_2633_, 2);
lean_inc_ref(v_goalPrefix_2636_);
v_mvarId_2637_ = lean_ctor_get(v_v_2633_, 3);
lean_inc_n(v_mvarId_2637_, 2);
v_isInserted_x3f_2638_ = lean_ctor_get(v_v_2633_, 4);
lean_inc(v_isInserted_x3f_2638_);
v_isRemoved_x3f_2639_ = lean_ctor_get(v_v_2633_, 5);
lean_inc(v_isRemoved_x3f_2639_);
v___x_2640_ = lean_unsigned_to_nat(0u);
v_bs_x27_2641_ = lean_array_uset(v_bs_2625_, v_i_2624_, v___x_2640_);
v___x_2642_ = lean_box(v_useAfter_2620_);
v___x_2643_ = lean_box(v___x_2622_);
lean_inc(v_a_2621_);
lean_inc(v___y_2619_);
v___f_2644_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0___boxed), 18, 11);
lean_closure_set(v___f_2644_, 0, v_mvarId_2637_);
lean_closure_set(v___f_2644_, 1, v___y_2619_);
lean_closure_set(v___f_2644_, 2, v___x_2642_);
lean_closure_set(v___f_2644_, 3, v_a_2621_);
lean_closure_set(v___f_2644_, 4, v_v_2633_);
lean_closure_set(v___f_2644_, 5, v___x_2643_);
lean_closure_set(v___f_2644_, 6, v_toInteractiveGoalCore_2634_);
lean_closure_set(v___f_2644_, 7, v_userName_x3f_2635_);
lean_closure_set(v___f_2644_, 8, v_goalPrefix_2636_);
lean_closure_set(v___f_2644_, 9, v_isInserted_x3f_2638_);
lean_closure_set(v___f_2644_, 10, v_isRemoved_x3f_2639_);
v___x_2645_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(v_mvarId_2637_, v___f_2644_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; size_t v___x_2647_; size_t v___x_2648_; lean_object* v___x_2649_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_a_2646_);
lean_dec_ref_known(v___x_2645_, 1);
v___x_2647_ = ((size_t)1ULL);
v___x_2648_ = lean_usize_add(v_i_2624_, v___x_2647_);
v___x_2649_ = lean_array_uset(v_bs_x27_2641_, v_i_2624_, v_a_2646_);
v_i_2624_ = v___x_2648_;
v_bs_2625_ = v___x_2649_;
goto _start;
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
lean_dec_ref(v_bs_x27_2641_);
lean_dec(v_a_2621_);
lean_dec(v___y_2619_);
v_a_2651_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___x_2645_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2645_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8___boxed(lean_object* v___y_2659_, lean_object* v_useAfter_2660_, lean_object* v_a_2661_, lean_object* v___x_2662_, lean_object* v_sz_2663_, lean_object* v_i_2664_, lean_object* v_bs_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
uint8_t v_useAfter_boxed_2671_; uint8_t v___x_3370__boxed_2672_; size_t v_sz_boxed_2673_; size_t v_i_boxed_2674_; lean_object* v_res_2675_; 
v_useAfter_boxed_2671_ = lean_unbox(v_useAfter_2660_);
v___x_3370__boxed_2672_ = lean_unbox(v___x_2662_);
v_sz_boxed_2673_ = lean_unbox_usize(v_sz_2663_);
lean_dec(v_sz_2663_);
v_i_boxed_2674_ = lean_unbox_usize(v_i_2664_);
lean_dec(v_i_2664_);
v_res_2675_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8(v___y_2659_, v_useAfter_boxed_2671_, v_a_2661_, v___x_3370__boxed_2672_, v_sz_boxed_2673_, v_i_boxed_2674_, v_bs_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7(uint8_t v_useAfter_2676_, lean_object* v_a_2677_, lean_object* v___y_2678_, uint8_t v___x_2679_, size_t v_sz_2680_, size_t v_i_2681_, lean_object* v_bs_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
uint8_t v___x_2688_; 
v___x_2688_ = lean_usize_dec_lt(v_i_2681_, v_sz_2680_);
if (v___x_2688_ == 0)
{
lean_object* v___x_2689_; 
lean_dec(v___y_2678_);
lean_dec(v_a_2677_);
v___x_2689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2689_, 0, v_bs_2682_);
return v___x_2689_;
}
else
{
lean_object* v_v_2690_; lean_object* v_toInteractiveGoalCore_2691_; lean_object* v_userName_x3f_2692_; lean_object* v_goalPrefix_2693_; lean_object* v_mvarId_2694_; lean_object* v_isInserted_x3f_2695_; lean_object* v_isRemoved_x3f_2696_; lean_object* v___x_2697_; lean_object* v_bs_x27_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___f_2701_; lean_object* v___x_2702_; 
v_v_2690_ = lean_array_uget(v_bs_2682_, v_i_2681_);
v_toInteractiveGoalCore_2691_ = lean_ctor_get(v_v_2690_, 0);
lean_inc_ref(v_toInteractiveGoalCore_2691_);
v_userName_x3f_2692_ = lean_ctor_get(v_v_2690_, 1);
lean_inc(v_userName_x3f_2692_);
v_goalPrefix_2693_ = lean_ctor_get(v_v_2690_, 2);
lean_inc_ref(v_goalPrefix_2693_);
v_mvarId_2694_ = lean_ctor_get(v_v_2690_, 3);
lean_inc_n(v_mvarId_2694_, 2);
v_isInserted_x3f_2695_ = lean_ctor_get(v_v_2690_, 4);
lean_inc(v_isInserted_x3f_2695_);
v_isRemoved_x3f_2696_ = lean_ctor_get(v_v_2690_, 5);
lean_inc(v_isRemoved_x3f_2696_);
v___x_2697_ = lean_unsigned_to_nat(0u);
v_bs_x27_2698_ = lean_array_uset(v_bs_2682_, v_i_2681_, v___x_2697_);
v___x_2699_ = lean_box(v_useAfter_2676_);
v___x_2700_ = lean_box(v___x_2679_);
lean_inc(v_a_2677_);
lean_inc(v___y_2678_);
v___f_2701_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0___boxed), 18, 11);
lean_closure_set(v___f_2701_, 0, v_mvarId_2694_);
lean_closure_set(v___f_2701_, 1, v___y_2678_);
lean_closure_set(v___f_2701_, 2, v___x_2699_);
lean_closure_set(v___f_2701_, 3, v_a_2677_);
lean_closure_set(v___f_2701_, 4, v_v_2690_);
lean_closure_set(v___f_2701_, 5, v___x_2700_);
lean_closure_set(v___f_2701_, 6, v_toInteractiveGoalCore_2691_);
lean_closure_set(v___f_2701_, 7, v_userName_x3f_2692_);
lean_closure_set(v___f_2701_, 8, v_goalPrefix_2693_);
lean_closure_set(v___f_2701_, 9, v_isInserted_x3f_2695_);
lean_closure_set(v___f_2701_, 10, v_isRemoved_x3f_2696_);
v___x_2702_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(v_mvarId_2694_, v___f_2701_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v_a_2703_; size_t v___x_2704_; size_t v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
lean_inc(v_a_2703_);
lean_dec_ref_known(v___x_2702_, 1);
v___x_2704_ = ((size_t)1ULL);
v___x_2705_ = lean_usize_add(v_i_2681_, v___x_2704_);
v___x_2706_ = lean_array_uset(v_bs_x27_2698_, v_i_2681_, v_a_2703_);
v___x_2707_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8(v___y_2678_, v_useAfter_2676_, v_a_2677_, v___x_2679_, v_sz_2680_, v___x_2705_, v___x_2706_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
return v___x_2707_;
}
else
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2715_; 
lean_dec_ref(v_bs_x27_2698_);
lean_dec(v___y_2678_);
lean_dec(v_a_2677_);
v_a_2708_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2710_ = v___x_2702_;
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2702_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2713_; 
if (v_isShared_2711_ == 0)
{
v___x_2713_ = v___x_2710_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___boxed(lean_object* v_useAfter_2716_, lean_object* v_a_2717_, lean_object* v___y_2718_, lean_object* v___x_2719_, lean_object* v_sz_2720_, lean_object* v_i_2721_, lean_object* v_bs_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
uint8_t v_useAfter_boxed_2728_; uint8_t v___x_3434__boxed_2729_; size_t v_sz_boxed_2730_; size_t v_i_boxed_2731_; lean_object* v_res_2732_; 
v_useAfter_boxed_2728_ = lean_unbox(v_useAfter_2716_);
v___x_3434__boxed_2729_ = lean_unbox(v___x_2719_);
v_sz_boxed_2730_ = lean_unbox_usize(v_sz_2720_);
lean_dec(v_sz_2720_);
v_i_boxed_2731_ = lean_unbox_usize(v_i_2721_);
lean_dec(v_i_2721_);
v_res_2732_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7(v_useAfter_boxed_2728_, v_a_2717_, v___y_2718_, v___x_3434__boxed_2729_, v_sz_boxed_2730_, v_i_boxed_2731_, v_bs_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_diffInteractiveGoals(uint8_t v_useAfter_2733_, lean_object* v_info_2734_, lean_object* v_igs_u2081_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_){
_start:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; uint8_t v___x_2743_; lean_object* v___y_2745_; 
v___x_2741_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2738_);
v___x_2742_ = l___private_Lean_Widget_Diff_0__Lean_Widget_showTacticDiff;
v___x_2743_ = l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(v___x_2741_, v___x_2742_);
lean_dec_ref(v___x_2741_);
if (v___x_2743_ == 0)
{
lean_object* v___x_2777_; 
lean_dec_ref(v_info_2734_);
v___x_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2777_, 0, v_igs_u2081_2735_);
return v___x_2777_;
}
else
{
if (v_useAfter_2733_ == 0)
{
lean_object* v_goalsAfter_2778_; 
v_goalsAfter_2778_ = lean_ctor_get(v_info_2734_, 4);
lean_inc(v_goalsAfter_2778_);
v___y_2745_ = v_goalsAfter_2778_;
goto v___jp_2744_;
}
else
{
lean_object* v_goalsBefore_2779_; 
v_goalsBefore_2779_ = lean_ctor_get(v_info_2734_, 2);
lean_inc(v_goalsBefore_2779_);
v___y_2745_ = v_goalsBefore_2779_;
goto v___jp_2744_;
}
}
v___jp_2744_:
{
lean_object* v_goalsBefore_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v_goalsBefore_2746_ = lean_ctor_get(v_info_2734_, 2);
lean_inc(v_goalsBefore_2746_);
lean_dec_ref(v_info_2734_);
v___x_2747_ = lean_box(1);
v___x_2748_ = l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(v___x_2747_, v_goalsBefore_2746_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v_a_2749_; size_t v_sz_2750_; size_t v___x_2751_; lean_object* v___x_2752_; 
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_a_2749_);
lean_dec_ref_known(v___x_2748_, 1);
v_sz_2750_ = lean_array_size(v_igs_u2081_2735_);
v___x_2751_ = ((size_t)0ULL);
v___x_2752_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7(v_useAfter_2733_, v_a_2749_, v___y_2745_, v___x_2743_, v_sz_2750_, v___x_2751_, v_igs_u2081_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2755_ = v___x_2752_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2752_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2758_; 
if (v_isShared_2756_ == 0)
{
v___x_2758_ = v___x_2755_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_a_2753_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
v_a_2761_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2752_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2752_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2761_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
else
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
lean_dec(v___y_2745_);
lean_dec_ref(v_igs_u2081_2735_);
v_a_2769_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2748_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2748_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2772_ == 0)
{
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2769_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_diffInteractiveGoals___boxed(lean_object* v_useAfter_2780_, lean_object* v_info_2781_, lean_object* v_igs_u2081_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_){
_start:
{
uint8_t v_useAfter_boxed_2788_; lean_object* v_res_2789_; 
v_useAfter_boxed_2788_ = lean_unbox(v_useAfter_2780_);
v_res_2789_ = l_Lean_Widget_diffInteractiveGoals(v_useAfter_boxed_2788_, v_info_2781_, v_igs_u2081_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_);
lean_dec(v_a_2786_);
lean_dec_ref(v_a_2785_);
lean_dec(v_a_2784_);
lean_dec_ref(v_a_2783_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2(lean_object* v_00_u03b4_2790_, lean_object* v_t_2791_, lean_object* v_k_2792_){
_start:
{
lean_object* v___x_2793_; 
v___x_2793_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(v_t_2791_, v_k_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___boxed(lean_object* v_00_u03b4_2794_, lean_object* v_t_2795_, lean_object* v_k_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2(v_00_u03b4_2794_, v_t_2795_, v_k_2796_);
lean_dec(v_k_2796_);
lean_dec(v_t_2795_);
return v_res_2797_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3(lean_object* v_00_u03b2_2798_, lean_object* v_k_2799_, lean_object* v_t_2800_){
_start:
{
uint8_t v___x_2801_; 
v___x_2801_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_k_2799_, v_t_2800_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___boxed(lean_object* v_00_u03b2_2802_, lean_object* v_k_2803_, lean_object* v_t_2804_){
_start:
{
uint8_t v_res_2805_; lean_object* v_r_2806_; 
v_res_2805_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3(v_00_u03b2_2802_, v_k_2803_, v_t_2804_);
lean_dec(v_t_2804_);
lean_dec(v_k_2803_);
v_r_2806_ = lean_box(v_res_2805_);
return v_r_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6(lean_object* v_00_u03b1_2807_, lean_object* v_lctx_2808_, lean_object* v_localInsts_2809_, lean_object* v_x_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_){
_start:
{
lean_object* v___x_2816_; 
v___x_2816_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(v_lctx_2808_, v_localInsts_2809_, v_x_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___boxed(lean_object* v_00_u03b1_2817_, lean_object* v_lctx_2818_, lean_object* v_localInsts_2819_, lean_object* v_x_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
lean_object* v_res_2826_; 
v_res_2826_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6(v_00_u03b1_2817_, v_lctx_2818_, v_localInsts_2819_, v_x_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6(lean_object* v_00_u03b1_2827_, lean_object* v_goal_2828_, lean_object* v_action_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v___x_2835_; 
v___x_2835_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(v_goal_2828_, v_action_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___boxed(lean_object* v_00_u03b1_2836_, lean_object* v_goal_2837_, lean_object* v_action_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6(v_00_u03b1_2836_, v_goal_2837_, v_action_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
return v_res_2844_;
}
}
lean_object* runtime_initialize_Lean_Widget_InteractiveGoal(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Widget_Diff(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Widget_InteractiveGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_();
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
