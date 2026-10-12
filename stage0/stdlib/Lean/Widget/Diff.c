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
lean_object* l_Lean_Option_register___at___00__private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_decl_2_ = stack[1].m_obj;
lean_object* v_ref_3_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_Lean_Option_register___at___00__private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__spec__0(v_name_1_, v_decl_2_, v_ref_3_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_30_, lean_object* v_decl_31_, lean_object* v_ref_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Option_register___at___00__private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__spec__0(v_name_30_, v_decl_31_, v_ref_32_);
lean_dec_ref(v_decl_31_);
return v_res_34_;
}
}
lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_73_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_));
v___x_74_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_));
v___x_75_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__15_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_));
v___x_76_ = l_Lean_Option_register___at___00__private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__spec__0(v___x_73_, v___x_74_, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT void l___private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_77_;
v_res_77_ = l___private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_();
stack->m_obj
 = v_res_77_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4____boxed(lean_object* v_a_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l___private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_();
return v_res_79_;
}
}
lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx___impl(uint8_t v_x_80_){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lean_box(v_x_80_);
v___x_82_ = lean_obj_tag_nat(v___x_81_);
lean_dec(v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT void l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_80_ = stack[0].m_num;
lean_object* v_res_83_;
v_res_83_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx___impl(v_x_80_);
stack->m_obj
 = v_res_83_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx___impl___boxed(lean_object* v_x_84_){
_start:
{
uint8_t v_x_4__boxed_85_; lean_object* v_res_86_; 
v_x_4__boxed_85_ = lean_unbox(v_x_84_);
v_res_86_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx___impl(v_x_4__boxed_85_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___redArg(lean_object* v_k_87_){
_start:
{
lean_inc(v_k_87_);
return v_k_87_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___redArg___boxed(lean_object* v_k_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___redArg(v_k_88_);
lean_dec(v_k_88_);
return v_res_89_;
}
}
lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim(lean_object* v_motive_90_, lean_object* v_ctorIdx_91_, uint8_t v_t_92_, lean_object* v_h_93_, lean_object* v_k_94_){
_start:
{
lean_inc(v_k_94_);
return v_k_94_;
}
}
LEAN_EXPORT void l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_91_ = stack[1].m_obj;
uint8_t v_t_92_ = stack[2].m_num;
lean_object* v_k_94_ = stack[4].m_obj;
lean_object* v_res_95_;
v_res_95_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim(lean_box(0), v_ctorIdx_91_, v_t_92_, lean_box(0), v_k_94_);
stack->m_obj
 = v_res_95_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___boxed(lean_object* v_motive_96_, lean_object* v_ctorIdx_97_, lean_object* v_t_98_, lean_object* v_h_99_, lean_object* v_k_100_){
_start:
{
uint8_t v_t_boxed_101_; lean_object* v_res_102_; 
v_t_boxed_101_ = lean_unbox(v_t_98_);
v_res_102_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim(v_motive_96_, v_ctorIdx_97_, v_t_boxed_101_, v_h_99_, v_k_100_);
lean_dec(v_k_100_);
lean_dec(v_ctorIdx_97_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___redArg(lean_object* v_change_103_){
_start:
{
lean_inc(v_change_103_);
return v_change_103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___redArg___boxed(lean_object* v_change_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___redArg(v_change_104_);
lean_dec(v_change_104_);
return v_res_105_;
}
}
lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim(lean_object* v_motive_106_, uint8_t v_t_107_, lean_object* v_h_108_, lean_object* v_change_109_){
_start:
{
lean_inc(v_change_109_);
return v_change_109_;
}
}
LEAN_EXPORT void l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_107_ = stack[1].m_num;
lean_object* v_change_109_ = stack[3].m_obj;
lean_object* v_res_110_;
v_res_110_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim(lean_box(0), v_t_107_, lean_box(0), v_change_109_);
stack->m_obj
 = v_res_110_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___boxed(lean_object* v_motive_111_, lean_object* v_t_112_, lean_object* v_h_113_, lean_object* v_change_114_){
_start:
{
uint8_t v_t_boxed_115_; lean_object* v_res_116_; 
v_t_boxed_115_ = lean_unbox(v_t_112_);
v_res_116_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim(v_motive_111_, v_t_boxed_115_, v_h_113_, v_change_114_);
lean_dec(v_change_114_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___redArg(lean_object* v_delete_117_){
_start:
{
lean_inc(v_delete_117_);
return v_delete_117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___redArg___boxed(lean_object* v_delete_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___redArg(v_delete_118_);
lean_dec(v_delete_118_);
return v_res_119_;
}
}
lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim(lean_object* v_motive_120_, uint8_t v_t_121_, lean_object* v_h_122_, lean_object* v_delete_123_){
_start:
{
lean_inc(v_delete_123_);
return v_delete_123_;
}
}
LEAN_EXPORT void l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_121_ = stack[1].m_num;
lean_object* v_delete_123_ = stack[3].m_obj;
lean_object* v_res_124_;
v_res_124_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim(lean_box(0), v_t_121_, lean_box(0), v_delete_123_);
stack->m_obj
 = v_res_124_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___boxed(lean_object* v_motive_125_, lean_object* v_t_126_, lean_object* v_h_127_, lean_object* v_delete_128_){
_start:
{
uint8_t v_t_boxed_129_; lean_object* v_res_130_; 
v_t_boxed_129_ = lean_unbox(v_t_126_);
v_res_130_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim(v_motive_125_, v_t_boxed_129_, v_h_127_, v_delete_128_);
lean_dec(v_delete_128_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___redArg(lean_object* v_insert_131_){
_start:
{
lean_inc(v_insert_131_);
return v_insert_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___redArg___boxed(lean_object* v_insert_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___redArg(v_insert_132_);
lean_dec(v_insert_132_);
return v_res_133_;
}
}
lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim(lean_object* v_motive_134_, uint8_t v_t_135_, lean_object* v_h_136_, lean_object* v_insert_137_){
_start:
{
lean_inc(v_insert_137_);
return v_insert_137_;
}
}
LEAN_EXPORT void l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_135_ = stack[1].m_num;
lean_object* v_insert_137_ = stack[3].m_obj;
lean_object* v_res_138_;
v_res_138_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim(lean_box(0), v_t_135_, lean_box(0), v_insert_137_);
stack->m_obj
 = v_res_138_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___boxed(lean_object* v_motive_139_, lean_object* v_t_140_, lean_object* v_h_141_, lean_object* v_insert_142_){
_start:
{
uint8_t v_t_boxed_143_; lean_object* v_res_144_; 
v_t_boxed_143_ = lean_unbox(v_t_140_);
v_res_144_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim(v_motive_139_, v_t_boxed_143_, v_h_141_, v_insert_142_);
lean_dec(v_insert_142_);
return v_res_144_;
}
}
uint8_t l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag(uint8_t v_x_145_, uint8_t v_x_146_){
_start:
{
if (v_x_145_ == 0)
{
switch(v_x_146_)
{
case 0:
{
uint8_t v___x_147_; 
v___x_147_ = 1;
return v___x_147_;
}
case 1:
{
uint8_t v___x_148_; 
v___x_148_ = 3;
return v___x_148_;
}
default: 
{
uint8_t v___x_149_; 
v___x_149_ = 5;
return v___x_149_;
}
}
}
else
{
switch(v_x_146_)
{
case 0:
{
uint8_t v___x_150_; 
v___x_150_ = 0;
return v___x_150_;
}
case 1:
{
uint8_t v___x_151_; 
v___x_151_ = 2;
return v___x_151_;
}
default: 
{
uint8_t v___x_152_; 
v___x_152_ = 4;
return v___x_152_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_145_ = stack[0].m_num;
uint8_t v_x_146_ = stack[1].m_num;
uint8_t v_res_153_;
v_res_153_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag(v_x_145_, v_x_146_);
stack->m_num = v_res_153_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag___boxed(lean_object* v_x_154_, lean_object* v_x_155_){
_start:
{
uint8_t v_x_49__boxed_156_; uint8_t v_x_50__boxed_157_; uint8_t v_res_158_; lean_object* v_r_159_; 
v_x_49__boxed_156_ = lean_unbox(v_x_154_);
v_x_50__boxed_157_ = lean_unbox(v_x_155_);
v_res_158_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag(v_x_49__boxed_156_, v_x_50__boxed_157_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString(uint8_t v_x_163_){
_start:
{
switch(v_x_163_)
{
case 0:
{
lean_object* v___x_164_; 
v___x_164_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__0));
return v___x_164_;
}
case 1:
{
lean_object* v___x_165_; 
v___x_165_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__1));
return v___x_165_;
}
default: 
{
lean_object* v___x_166_; 
v___x_166_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__2));
return v___x_166_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_163_ = stack[0].m_num;
lean_object* v_res_167_;
v_res_167_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString(v_x_163_);
stack->m_obj
 = v_res_167_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___boxed(lean_object* v_x_168_){
_start:
{
uint8_t v_x_31__boxed_169_; lean_object* v_res_170_; 
v_x_31__boxed_169_ = lean_unbox(v_x_168_);
v_res_170_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString(v_x_31__boxed_169_);
return v_res_170_;
}
}
uint8_t l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0(lean_object* v_x_176_, lean_object* v_y_177_){
_start:
{
uint8_t v___x_178_; 
v___x_178_ = lean_nat_dec_lt(v_x_176_, v_y_177_);
if (v___x_178_ == 0)
{
uint8_t v___x_179_; 
v___x_179_ = lean_nat_dec_eq(v_x_176_, v_y_177_);
if (v___x_179_ == 0)
{
uint8_t v___x_180_; 
v___x_180_ = 2;
return v___x_180_;
}
else
{
uint8_t v___x_181_; 
v___x_181_ = 1;
return v___x_181_;
}
}
else
{
uint8_t v___x_182_; 
v___x_182_ = 0;
return v___x_182_;
}
}
}
LEAN_EXPORT void l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_176_ = stack[0].m_obj;
lean_object* v_y_177_ = stack[1].m_obj;
uint8_t v_res_183_;
v_res_183_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0(v_x_176_, v_y_177_);
stack->m_num = v_res_183_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0___boxed(lean_object* v_x_184_, lean_object* v_y_185_){
_start:
{
uint8_t v_res_186_; lean_object* v_r_187_; 
v_res_186_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0(v_x_184_, v_y_185_);
lean_dec(v_y_185_);
lean_dec(v_x_184_);
v_r_187_ = lean_box(v_res_186_);
return v_r_187_;
}
}
lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1(uint8_t v_b_u2082_188_, lean_object* v_x_189_){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_box(v_b_u2082_188_);
v___x_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT void l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_u2082_188_ = stack[0].m_num;
lean_object* v_x_189_ = stack[1].m_obj;
lean_object* v_res_192_;
v_res_192_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1(v_b_u2082_188_, v_x_189_);
stack->m_obj
 = v_res_192_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1___boxed(lean_object* v_b_u2082_193_, lean_object* v_x_194_){
_start:
{
uint8_t v_b_u2082_boxed_195_; lean_object* v_res_196_; 
v_b_u2082_boxed_195_ = lean_unbox(v_b_u2082_193_);
v_res_196_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1(v_b_u2082_boxed_195_, v_x_194_);
lean_dec(v_x_194_);
return v_res_196_;
}
}
lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2(lean_object* v___f_197_, lean_object* v_t_198_, lean_object* v_a_199_, uint8_t v_b_u2082_200_){
_start:
{
lean_object* v___x_201_; lean_object* v___f_202_; lean_object* v___x_203_; 
v___x_201_ = lean_box(v_b_u2082_200_);
v___f_202_ = lean_alloc_closure((void*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1___boxed), 2, 1);
lean_closure_set(v___f_202_, 0, v___x_201_);
v___x_203_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v___f_197_, v_a_199_, v___f_202_, v_t_198_);
return v___x_203_;
}
}
LEAN_EXPORT void l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_197_ = stack[0].m_obj;
lean_object* v_t_198_ = stack[1].m_obj;
lean_object* v_a_199_ = stack[2].m_obj;
uint8_t v_b_u2082_200_ = stack[3].m_num;
lean_object* v_res_204_;
v_res_204_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2(v___f_197_, v_t_198_, v_a_199_, v_b_u2082_200_);
stack->m_obj
 = v_res_204_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2___boxed(lean_object* v___f_205_, lean_object* v_t_206_, lean_object* v_a_207_, lean_object* v_b_u2082_208_){
_start:
{
uint8_t v_b_u2082_boxed_209_; lean_object* v_res_210_; 
v_b_u2082_boxed_209_ = lean_unbox(v_b_u2082_208_);
v_res_210_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2(v___f_205_, v_t_206_, v_a_207_, v_b_u2082_boxed_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__5(lean_object* v___f_211_, lean_object* v___f_212_, lean_object* v_a_213_, lean_object* v_b_214_){
_start:
{
lean_object* v_changesBefore_215_; lean_object* v_changesAfter_216_; lean_object* v_changesBefore_217_; lean_object* v_changesAfter_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_227_; 
v_changesBefore_215_ = lean_ctor_get(v_a_213_, 0);
lean_inc(v_changesBefore_215_);
v_changesAfter_216_ = lean_ctor_get(v_a_213_, 1);
lean_inc(v_changesAfter_216_);
lean_dec_ref(v_a_213_);
v_changesBefore_217_ = lean_ctor_get(v_b_214_, 0);
v_changesAfter_218_ = lean_ctor_get(v_b_214_, 1);
v_isSharedCheck_227_ = !lean_is_exclusive(v_b_214_);
if (v_isSharedCheck_227_ == 0)
{
v___x_220_ = v_b_214_;
v_isShared_221_ = v_isSharedCheck_227_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_changesAfter_218_);
lean_inc(v_changesBefore_217_);
lean_dec(v_b_214_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_227_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_222_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_211_, v_changesBefore_215_, v_changesBefore_217_);
v___x_223_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_212_, v_changesAfter_216_, v_changesAfter_218_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 1, v___x_223_);
lean_ctor_set(v___x_220_, 0, v___x_222_);
v___x_225_ = v___x_220_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v___x_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0(lean_object* v_x_237_){
_start:
{
lean_object* v_fst_238_; lean_object* v_snd_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v_fst_238_ = lean_ctor_get(v_x_237_, 0);
v_snd_239_ = lean_ctor_get(v_x_237_, 1);
v___x_240_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__0));
v___x_241_ = l_Lean_SubExpr_Pos_toString(v_fst_238_);
v___x_242_ = lean_string_append(v___x_240_, v___x_241_);
lean_dec_ref(v___x_241_);
v___x_243_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__1));
v___x_244_ = lean_string_append(v___x_242_, v___x_243_);
v___x_245_ = lean_unbox(v_snd_239_);
v___x_246_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString(v___x_245_);
v___x_247_ = lean_string_append(v___x_244_, v___x_246_);
lean_dec_ref(v___x_246_);
v___x_248_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__2));
v___x_249_ = lean_string_append(v___x_247_, v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___boxed(lean_object* v_x_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0(v_x_250_);
lean_dec_ref(v_x_250_);
return v_res_251_;
}
}
lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1(lean_object* v_x1_252_, uint8_t v_x2_253_, lean_object* v_x3_254_){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_255_ = lean_box(v_x2_253_);
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v_x1_252_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set(v___x_257_, 1, v_x3_254_);
return v___x_257_;
}
}
LEAN_EXPORT void l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_252_ = stack[0].m_obj;
uint8_t v_x2_253_ = stack[1].m_num;
lean_object* v_x3_254_ = stack[2].m_obj;
lean_object* v_res_258_;
v_res_258_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1(v_x1_252_, v_x2_253_, v_x3_254_);
stack->m_obj
 = v_res_258_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1___boxed(lean_object* v_x1_259_, lean_object* v_x2_260_, lean_object* v_x3_261_){
_start:
{
uint8_t v_x2_262__boxed_262_; lean_object* v_res_263_; 
v_x2_262__boxed_262_ = lean_unbox(v_x2_260_);
v_res_263_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1(v_x1_259_, v_x2_262__boxed_262_, v_x3_261_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2(lean_object* v___f_283_, lean_object* v___f_284_, lean_object* v_p_285_){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_286_ = lean_box(0);
v___x_287_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__9));
v___x_288_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_287_, v___f_283_, v___x_286_, v_p_285_);
v___x_289_ = l_List_mapTR_loop___redArg(v___f_284_, v___x_288_, v___x_286_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3(lean_object* v_f_292_, lean_object* v___f_293_, lean_object* v_x_294_){
_start:
{
lean_object* v_changesBefore_295_; lean_object* v_changesAfter_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v_changesBefore_295_ = lean_ctor_get(v_x_294_, 0);
lean_inc(v_changesBefore_295_);
v_changesAfter_296_ = lean_ctor_get(v_x_294_, 1);
lean_inc(v_changesAfter_296_);
lean_dec_ref(v_x_294_);
v___x_297_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__0));
lean_inc_ref(v_f_292_);
v___x_298_ = lean_apply_1(v_f_292_, v_changesBefore_295_);
lean_inc_ref(v___f_293_);
v___x_299_ = l_List_toString___redArg(v___f_293_, v___x_298_);
v___x_300_ = lean_string_append(v___x_297_, v___x_299_);
lean_dec_ref(v___x_299_);
v___x_301_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__1));
v___x_302_ = lean_string_append(v___x_300_, v___x_301_);
v___x_303_ = lean_apply_1(v_f_292_, v_changesAfter_296_);
v___x_304_ = l_List_toString___redArg(v___f_293_, v___x_303_);
v___x_305_ = lean_string_append(v___x_302_, v___x_304_);
lean_dec_ref(v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(lean_object* v_k_316_, lean_object* v_v_317_, lean_object* v_t_318_){
_start:
{
if (lean_obj_tag(v_t_318_) == 0)
{
lean_object* v_size_319_; lean_object* v_k_320_; lean_object* v_v_321_; lean_object* v_l_322_; lean_object* v_r_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_604_; 
v_size_319_ = lean_ctor_get(v_t_318_, 0);
v_k_320_ = lean_ctor_get(v_t_318_, 1);
v_v_321_ = lean_ctor_get(v_t_318_, 2);
v_l_322_ = lean_ctor_get(v_t_318_, 3);
v_r_323_ = lean_ctor_get(v_t_318_, 4);
v_isSharedCheck_604_ = !lean_is_exclusive(v_t_318_);
if (v_isSharedCheck_604_ == 0)
{
v___x_325_ = v_t_318_;
v_isShared_326_ = v_isSharedCheck_604_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_r_323_);
lean_inc(v_l_322_);
lean_inc(v_v_321_);
lean_inc(v_k_320_);
lean_inc(v_size_319_);
lean_dec(v_t_318_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_604_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
uint8_t v___x_327_; 
v___x_327_ = lean_nat_dec_lt(v_k_316_, v_k_320_);
if (v___x_327_ == 0)
{
uint8_t v___x_328_; 
v___x_328_ = lean_nat_dec_eq(v_k_316_, v_k_320_);
if (v___x_328_ == 0)
{
lean_object* v_impl_329_; lean_object* v___x_330_; 
lean_dec(v_size_319_);
v_impl_329_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_k_316_, v_v_317_, v_r_323_);
v___x_330_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_322_) == 0)
{
lean_object* v_size_331_; lean_object* v_size_332_; lean_object* v_k_333_; lean_object* v_v_334_; lean_object* v_l_335_; lean_object* v_r_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v_size_331_ = lean_ctor_get(v_l_322_, 0);
v_size_332_ = lean_ctor_get(v_impl_329_, 0);
v_k_333_ = lean_ctor_get(v_impl_329_, 1);
v_v_334_ = lean_ctor_get(v_impl_329_, 2);
v_l_335_ = lean_ctor_get(v_impl_329_, 3);
lean_inc(v_l_335_);
v_r_336_ = lean_ctor_get(v_impl_329_, 4);
v___x_337_ = lean_unsigned_to_nat(3u);
v___x_338_ = lean_nat_mul(v___x_337_, v_size_331_);
v___x_339_ = lean_nat_dec_lt(v___x_338_, v_size_332_);
lean_dec(v___x_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_343_; 
lean_dec(v_l_335_);
v___x_340_ = lean_nat_add(v___x_330_, v_size_331_);
v___x_341_ = lean_nat_add(v___x_340_, v_size_332_);
lean_dec(v___x_340_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 4, v_impl_329_);
lean_ctor_set(v___x_325_, 0, v___x_341_);
v___x_343_ = v___x_325_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_k_320_);
lean_ctor_set(v_reuseFailAlloc_344_, 2, v_v_321_);
lean_ctor_set(v_reuseFailAlloc_344_, 3, v_l_322_);
lean_ctor_set(v_reuseFailAlloc_344_, 4, v_impl_329_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
else
{
lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_408_; 
lean_inc(v_r_336_);
lean_inc(v_v_334_);
lean_inc(v_k_333_);
lean_inc(v_size_332_);
v_isSharedCheck_408_ = !lean_is_exclusive(v_impl_329_);
if (v_isSharedCheck_408_ == 0)
{
lean_object* v_unused_409_; lean_object* v_unused_410_; lean_object* v_unused_411_; lean_object* v_unused_412_; lean_object* v_unused_413_; 
v_unused_409_ = lean_ctor_get(v_impl_329_, 4);
lean_dec(v_unused_409_);
v_unused_410_ = lean_ctor_get(v_impl_329_, 3);
lean_dec(v_unused_410_);
v_unused_411_ = lean_ctor_get(v_impl_329_, 2);
lean_dec(v_unused_411_);
v_unused_412_ = lean_ctor_get(v_impl_329_, 1);
lean_dec(v_unused_412_);
v_unused_413_ = lean_ctor_get(v_impl_329_, 0);
lean_dec(v_unused_413_);
v___x_346_ = v_impl_329_;
v_isShared_347_ = v_isSharedCheck_408_;
goto v_resetjp_345_;
}
else
{
lean_dec(v_impl_329_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_408_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v_size_348_; lean_object* v_k_349_; lean_object* v_v_350_; lean_object* v_l_351_; lean_object* v_r_352_; lean_object* v_size_353_; lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v_size_348_ = lean_ctor_get(v_l_335_, 0);
v_k_349_ = lean_ctor_get(v_l_335_, 1);
v_v_350_ = lean_ctor_get(v_l_335_, 2);
v_l_351_ = lean_ctor_get(v_l_335_, 3);
v_r_352_ = lean_ctor_get(v_l_335_, 4);
v_size_353_ = lean_ctor_get(v_r_336_, 0);
v___x_354_ = lean_unsigned_to_nat(2u);
v___x_355_ = lean_nat_mul(v___x_354_, v_size_353_);
v___x_356_ = lean_nat_dec_lt(v_size_348_, v___x_355_);
lean_dec(v___x_355_);
if (v___x_356_ == 0)
{
lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_384_; 
lean_inc(v_r_352_);
lean_inc(v_l_351_);
lean_inc(v_v_350_);
lean_inc(v_k_349_);
v_isSharedCheck_384_ = !lean_is_exclusive(v_l_335_);
if (v_isSharedCheck_384_ == 0)
{
lean_object* v_unused_385_; lean_object* v_unused_386_; lean_object* v_unused_387_; lean_object* v_unused_388_; lean_object* v_unused_389_; 
v_unused_385_ = lean_ctor_get(v_l_335_, 4);
lean_dec(v_unused_385_);
v_unused_386_ = lean_ctor_get(v_l_335_, 3);
lean_dec(v_unused_386_);
v_unused_387_ = lean_ctor_get(v_l_335_, 2);
lean_dec(v_unused_387_);
v_unused_388_ = lean_ctor_get(v_l_335_, 1);
lean_dec(v_unused_388_);
v_unused_389_ = lean_ctor_get(v_l_335_, 0);
lean_dec(v_unused_389_);
v___x_358_ = v_l_335_;
v_isShared_359_ = v_isSharedCheck_384_;
goto v_resetjp_357_;
}
else
{
lean_dec(v_l_335_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_384_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_374_; 
v___x_360_ = lean_nat_add(v___x_330_, v_size_331_);
v___x_361_ = lean_nat_add(v___x_360_, v_size_332_);
lean_dec(v_size_332_);
if (lean_obj_tag(v_l_351_) == 0)
{
lean_object* v_size_382_; 
v_size_382_ = lean_ctor_get(v_l_351_, 0);
lean_inc(v_size_382_);
v___y_374_ = v_size_382_;
goto v___jp_373_;
}
else
{
lean_object* v___x_383_; 
v___x_383_ = lean_unsigned_to_nat(0u);
v___y_374_ = v___x_383_;
goto v___jp_373_;
}
v___jp_362_:
{
lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_366_ = lean_nat_add(v___y_363_, v___y_365_);
lean_dec(v___y_365_);
lean_dec(v___y_363_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 4, v_r_336_);
lean_ctor_set(v___x_358_, 3, v_r_352_);
lean_ctor_set(v___x_358_, 2, v_v_334_);
lean_ctor_set(v___x_358_, 1, v_k_333_);
lean_ctor_set(v___x_358_, 0, v___x_366_);
v___x_368_ = v___x_358_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_k_333_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v_v_334_);
lean_ctor_set(v_reuseFailAlloc_372_, 3, v_r_352_);
lean_ctor_set(v_reuseFailAlloc_372_, 4, v_r_336_);
v___x_368_ = v_reuseFailAlloc_372_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_370_; 
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 4, v___x_368_);
lean_ctor_set(v___x_346_, 3, v___y_364_);
lean_ctor_set(v___x_346_, 2, v_v_350_);
lean_ctor_set(v___x_346_, 1, v_k_349_);
lean_ctor_set(v___x_346_, 0, v___x_361_);
v___x_370_ = v___x_346_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_361_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_k_349_);
lean_ctor_set(v_reuseFailAlloc_371_, 2, v_v_350_);
lean_ctor_set(v_reuseFailAlloc_371_, 3, v___y_364_);
lean_ctor_set(v_reuseFailAlloc_371_, 4, v___x_368_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
v___jp_373_:
{
lean_object* v___x_375_; lean_object* v___x_377_; 
v___x_375_ = lean_nat_add(v___x_360_, v___y_374_);
lean_dec(v___y_374_);
lean_dec(v___x_360_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 4, v_l_351_);
lean_ctor_set(v___x_325_, 0, v___x_375_);
v___x_377_ = v___x_325_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_k_320_);
lean_ctor_set(v_reuseFailAlloc_381_, 2, v_v_321_);
lean_ctor_set(v_reuseFailAlloc_381_, 3, v_l_322_);
lean_ctor_set(v_reuseFailAlloc_381_, 4, v_l_351_);
v___x_377_ = v_reuseFailAlloc_381_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_378_; 
v___x_378_ = lean_nat_add(v___x_330_, v_size_353_);
if (lean_obj_tag(v_r_352_) == 0)
{
lean_object* v_size_379_; 
v_size_379_ = lean_ctor_get(v_r_352_, 0);
lean_inc(v_size_379_);
v___y_363_ = v___x_378_;
v___y_364_ = v___x_377_;
v___y_365_ = v_size_379_;
goto v___jp_362_;
}
else
{
lean_object* v___x_380_; 
v___x_380_ = lean_unsigned_to_nat(0u);
v___y_363_ = v___x_378_;
v___y_364_ = v___x_377_;
v___y_365_ = v___x_380_;
goto v___jp_362_;
}
}
}
}
}
else
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_394_; 
lean_del_object(v___x_325_);
v___x_390_ = lean_nat_add(v___x_330_, v_size_331_);
v___x_391_ = lean_nat_add(v___x_390_, v_size_332_);
lean_dec(v_size_332_);
v___x_392_ = lean_nat_add(v___x_390_, v_size_348_);
lean_dec(v___x_390_);
lean_inc_ref(v_l_322_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 4, v_l_335_);
lean_ctor_set(v___x_346_, 3, v_l_322_);
lean_ctor_set(v___x_346_, 2, v_v_321_);
lean_ctor_set(v___x_346_, 1, v_k_320_);
lean_ctor_set(v___x_346_, 0, v___x_392_);
v___x_394_ = v___x_346_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_k_320_);
lean_ctor_set(v_reuseFailAlloc_407_, 2, v_v_321_);
lean_ctor_set(v_reuseFailAlloc_407_, 3, v_l_322_);
lean_ctor_set(v_reuseFailAlloc_407_, 4, v_l_335_);
v___x_394_ = v_reuseFailAlloc_407_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
v_isSharedCheck_401_ = !lean_is_exclusive(v_l_322_);
if (v_isSharedCheck_401_ == 0)
{
lean_object* v_unused_402_; lean_object* v_unused_403_; lean_object* v_unused_404_; lean_object* v_unused_405_; lean_object* v_unused_406_; 
v_unused_402_ = lean_ctor_get(v_l_322_, 4);
lean_dec(v_unused_402_);
v_unused_403_ = lean_ctor_get(v_l_322_, 3);
lean_dec(v_unused_403_);
v_unused_404_ = lean_ctor_get(v_l_322_, 2);
lean_dec(v_unused_404_);
v_unused_405_ = lean_ctor_get(v_l_322_, 1);
lean_dec(v_unused_405_);
v_unused_406_ = lean_ctor_get(v_l_322_, 0);
lean_dec(v_unused_406_);
v___x_396_ = v_l_322_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_dec(v_l_322_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 4, v_r_336_);
lean_ctor_set(v___x_396_, 3, v___x_394_);
lean_ctor_set(v___x_396_, 2, v_v_334_);
lean_ctor_set(v___x_396_, 1, v_k_333_);
lean_ctor_set(v___x_396_, 0, v___x_391_);
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v_k_333_);
lean_ctor_set(v_reuseFailAlloc_400_, 2, v_v_334_);
lean_ctor_set(v_reuseFailAlloc_400_, 3, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_400_, 4, v_r_336_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_414_; 
v_l_414_ = lean_ctor_get(v_impl_329_, 3);
lean_inc(v_l_414_);
if (lean_obj_tag(v_l_414_) == 0)
{
lean_object* v_r_415_; lean_object* v_k_416_; lean_object* v_v_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_440_; 
v_r_415_ = lean_ctor_get(v_impl_329_, 4);
v_k_416_ = lean_ctor_get(v_impl_329_, 1);
v_v_417_ = lean_ctor_get(v_impl_329_, 2);
v_isSharedCheck_440_ = !lean_is_exclusive(v_impl_329_);
if (v_isSharedCheck_440_ == 0)
{
lean_object* v_unused_441_; lean_object* v_unused_442_; 
v_unused_441_ = lean_ctor_get(v_impl_329_, 3);
lean_dec(v_unused_441_);
v_unused_442_ = lean_ctor_get(v_impl_329_, 0);
lean_dec(v_unused_442_);
v___x_419_ = v_impl_329_;
v_isShared_420_ = v_isSharedCheck_440_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_r_415_);
lean_inc(v_v_417_);
lean_inc(v_k_416_);
lean_dec(v_impl_329_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_440_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v_k_421_; lean_object* v_v_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_436_; 
v_k_421_ = lean_ctor_get(v_l_414_, 1);
v_v_422_ = lean_ctor_get(v_l_414_, 2);
v_isSharedCheck_436_ = !lean_is_exclusive(v_l_414_);
if (v_isSharedCheck_436_ == 0)
{
lean_object* v_unused_437_; lean_object* v_unused_438_; lean_object* v_unused_439_; 
v_unused_437_ = lean_ctor_get(v_l_414_, 4);
lean_dec(v_unused_437_);
v_unused_438_ = lean_ctor_get(v_l_414_, 3);
lean_dec(v_unused_438_);
v_unused_439_ = lean_ctor_get(v_l_414_, 0);
lean_dec(v_unused_439_);
v___x_424_ = v_l_414_;
v_isShared_425_ = v_isSharedCheck_436_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_v_422_);
lean_inc(v_k_421_);
lean_dec(v_l_414_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_436_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_426_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_415_, 2);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 4, v_r_415_);
lean_ctor_set(v___x_424_, 3, v_r_415_);
lean_ctor_set(v___x_424_, 2, v_v_321_);
lean_ctor_set(v___x_424_, 1, v_k_320_);
lean_ctor_set(v___x_424_, 0, v___x_330_);
v___x_428_ = v___x_424_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_k_320_);
lean_ctor_set(v_reuseFailAlloc_435_, 2, v_v_321_);
lean_ctor_set(v_reuseFailAlloc_435_, 3, v_r_415_);
lean_ctor_set(v_reuseFailAlloc_435_, 4, v_r_415_);
v___x_428_ = v_reuseFailAlloc_435_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_430_; 
lean_inc(v_r_415_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 3, v_r_415_);
lean_ctor_set(v___x_419_, 0, v___x_330_);
v___x_430_ = v___x_419_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_k_416_);
lean_ctor_set(v_reuseFailAlloc_434_, 2, v_v_417_);
lean_ctor_set(v_reuseFailAlloc_434_, 3, v_r_415_);
lean_ctor_set(v_reuseFailAlloc_434_, 4, v_r_415_);
v___x_430_ = v_reuseFailAlloc_434_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
lean_object* v___x_432_; 
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 4, v___x_430_);
lean_ctor_set(v___x_325_, 3, v___x_428_);
lean_ctor_set(v___x_325_, 2, v_v_422_);
lean_ctor_set(v___x_325_, 1, v_k_421_);
lean_ctor_set(v___x_325_, 0, v___x_426_);
v___x_432_ = v___x_325_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_k_421_);
lean_ctor_set(v_reuseFailAlloc_433_, 2, v_v_422_);
lean_ctor_set(v_reuseFailAlloc_433_, 3, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_433_, 4, v___x_430_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
}
}
else
{
lean_object* v_r_443_; 
v_r_443_ = lean_ctor_get(v_impl_329_, 4);
lean_inc(v_r_443_);
if (lean_obj_tag(v_r_443_) == 0)
{
lean_object* v_k_444_; lean_object* v_v_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_456_; 
v_k_444_ = lean_ctor_get(v_impl_329_, 1);
v_v_445_ = lean_ctor_get(v_impl_329_, 2);
v_isSharedCheck_456_ = !lean_is_exclusive(v_impl_329_);
if (v_isSharedCheck_456_ == 0)
{
lean_object* v_unused_457_; lean_object* v_unused_458_; lean_object* v_unused_459_; 
v_unused_457_ = lean_ctor_get(v_impl_329_, 4);
lean_dec(v_unused_457_);
v_unused_458_ = lean_ctor_get(v_impl_329_, 3);
lean_dec(v_unused_458_);
v_unused_459_ = lean_ctor_get(v_impl_329_, 0);
lean_dec(v_unused_459_);
v___x_447_ = v_impl_329_;
v_isShared_448_ = v_isSharedCheck_456_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_v_445_);
lean_inc(v_k_444_);
lean_dec(v_impl_329_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_456_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_449_ = lean_unsigned_to_nat(3u);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 4, v_l_414_);
lean_ctor_set(v___x_447_, 2, v_v_321_);
lean_ctor_set(v___x_447_, 1, v_k_320_);
lean_ctor_set(v___x_447_, 0, v___x_330_);
v___x_451_ = v___x_447_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_k_320_);
lean_ctor_set(v_reuseFailAlloc_455_, 2, v_v_321_);
lean_ctor_set(v_reuseFailAlloc_455_, 3, v_l_414_);
lean_ctor_set(v_reuseFailAlloc_455_, 4, v_l_414_);
v___x_451_ = v_reuseFailAlloc_455_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_453_; 
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 4, v_r_443_);
lean_ctor_set(v___x_325_, 3, v___x_451_);
lean_ctor_set(v___x_325_, 2, v_v_445_);
lean_ctor_set(v___x_325_, 1, v_k_444_);
lean_ctor_set(v___x_325_, 0, v___x_449_);
v___x_453_ = v___x_325_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_449_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_k_444_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v_v_445_);
lean_ctor_set(v_reuseFailAlloc_454_, 3, v___x_451_);
lean_ctor_set(v_reuseFailAlloc_454_, 4, v_r_443_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
else
{
lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_460_ = lean_unsigned_to_nat(2u);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 4, v_impl_329_);
lean_ctor_set(v___x_325_, 3, v_r_443_);
lean_ctor_set(v___x_325_, 0, v___x_460_);
v___x_462_ = v___x_325_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_k_320_);
lean_ctor_set(v_reuseFailAlloc_463_, 2, v_v_321_);
lean_ctor_set(v_reuseFailAlloc_463_, 3, v_r_443_);
lean_ctor_set(v_reuseFailAlloc_463_, 4, v_impl_329_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
}
else
{
lean_object* v___x_465_; 
lean_dec(v_v_321_);
lean_dec(v_k_320_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 2, v_v_317_);
lean_ctor_set(v___x_325_, 1, v_k_316_);
v___x_465_ = v___x_325_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_size_319_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_k_316_);
lean_ctor_set(v_reuseFailAlloc_466_, 2, v_v_317_);
lean_ctor_set(v_reuseFailAlloc_466_, 3, v_l_322_);
lean_ctor_set(v_reuseFailAlloc_466_, 4, v_r_323_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
else
{
lean_object* v_impl_467_; lean_object* v___x_468_; 
lean_dec(v_size_319_);
v_impl_467_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_k_316_, v_v_317_, v_l_322_);
v___x_468_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_323_) == 0)
{
lean_object* v_size_469_; lean_object* v_size_470_; lean_object* v_k_471_; lean_object* v_v_472_; lean_object* v_l_473_; lean_object* v_r_474_; lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v_size_469_ = lean_ctor_get(v_r_323_, 0);
v_size_470_ = lean_ctor_get(v_impl_467_, 0);
v_k_471_ = lean_ctor_get(v_impl_467_, 1);
v_v_472_ = lean_ctor_get(v_impl_467_, 2);
v_l_473_ = lean_ctor_get(v_impl_467_, 3);
v_r_474_ = lean_ctor_get(v_impl_467_, 4);
lean_inc(v_r_474_);
v___x_475_ = lean_unsigned_to_nat(3u);
v___x_476_ = lean_nat_mul(v___x_475_, v_size_469_);
v___x_477_ = lean_nat_dec_lt(v___x_476_, v_size_470_);
lean_dec(v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
lean_dec(v_r_474_);
v___x_478_ = lean_nat_add(v___x_468_, v_size_470_);
v___x_479_ = lean_nat_add(v___x_478_, v_size_469_);
lean_dec(v___x_478_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 3, v_impl_467_);
lean_ctor_set(v___x_325_, 0, v___x_479_);
v___x_481_ = v___x_325_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v_k_320_);
lean_ctor_set(v_reuseFailAlloc_482_, 2, v_v_321_);
lean_ctor_set(v_reuseFailAlloc_482_, 3, v_impl_467_);
lean_ctor_set(v_reuseFailAlloc_482_, 4, v_r_323_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
else
{
lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_548_; 
lean_inc(v_l_473_);
lean_inc(v_v_472_);
lean_inc(v_k_471_);
lean_inc(v_size_470_);
v_isSharedCheck_548_ = !lean_is_exclusive(v_impl_467_);
if (v_isSharedCheck_548_ == 0)
{
lean_object* v_unused_549_; lean_object* v_unused_550_; lean_object* v_unused_551_; lean_object* v_unused_552_; lean_object* v_unused_553_; 
v_unused_549_ = lean_ctor_get(v_impl_467_, 4);
lean_dec(v_unused_549_);
v_unused_550_ = lean_ctor_get(v_impl_467_, 3);
lean_dec(v_unused_550_);
v_unused_551_ = lean_ctor_get(v_impl_467_, 2);
lean_dec(v_unused_551_);
v_unused_552_ = lean_ctor_get(v_impl_467_, 1);
lean_dec(v_unused_552_);
v_unused_553_ = lean_ctor_get(v_impl_467_, 0);
lean_dec(v_unused_553_);
v___x_484_ = v_impl_467_;
v_isShared_485_ = v_isSharedCheck_548_;
goto v_resetjp_483_;
}
else
{
lean_dec(v_impl_467_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_548_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v_size_486_; lean_object* v_size_487_; lean_object* v_k_488_; lean_object* v_v_489_; lean_object* v_l_490_; lean_object* v_r_491_; lean_object* v___x_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v_size_486_ = lean_ctor_get(v_l_473_, 0);
v_size_487_ = lean_ctor_get(v_r_474_, 0);
v_k_488_ = lean_ctor_get(v_r_474_, 1);
v_v_489_ = lean_ctor_get(v_r_474_, 2);
v_l_490_ = lean_ctor_get(v_r_474_, 3);
v_r_491_ = lean_ctor_get(v_r_474_, 4);
v___x_492_ = lean_unsigned_to_nat(2u);
v___x_493_ = lean_nat_mul(v___x_492_, v_size_486_);
v___x_494_ = lean_nat_dec_lt(v_size_487_, v___x_493_);
lean_dec(v___x_493_);
if (v___x_494_ == 0)
{
lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_523_; 
lean_inc(v_r_491_);
lean_inc(v_l_490_);
lean_inc(v_v_489_);
lean_inc(v_k_488_);
v_isSharedCheck_523_ = !lean_is_exclusive(v_r_474_);
if (v_isSharedCheck_523_ == 0)
{
lean_object* v_unused_524_; lean_object* v_unused_525_; lean_object* v_unused_526_; lean_object* v_unused_527_; lean_object* v_unused_528_; 
v_unused_524_ = lean_ctor_get(v_r_474_, 4);
lean_dec(v_unused_524_);
v_unused_525_ = lean_ctor_get(v_r_474_, 3);
lean_dec(v_unused_525_);
v_unused_526_ = lean_ctor_get(v_r_474_, 2);
lean_dec(v_unused_526_);
v_unused_527_ = lean_ctor_get(v_r_474_, 1);
lean_dec(v_unused_527_);
v_unused_528_ = lean_ctor_get(v_r_474_, 0);
lean_dec(v_unused_528_);
v___x_496_ = v_r_474_;
v_isShared_497_ = v_isSharedCheck_523_;
goto v_resetjp_495_;
}
else
{
lean_dec(v_r_474_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_523_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___x_511_; lean_object* v___y_513_; 
v___x_498_ = lean_nat_add(v___x_468_, v_size_470_);
lean_dec(v_size_470_);
v___x_499_ = lean_nat_add(v___x_498_, v_size_469_);
lean_dec(v___x_498_);
v___x_511_ = lean_nat_add(v___x_468_, v_size_486_);
if (lean_obj_tag(v_l_490_) == 0)
{
lean_object* v_size_521_; 
v_size_521_ = lean_ctor_get(v_l_490_, 0);
lean_inc(v_size_521_);
v___y_513_ = v_size_521_;
goto v___jp_512_;
}
else
{
lean_object* v___x_522_; 
v___x_522_ = lean_unsigned_to_nat(0u);
v___y_513_ = v___x_522_;
goto v___jp_512_;
}
v___jp_500_:
{
lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_504_ = lean_nat_add(v___y_501_, v___y_503_);
lean_dec(v___y_503_);
lean_dec(v___y_501_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 4, v_r_323_);
lean_ctor_set(v___x_496_, 3, v_r_491_);
lean_ctor_set(v___x_496_, 2, v_v_321_);
lean_ctor_set(v___x_496_, 1, v_k_320_);
lean_ctor_set(v___x_496_, 0, v___x_504_);
v___x_506_ = v___x_496_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_k_320_);
lean_ctor_set(v_reuseFailAlloc_510_, 2, v_v_321_);
lean_ctor_set(v_reuseFailAlloc_510_, 3, v_r_491_);
lean_ctor_set(v_reuseFailAlloc_510_, 4, v_r_323_);
v___x_506_ = v_reuseFailAlloc_510_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_508_; 
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 4, v___x_506_);
lean_ctor_set(v___x_484_, 3, v___y_502_);
lean_ctor_set(v___x_484_, 2, v_v_489_);
lean_ctor_set(v___x_484_, 1, v_k_488_);
lean_ctor_set(v___x_484_, 0, v___x_499_);
v___x_508_ = v___x_484_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_499_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_k_488_);
lean_ctor_set(v_reuseFailAlloc_509_, 2, v_v_489_);
lean_ctor_set(v_reuseFailAlloc_509_, 3, v___y_502_);
lean_ctor_set(v_reuseFailAlloc_509_, 4, v___x_506_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
v___jp_512_:
{
lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_514_ = lean_nat_add(v___x_511_, v___y_513_);
lean_dec(v___y_513_);
lean_dec(v___x_511_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 4, v_l_490_);
lean_ctor_set(v___x_325_, 3, v_l_473_);
lean_ctor_set(v___x_325_, 2, v_v_472_);
lean_ctor_set(v___x_325_, 1, v_k_471_);
lean_ctor_set(v___x_325_, 0, v___x_514_);
v___x_516_ = v___x_325_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_520_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_520_, 3, v_l_473_);
lean_ctor_set(v_reuseFailAlloc_520_, 4, v_l_490_);
v___x_516_ = v_reuseFailAlloc_520_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_object* v___x_517_; 
v___x_517_ = lean_nat_add(v___x_468_, v_size_469_);
if (lean_obj_tag(v_r_491_) == 0)
{
lean_object* v_size_518_; 
v_size_518_ = lean_ctor_get(v_r_491_, 0);
lean_inc(v_size_518_);
v___y_501_ = v___x_517_;
v___y_502_ = v___x_516_;
v___y_503_ = v_size_518_;
goto v___jp_500_;
}
else
{
lean_object* v___x_519_; 
v___x_519_ = lean_unsigned_to_nat(0u);
v___y_501_ = v___x_517_;
v___y_502_ = v___x_516_;
v___y_503_ = v___x_519_;
goto v___jp_500_;
}
}
}
}
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_534_; 
lean_del_object(v___x_325_);
v___x_529_ = lean_nat_add(v___x_468_, v_size_470_);
lean_dec(v_size_470_);
v___x_530_ = lean_nat_add(v___x_529_, v_size_469_);
lean_dec(v___x_529_);
v___x_531_ = lean_nat_add(v___x_468_, v_size_469_);
v___x_532_ = lean_nat_add(v___x_531_, v_size_487_);
lean_dec(v___x_531_);
lean_inc_ref(v_r_323_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 4, v_r_323_);
lean_ctor_set(v___x_484_, 3, v_r_474_);
lean_ctor_set(v___x_484_, 2, v_v_321_);
lean_ctor_set(v___x_484_, 1, v_k_320_);
lean_ctor_set(v___x_484_, 0, v___x_532_);
v___x_534_ = v___x_484_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_532_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v_k_320_);
lean_ctor_set(v_reuseFailAlloc_547_, 2, v_v_321_);
lean_ctor_set(v_reuseFailAlloc_547_, 3, v_r_474_);
lean_ctor_set(v_reuseFailAlloc_547_, 4, v_r_323_);
v___x_534_ = v_reuseFailAlloc_547_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
v_isSharedCheck_541_ = !lean_is_exclusive(v_r_323_);
if (v_isSharedCheck_541_ == 0)
{
lean_object* v_unused_542_; lean_object* v_unused_543_; lean_object* v_unused_544_; lean_object* v_unused_545_; lean_object* v_unused_546_; 
v_unused_542_ = lean_ctor_get(v_r_323_, 4);
lean_dec(v_unused_542_);
v_unused_543_ = lean_ctor_get(v_r_323_, 3);
lean_dec(v_unused_543_);
v_unused_544_ = lean_ctor_get(v_r_323_, 2);
lean_dec(v_unused_544_);
v_unused_545_ = lean_ctor_get(v_r_323_, 1);
lean_dec(v_unused_545_);
v_unused_546_ = lean_ctor_get(v_r_323_, 0);
lean_dec(v_unused_546_);
v___x_536_ = v_r_323_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_dec(v_r_323_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 4, v___x_534_);
lean_ctor_set(v___x_536_, 3, v_l_473_);
lean_ctor_set(v___x_536_, 2, v_v_472_);
lean_ctor_set(v___x_536_, 1, v_k_471_);
lean_ctor_set(v___x_536_, 0, v___x_530_);
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_530_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_540_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_540_, 3, v_l_473_);
lean_ctor_set(v_reuseFailAlloc_540_, 4, v___x_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_554_; 
v_l_554_ = lean_ctor_get(v_impl_467_, 3);
if (lean_obj_tag(v_l_554_) == 0)
{
lean_object* v_r_555_; lean_object* v_k_556_; lean_object* v_v_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_568_; 
lean_inc_ref(v_l_554_);
v_r_555_ = lean_ctor_get(v_impl_467_, 4);
v_k_556_ = lean_ctor_get(v_impl_467_, 1);
v_v_557_ = lean_ctor_get(v_impl_467_, 2);
v_isSharedCheck_568_ = !lean_is_exclusive(v_impl_467_);
if (v_isSharedCheck_568_ == 0)
{
lean_object* v_unused_569_; lean_object* v_unused_570_; 
v_unused_569_ = lean_ctor_get(v_impl_467_, 3);
lean_dec(v_unused_569_);
v_unused_570_ = lean_ctor_get(v_impl_467_, 0);
lean_dec(v_unused_570_);
v___x_559_ = v_impl_467_;
v_isShared_560_ = v_isSharedCheck_568_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_r_555_);
lean_inc(v_v_557_);
lean_inc(v_k_556_);
lean_dec(v_impl_467_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_568_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_561_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_555_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 3, v_r_555_);
lean_ctor_set(v___x_559_, 2, v_v_321_);
lean_ctor_set(v___x_559_, 1, v_k_320_);
lean_ctor_set(v___x_559_, 0, v___x_468_);
v___x_563_ = v___x_559_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_k_320_);
lean_ctor_set(v_reuseFailAlloc_567_, 2, v_v_321_);
lean_ctor_set(v_reuseFailAlloc_567_, 3, v_r_555_);
lean_ctor_set(v_reuseFailAlloc_567_, 4, v_r_555_);
v___x_563_ = v_reuseFailAlloc_567_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_565_; 
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 4, v___x_563_);
lean_ctor_set(v___x_325_, 3, v_l_554_);
lean_ctor_set(v___x_325_, 2, v_v_557_);
lean_ctor_set(v___x_325_, 1, v_k_556_);
lean_ctor_set(v___x_325_, 0, v___x_561_);
v___x_565_ = v___x_325_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_k_556_);
lean_ctor_set(v_reuseFailAlloc_566_, 2, v_v_557_);
lean_ctor_set(v_reuseFailAlloc_566_, 3, v_l_554_);
lean_ctor_set(v_reuseFailAlloc_566_, 4, v___x_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
else
{
lean_object* v_r_571_; 
v_r_571_ = lean_ctor_get(v_impl_467_, 4);
lean_inc(v_r_571_);
if (lean_obj_tag(v_r_571_) == 0)
{
lean_object* v_k_572_; lean_object* v_v_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_596_; 
lean_inc(v_l_554_);
v_k_572_ = lean_ctor_get(v_impl_467_, 1);
v_v_573_ = lean_ctor_get(v_impl_467_, 2);
v_isSharedCheck_596_ = !lean_is_exclusive(v_impl_467_);
if (v_isSharedCheck_596_ == 0)
{
lean_object* v_unused_597_; lean_object* v_unused_598_; lean_object* v_unused_599_; 
v_unused_597_ = lean_ctor_get(v_impl_467_, 4);
lean_dec(v_unused_597_);
v_unused_598_ = lean_ctor_get(v_impl_467_, 3);
lean_dec(v_unused_598_);
v_unused_599_ = lean_ctor_get(v_impl_467_, 0);
lean_dec(v_unused_599_);
v___x_575_ = v_impl_467_;
v_isShared_576_ = v_isSharedCheck_596_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_v_573_);
lean_inc(v_k_572_);
lean_dec(v_impl_467_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_596_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v_k_577_; lean_object* v_v_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_592_; 
v_k_577_ = lean_ctor_get(v_r_571_, 1);
v_v_578_ = lean_ctor_get(v_r_571_, 2);
v_isSharedCheck_592_ = !lean_is_exclusive(v_r_571_);
if (v_isSharedCheck_592_ == 0)
{
lean_object* v_unused_593_; lean_object* v_unused_594_; lean_object* v_unused_595_; 
v_unused_593_ = lean_ctor_get(v_r_571_, 4);
lean_dec(v_unused_593_);
v_unused_594_ = lean_ctor_get(v_r_571_, 3);
lean_dec(v_unused_594_);
v_unused_595_ = lean_ctor_get(v_r_571_, 0);
lean_dec(v_unused_595_);
v___x_580_ = v_r_571_;
v_isShared_581_ = v_isSharedCheck_592_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_v_578_);
lean_inc(v_k_577_);
lean_dec(v_r_571_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_592_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; lean_object* v___x_584_; 
v___x_582_ = lean_unsigned_to_nat(3u);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 4, v_l_554_);
lean_ctor_set(v___x_580_, 3, v_l_554_);
lean_ctor_set(v___x_580_, 2, v_v_573_);
lean_ctor_set(v___x_580_, 1, v_k_572_);
lean_ctor_set(v___x_580_, 0, v___x_468_);
v___x_584_ = v___x_580_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_k_572_);
lean_ctor_set(v_reuseFailAlloc_591_, 2, v_v_573_);
lean_ctor_set(v_reuseFailAlloc_591_, 3, v_l_554_);
lean_ctor_set(v_reuseFailAlloc_591_, 4, v_l_554_);
v___x_584_ = v_reuseFailAlloc_591_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_586_; 
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 4, v_l_554_);
lean_ctor_set(v___x_575_, 2, v_v_321_);
lean_ctor_set(v___x_575_, 1, v_k_320_);
lean_ctor_set(v___x_575_, 0, v___x_468_);
v___x_586_ = v___x_575_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_k_320_);
lean_ctor_set(v_reuseFailAlloc_590_, 2, v_v_321_);
lean_ctor_set(v_reuseFailAlloc_590_, 3, v_l_554_);
lean_ctor_set(v_reuseFailAlloc_590_, 4, v_l_554_);
v___x_586_ = v_reuseFailAlloc_590_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_588_; 
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 4, v___x_586_);
lean_ctor_set(v___x_325_, 3, v___x_584_);
lean_ctor_set(v___x_325_, 2, v_v_578_);
lean_ctor_set(v___x_325_, 1, v_k_577_);
lean_ctor_set(v___x_325_, 0, v___x_582_);
v___x_588_ = v___x_325_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_582_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_k_577_);
lean_ctor_set(v_reuseFailAlloc_589_, 2, v_v_578_);
lean_ctor_set(v_reuseFailAlloc_589_, 3, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_589_, 4, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
}
}
else
{
lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_600_ = lean_unsigned_to_nat(2u);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 4, v_r_571_);
lean_ctor_set(v___x_325_, 3, v_impl_467_);
lean_ctor_set(v___x_325_, 0, v___x_600_);
v___x_602_ = v___x_325_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_k_320_);
lean_ctor_set(v_reuseFailAlloc_603_, 2, v_v_321_);
lean_ctor_set(v_reuseFailAlloc_603_, 3, v_impl_467_);
lean_ctor_set(v_reuseFailAlloc_603_, 4, v_r_571_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_unsigned_to_nat(1u);
v___x_606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
lean_ctor_set(v___x_606_, 1, v_k_316_);
lean_ctor_set(v___x_606_, 2, v_v_317_);
lean_ctor_set(v___x_606_, 3, v_t_318_);
lean_ctor_set(v___x_606_, 4, v_t_318_);
return v___x_606_;
}
}
}
lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange(lean_object* v_p_607_, uint8_t v_d_608_, lean_object* v_00_u03b4_609_){
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
v___x_616_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_p_607_, v___x_615_, v_changesBefore_610_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_616_);
v___x_618_ = v___x_613_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_616_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_changesAfter_611_);
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
LEAN_EXPORT void l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_607_ = stack[0].m_obj;
uint8_t v_d_608_ = stack[1].m_num;
lean_object* v_00_u03b4_609_ = stack[2].m_obj;
lean_object* v_res_621_;
v_res_621_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange(v_p_607_, v_d_608_, v_00_u03b4_609_);
stack->m_obj
 = v_res_621_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange___boxed(lean_object* v_p_622_, lean_object* v_d_623_, lean_object* v_00_u03b4_624_){
_start:
{
uint8_t v_d_boxed_625_; lean_object* v_res_626_; 
v_d_boxed_625_ = lean_unbox(v_d_623_);
v_res_626_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange(v_p_622_, v_d_boxed_625_, v_00_u03b4_624_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0(lean_object* v_00_u03b2_627_, lean_object* v_k_628_, lean_object* v_v_629_, lean_object* v_t_630_, lean_object* v_hl_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_k_628_, v_v_629_, v_t_630_);
return v___x_632_;
}
}
lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertAfterChange(lean_object* v_p_633_, uint8_t v_d_634_, lean_object* v_00_u03b4_635_){
_start:
{
lean_object* v_changesBefore_636_; lean_object* v_changesAfter_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_646_; 
v_changesBefore_636_ = lean_ctor_get(v_00_u03b4_635_, 0);
v_changesAfter_637_ = lean_ctor_get(v_00_u03b4_635_, 1);
v_isSharedCheck_646_ = !lean_is_exclusive(v_00_u03b4_635_);
if (v_isSharedCheck_646_ == 0)
{
v___x_639_ = v_00_u03b4_635_;
v_isShared_640_ = v_isSharedCheck_646_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_changesAfter_637_);
lean_inc(v_changesBefore_636_);
lean_dec(v_00_u03b4_635_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_646_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_641_ = lean_box(v_d_634_);
v___x_642_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_p_633_, v___x_641_, v_changesAfter_637_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 1, v___x_642_);
v___x_644_ = v___x_639_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_changesBefore_636_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v___x_642_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertAfterChange_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_633_ = stack[0].m_obj;
uint8_t v_d_634_ = stack[1].m_num;
lean_object* v_00_u03b4_635_ = stack[2].m_obj;
lean_object* v_res_647_;
v_res_647_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertAfterChange(v_p_633_, v_d_634_, v_00_u03b4_635_);
stack->m_obj
 = v_res_647_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertAfterChange___boxed(lean_object* v_p_648_, lean_object* v_d_649_, lean_object* v_00_u03b4_650_){
_start:
{
uint8_t v_d_boxed_651_; lean_object* v_res_652_; 
v_d_boxed_651_ = lean_unbox(v_d_649_);
v_res_652_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertAfterChange(v_p_648_, v_d_boxed_651_, v_00_u03b4_650_);
return v_res_652_;
}
}
lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(lean_object* v_before_653_, lean_object* v_after_654_, uint8_t v_d_655_){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_656_ = lean_box(1);
v___x_657_ = lean_box(v_d_655_);
v___x_658_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_before_653_, v___x_657_, v___x_656_);
v___x_659_ = lean_box(v_d_655_);
v___x_660_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_after_654_, v___x_659_, v___x_656_);
v___x_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_658_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
return v___x_661_;
}
}
LEAN_EXPORT void l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos_0interp(lean_interpreter_value* stack)
{
lean_object* v_before_653_ = stack[0].m_obj;
lean_object* v_after_654_ = stack[1].m_obj;
uint8_t v_d_655_ = stack[2].m_num;
lean_object* v_res_662_;
v_res_662_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v_before_653_, v_after_654_, v_d_655_);
stack->m_obj
 = v_res_662_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos___boxed(lean_object* v_before_663_, lean_object* v_after_664_, lean_object* v_d_665_){
_start:
{
uint8_t v_d_boxed_666_; lean_object* v_res_667_; 
v_d_boxed_666_ = lean_unbox(v_d_665_);
v_res_667_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v_before_663_, v_after_664_, v_d_boxed_666_);
return v_res_667_;
}
}
lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(lean_object* v_before_668_, lean_object* v_after_669_, uint8_t v_d_670_){
_start:
{
lean_object* v_pos_671_; lean_object* v_pos_672_; lean_object* v___x_673_; 
v_pos_671_ = lean_ctor_get(v_before_668_, 1);
lean_inc(v_pos_671_);
lean_dec_ref(v_before_668_);
v_pos_672_ = lean_ctor_get(v_after_669_, 1);
lean_inc(v_pos_672_);
lean_dec_ref(v_after_669_);
v___x_673_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v_pos_671_, v_pos_672_, v_d_670_);
return v___x_673_;
}
}
LEAN_EXPORT void l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange_0interp(lean_interpreter_value* stack)
{
lean_object* v_before_668_ = stack[0].m_obj;
lean_object* v_after_669_ = stack[1].m_obj;
uint8_t v_d_670_ = stack[2].m_num;
lean_object* v_res_674_;
v_res_674_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_668_, v_after_669_, v_d_670_);
stack->m_obj
 = v_res_674_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange___boxed(lean_object* v_before_675_, lean_object* v_after_676_, lean_object* v_d_677_){
_start:
{
uint8_t v_d_boxed_678_; lean_object* v_res_679_; 
v_d_boxed_678_ = lean_unbox(v_d_677_);
v_res_679_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_675_, v_after_676_, v_d_boxed_678_);
return v_res_679_;
}
}
uint8_t l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(lean_object* v_d_680_){
_start:
{
lean_object* v_changesAfter_681_; 
v_changesAfter_681_ = lean_ctor_get(v_d_680_, 1);
if (lean_obj_tag(v_changesAfter_681_) == 0)
{
uint8_t v___x_682_; 
v___x_682_ = 0;
return v___x_682_;
}
else
{
lean_object* v_changesBefore_683_; 
v_changesBefore_683_ = lean_ctor_get(v_d_680_, 0);
if (lean_obj_tag(v_changesBefore_683_) == 0)
{
uint8_t v___x_684_; 
v___x_684_ = 0;
return v___x_684_;
}
else
{
uint8_t v___x_685_; 
v___x_685_ = 1;
return v___x_685_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_680_ = stack[0].m_obj;
uint8_t v_res_686_;
v_res_686_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_d_680_);
stack->m_num = v_res_686_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty___boxed(lean_object* v_d_687_){
_start:
{
uint8_t v_res_688_; lean_object* v_r_689_; 
v_res_688_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_d_687_);
lean_dec_ref(v_d_687_);
v_r_689_ = lean_box(v_res_688_);
return v_r_689_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0(lean_object* v_k_690_, lean_object* v_b_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v___x_697_; 
lean_inc(v___y_695_);
lean_inc_ref(v___y_694_);
lean_inc(v___y_693_);
lean_inc_ref(v___y_692_);
v___x_697_ = lean_apply_6(v_k_690_, v_b_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, lean_box(0));
return v___x_697_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_690_ = stack[0].m_obj;
lean_object* v_b_691_ = stack[1].m_obj;
lean_object* v___y_692_ = stack[2].m_obj;
lean_object* v___y_693_ = stack[3].m_obj;
lean_object* v___y_694_ = stack[4].m_obj;
lean_object* v___y_695_ = stack[5].m_obj;
lean_object* v_res_698_;
v_res_698_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0(v_k_690_, v_b_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
stack->m_obj
 = v_res_698_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0___boxed(lean_object* v_k_699_, lean_object* v_b_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0(v_k_699_, v_b_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
return v_res_706_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(lean_object* v_name_707_, uint8_t v_bi_708_, lean_object* v_type_709_, lean_object* v_k_710_, uint8_t v_kind_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v___f_717_; lean_object* v___x_718_; 
v___f_717_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_717_, 0, v_k_710_);
v___x_718_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_707_, v_bi_708_, v_type_709_, v___f_717_, v_kind_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_718_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
v_a_727_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_718_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_718_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_707_ = stack[0].m_obj;
uint8_t v_bi_708_ = stack[1].m_num;
lean_object* v_type_709_ = stack[2].m_obj;
lean_object* v_k_710_ = stack[3].m_obj;
uint8_t v_kind_711_ = stack[4].m_num;
lean_object* v___y_712_ = stack[5].m_obj;
lean_object* v___y_713_ = stack[6].m_obj;
lean_object* v___y_714_ = stack[7].m_obj;
lean_object* v___y_715_ = stack[8].m_obj;
lean_object* v_res_735_;
v_res_735_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_name_707_, v_bi_708_, v_type_709_, v_k_710_, v_kind_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
stack->m_obj
 = v_res_735_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___boxed(lean_object* v_name_736_, lean_object* v_bi_737_, lean_object* v_type_738_, lean_object* v_k_739_, lean_object* v_kind_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
uint8_t v_bi_boxed_746_; uint8_t v_kind_boxed_747_; lean_object* v_res_748_; 
v_bi_boxed_746_ = lean_unbox(v_bi_737_);
v_kind_boxed_747_ = lean_unbox(v_kind_740_);
v_res_748_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_name_736_, v_bi_boxed_746_, v_type_738_, v_k_739_, v_kind_boxed_747_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
return v_res_748_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6(lean_object* v_00_u03b1_749_, lean_object* v_name_750_, uint8_t v_bi_751_, lean_object* v_type_752_, lean_object* v_k_753_, uint8_t v_kind_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_name_750_, v_bi_751_, v_type_752_, v_k_753_, v_kind_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
return v___x_760_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_750_ = stack[1].m_obj;
uint8_t v_bi_751_ = stack[2].m_num;
lean_object* v_type_752_ = stack[3].m_obj;
lean_object* v_k_753_ = stack[4].m_obj;
uint8_t v_kind_754_ = stack[5].m_num;
lean_object* v___y_755_ = stack[6].m_obj;
lean_object* v___y_756_ = stack[7].m_obj;
lean_object* v___y_757_ = stack[8].m_obj;
lean_object* v___y_758_ = stack[9].m_obj;
lean_object* v_res_761_;
v_res_761_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6(lean_box(0), v_name_750_, v_bi_751_, v_type_752_, v_k_753_, v_kind_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
stack->m_obj
 = v_res_761_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___boxed(lean_object* v_00_u03b1_762_, lean_object* v_name_763_, lean_object* v_bi_764_, lean_object* v_type_765_, lean_object* v_k_766_, lean_object* v_kind_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
uint8_t v_bi_boxed_773_; uint8_t v_kind_boxed_774_; lean_object* v_res_775_; 
v_bi_boxed_773_ = lean_unbox(v_bi_764_);
v_kind_boxed_774_ = lean_unbox(v_kind_767_);
v_res_775_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6(v_00_u03b1_762_, v_name_763_, v_bi_boxed_773_, v_type_765_, v_k_766_, v_kind_boxed_774_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
return v_res_775_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(lean_object* v_msgData_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v___x_782_; lean_object* v_env_783_; uint8_t v___x_784_; lean_object* v_env_785_; lean_object* v___x_786_; lean_object* v_toCold_787_; lean_object* v_mctx_788_; lean_object* v_lctx_789_; lean_object* v_options_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_782_ = lean_st_ref_get(v___y_780_);
v_env_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc_ref(v_env_783_);
lean_dec(v___x_782_);
v___x_784_ = 0;
v_env_785_ = l_Lean_Environment_setRecordingDeps(v_env_783_, v___x_784_);
v___x_786_ = lean_st_ref_get(v___y_778_);
v_toCold_787_ = lean_ctor_get(v___y_779_, 0);
v_mctx_788_ = lean_ctor_get(v___x_786_, 0);
lean_inc_ref(v_mctx_788_);
lean_dec(v___x_786_);
v_lctx_789_ = lean_ctor_get(v___y_777_, 2);
v_options_790_ = lean_ctor_get(v_toCold_787_, 2);
lean_inc_ref(v_options_790_);
lean_inc_ref(v_lctx_789_);
v___x_791_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_791_, 0, v_env_785_);
lean_ctor_set(v___x_791_, 1, v_mctx_788_);
lean_ctor_set(v___x_791_, 2, v_lctx_789_);
lean_ctor_set(v___x_791_, 3, v_options_790_);
v___x_792_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
lean_ctor_set(v___x_792_, 1, v_msgData_776_);
v___x_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
return v___x_793_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_776_ = stack[0].m_obj;
lean_object* v___y_777_ = stack[1].m_obj;
lean_object* v___y_778_ = stack[2].m_obj;
lean_object* v___y_779_ = stack[3].m_obj;
lean_object* v___y_780_ = stack[4].m_obj;
lean_object* v_res_794_;
v_res_794_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(v_msgData_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
stack->m_obj
 = v_res_794_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4___boxed(lean_object* v_msgData_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(v_msgData_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
return v_res_801_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(lean_object* v_msg_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_ref_808_; lean_object* v___x_809_; lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_818_; 
v_ref_808_ = lean_ctor_get(v___y_805_, 2);
v___x_809_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(v_msg_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
v_a_810_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_818_ == 0)
{
v___x_812_ = v___x_809_;
v_isShared_813_ = v_isSharedCheck_818_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_809_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_818_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; lean_object* v___x_816_; 
lean_inc(v_ref_808_);
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v_ref_808_);
lean_ctor_set(v___x_814_, 1, v_a_810_);
if (v_isShared_813_ == 0)
{
lean_ctor_set_tag(v___x_812_, 1);
lean_ctor_set(v___x_812_, 0, v___x_814_);
v___x_816_ = v___x_812_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_802_ = stack[0].m_obj;
lean_object* v___y_803_ = stack[1].m_obj;
lean_object* v___y_804_ = stack[2].m_obj;
lean_object* v___y_805_ = stack[3].m_obj;
lean_object* v___y_806_ = stack[4].m_obj;
lean_object* v_res_819_;
v_res_819_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v_msg_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
stack->m_obj
 = v_res_819_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg___boxed(lean_object* v_msg_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v_msg_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
return v_res_826_;
}
}
lean_object* l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(lean_object* v_x_827_, lean_object* v_x_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
if (lean_obj_tag(v_x_827_) == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = l_List_reverse___redArg(v_x_828_);
v___x_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
return v___x_835_;
}
else
{
lean_object* v_head_836_; lean_object* v_tail_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_855_; 
v_head_836_ = lean_ctor_get(v_x_827_, 0);
v_tail_837_ = lean_ctor_get(v_x_827_, 1);
v_isSharedCheck_855_ = !lean_is_exclusive(v_x_827_);
if (v_isSharedCheck_855_ == 0)
{
v___x_839_ = v_x_827_;
v_isShared_840_ = v_isSharedCheck_855_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_tail_837_);
lean_inc(v_head_836_);
lean_dec(v_x_827_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_855_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; 
v___x_841_ = l_Lean_Meta_getFVarFromUserName(v_head_836_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_844_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_a_842_);
lean_dec_ref_known(v___x_841_, 1);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 1, v_x_828_);
lean_ctor_set(v___x_839_, 0, v_a_842_);
v___x_844_ = v___x_839_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_842_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_x_828_);
v___x_844_ = v_reuseFailAlloc_846_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
v_x_827_ = v_tail_837_;
v_x_828_ = v___x_844_;
goto _start;
}
}
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
lean_del_object(v___x_839_);
lean_dec(v_tail_837_);
lean_dec(v_x_828_);
v_a_847_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_841_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_841_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_847_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_827_ = stack[0].m_obj;
lean_object* v_x_828_ = stack[1].m_obj;
lean_object* v___y_829_ = stack[2].m_obj;
lean_object* v___y_830_ = stack[3].m_obj;
lean_object* v___y_831_ = stack[4].m_obj;
lean_object* v___y_832_ = stack[5].m_obj;
lean_object* v_res_856_;
v_res_856_ = l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(v_x_827_, v_x_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
stack->m_obj
 = v_res_856_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2___boxed(lean_object* v_x_857_, lean_object* v_x_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(v_x_857_, v_x_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
return v_res_864_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(lean_object* v_upperBound_865_, lean_object* v_before_866_, lean_object* v_a_867_, lean_object* v_b_868_){
_start:
{
uint8_t v___x_870_; 
v___x_870_ = lean_nat_dec_lt(v_a_867_, v_upperBound_865_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; 
lean_dec(v_a_867_);
lean_dec_ref(v_before_866_);
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v_b_868_);
return v___x_871_;
}
else
{
lean_object* v_pos_872_; lean_object* v___x_873_; uint8_t v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_pos_872_ = lean_ctor_get(v_before_866_, 1);
lean_inc(v_pos_872_);
lean_inc(v_a_867_);
v___x_873_ = l_Lean_SubExpr_Pos_pushNthBindingDomain(v_a_867_, v_pos_872_);
v___x_874_ = 1;
v___x_875_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange(v___x_873_, v___x_874_, v_b_868_);
v___x_876_ = lean_unsigned_to_nat(1u);
v___x_877_ = lean_nat_add(v_a_867_, v___x_876_);
lean_dec(v_a_867_);
v_a_867_ = v___x_877_;
v_b_868_ = v___x_875_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_865_ = stack[0].m_obj;
lean_object* v_before_866_ = stack[1].m_obj;
lean_object* v_a_867_ = stack[2].m_obj;
lean_object* v_b_868_ = stack[3].m_obj;
lean_object* v_res_879_;
v_res_879_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v_upperBound_865_, v_before_866_, v_a_867_, v_b_868_);
stack->m_obj
 = v_res_879_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg___boxed(lean_object* v_upperBound_880_, lean_object* v_before_881_, lean_object* v_a_882_, lean_object* v_b_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v_upperBound_880_, v_before_881_, v_a_882_, v_b_883_);
lean_dec(v_upperBound_880_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0(lean_object* v_x_886_, lean_object* v_x_887_){
_start:
{
if (lean_obj_tag(v_x_886_) == 0)
{
lean_object* v___x_888_; 
v___x_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_888_, 0, v_x_887_);
return v___x_888_;
}
else
{
if (lean_obj_tag(v_x_887_) == 0)
{
lean_object* v___x_889_; 
v___x_889_ = lean_box(0);
return v___x_889_;
}
else
{
lean_object* v_head_890_; lean_object* v_tail_891_; lean_object* v_head_892_; lean_object* v_tail_893_; uint8_t v___x_894_; 
v_head_890_ = lean_ctor_get(v_x_886_, 0);
v_tail_891_ = lean_ctor_get(v_x_886_, 1);
v_head_892_ = lean_ctor_get(v_x_887_, 0);
lean_inc(v_head_892_);
v_tail_893_ = lean_ctor_get(v_x_887_, 1);
lean_inc(v_tail_893_);
lean_dec_ref_known(v_x_887_, 2);
v___x_894_ = lean_name_eq(v_head_890_, v_head_892_);
lean_dec(v_head_892_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; 
lean_dec(v_tail_893_);
v___x_895_ = lean_box(0);
return v___x_895_;
}
else
{
v_x_886_ = v_tail_891_;
v_x_887_ = v_tail_893_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0___boxed(lean_object* v_x_897_, lean_object* v_x_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0(v_x_897_, v_x_898_);
lean_dec(v_x_897_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0(lean_object* v_l_u2081_900_, lean_object* v_l_u2082_901_){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_902_ = l_List_reverse___redArg(v_l_u2081_900_);
v___x_903_ = l_List_reverse___redArg(v_l_u2082_901_);
v___x_904_ = l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0(v___x_902_, v___x_903_);
lean_dec(v___x_902_);
if (lean_obj_tag(v___x_904_) == 0)
{
return v___x_904_;
}
else
{
lean_object* v_val_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_913_; 
v_val_905_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_913_ == 0)
{
v___x_907_ = v___x_904_;
v_isShared_908_ = v_isSharedCheck_913_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_val_905_);
lean_dec(v___x_904_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_913_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_909_; lean_object* v___x_911_; 
v___x_909_ = l_List_reverse___redArg(v_val_905_);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v___x_909_);
v___x_911_ = v___x_907_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(uint8_t v_b_u2082_914_, lean_object* v_k_915_, lean_object* v_t_916_){
_start:
{
if (lean_obj_tag(v_t_916_) == 0)
{
lean_object* v_size_917_; lean_object* v_k_918_; lean_object* v_v_919_; lean_object* v_l_920_; lean_object* v_r_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_935_; 
v_size_917_ = lean_ctor_get(v_t_916_, 0);
v_k_918_ = lean_ctor_get(v_t_916_, 1);
v_v_919_ = lean_ctor_get(v_t_916_, 2);
v_l_920_ = lean_ctor_get(v_t_916_, 3);
v_r_921_ = lean_ctor_get(v_t_916_, 4);
v_isSharedCheck_935_ = !lean_is_exclusive(v_t_916_);
if (v_isSharedCheck_935_ == 0)
{
v___x_923_ = v_t_916_;
v_isShared_924_ = v_isSharedCheck_935_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_r_921_);
lean_inc(v_l_920_);
lean_inc(v_v_919_);
lean_inc(v_k_918_);
lean_inc(v_size_917_);
lean_dec(v_t_916_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_935_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
uint8_t v___x_925_; 
v___x_925_ = lean_nat_dec_lt(v_k_915_, v_k_918_);
if (v___x_925_ == 0)
{
uint8_t v___x_926_; 
v___x_926_ = lean_nat_dec_eq(v_k_915_, v_k_918_);
if (v___x_926_ == 0)
{
lean_object* v_impl_927_; lean_object* v___x_928_; 
lean_del_object(v___x_923_);
lean_dec(v_size_917_);
v_impl_927_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_914_, v_k_915_, v_r_921_);
v___x_928_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_918_, v_v_919_, v_l_920_, v_impl_927_);
return v___x_928_;
}
else
{
lean_object* v___x_929_; lean_object* v___x_931_; 
lean_dec(v_v_919_);
lean_dec(v_k_918_);
v___x_929_ = lean_box(v_b_u2082_914_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 2, v___x_929_);
lean_ctor_set(v___x_923_, 1, v_k_915_);
v___x_931_ = v___x_923_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_size_917_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_k_915_);
lean_ctor_set(v_reuseFailAlloc_932_, 2, v___x_929_);
lean_ctor_set(v_reuseFailAlloc_932_, 3, v_l_920_);
lean_ctor_set(v_reuseFailAlloc_932_, 4, v_r_921_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
else
{
lean_object* v_impl_933_; lean_object* v___x_934_; 
lean_del_object(v___x_923_);
lean_dec(v_size_917_);
v_impl_933_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_914_, v_k_915_, v_l_920_);
v___x_934_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_918_, v_v_919_, v_impl_933_, v_r_921_);
return v___x_934_;
}
}
}
else
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_936_ = lean_unsigned_to_nat(1u);
v___x_937_ = lean_box(v_b_u2082_914_);
v___x_938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_938_, 0, v___x_936_);
lean_ctor_set(v___x_938_, 1, v_k_915_);
lean_ctor_set(v___x_938_, 2, v___x_937_);
lean_ctor_set(v___x_938_, 3, v_t_916_);
lean_ctor_set(v___x_938_, 4, v_t_916_);
return v___x_938_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_u2082_914_ = stack[0].m_num;
lean_object* v_k_915_ = stack[1].m_obj;
lean_object* v_t_916_ = stack[2].m_obj;
lean_object* v_res_939_;
v_res_939_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_914_, v_k_915_, v_t_916_);
stack->m_obj
 = v_res_939_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg___boxed(lean_object* v_b_u2082_940_, lean_object* v_k_941_, lean_object* v_t_942_){
_start:
{
uint8_t v_b_u2082_boxed_943_; lean_object* v_res_944_; 
v_b_u2082_boxed_943_ = lean_unbox(v_b_u2082_940_);
v_res_944_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_boxed_943_, v_k_941_, v_t_942_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(lean_object* v_init_945_, lean_object* v_x_946_){
_start:
{
if (lean_obj_tag(v_x_946_) == 0)
{
lean_object* v_k_947_; lean_object* v_v_948_; lean_object* v_l_949_; lean_object* v_r_950_; lean_object* v___x_951_; uint8_t v___x_952_; lean_object* v___x_953_; 
v_k_947_ = lean_ctor_get(v_x_946_, 1);
lean_inc(v_k_947_);
v_v_948_ = lean_ctor_get(v_x_946_, 2);
lean_inc(v_v_948_);
v_l_949_ = lean_ctor_get(v_x_946_, 3);
lean_inc(v_l_949_);
v_r_950_ = lean_ctor_get(v_x_946_, 4);
lean_inc(v_r_950_);
lean_dec_ref_known(v_x_946_, 5);
v___x_951_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_init_945_, v_l_949_);
v___x_952_ = lean_unbox(v_v_948_);
lean_dec(v_v_948_);
v___x_953_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v___x_952_, v_k_947_, v___x_951_);
v_init_945_ = v___x_953_;
v_x_946_ = v_r_950_;
goto _start;
}
else
{
return v_init_945_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(lean_object* v_as_955_, size_t v_i_956_, size_t v_stop_957_, lean_object* v_b_958_){
_start:
{
uint8_t v___x_959_; 
v___x_959_ = lean_usize_dec_eq(v_i_956_, v_stop_957_);
if (v___x_959_ == 0)
{
lean_object* v_changesBefore_960_; lean_object* v_changesAfter_961_; lean_object* v___x_962_; lean_object* v_changesBefore_963_; lean_object* v_changesAfter_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_976_; 
v_changesBefore_960_ = lean_ctor_get(v_b_958_, 0);
lean_inc(v_changesBefore_960_);
v_changesAfter_961_ = lean_ctor_get(v_b_958_, 1);
lean_inc(v_changesAfter_961_);
lean_dec_ref(v_b_958_);
v___x_962_ = lean_array_uget(v_as_955_, v_i_956_);
v_changesBefore_963_ = lean_ctor_get(v___x_962_, 0);
v_changesAfter_964_ = lean_ctor_get(v___x_962_, 1);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_976_ == 0)
{
v___x_966_ = v___x_962_;
v_isShared_967_ = v_isSharedCheck_976_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_changesAfter_964_);
lean_inc(v_changesBefore_963_);
lean_dec(v___x_962_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_976_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_971_; 
v___x_968_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesBefore_960_, v_changesBefore_963_);
v___x_969_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesAfter_961_, v_changesAfter_964_);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 1, v___x_969_);
lean_ctor_set(v___x_966_, 0, v___x_968_);
v___x_971_ = v___x_966_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v___x_969_);
v___x_971_ = v_reuseFailAlloc_975_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
size_t v___x_972_; size_t v___x_973_; 
v___x_972_ = ((size_t)1ULL);
v___x_973_ = lean_usize_add(v_i_956_, v___x_972_);
v_i_956_ = v___x_973_;
v_b_958_ = v___x_971_;
goto _start;
}
}
}
else
{
return v_b_958_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_955_ = stack[0].m_obj;
size_t v_i_956_ = stack[1].m_num;
size_t v_stop_957_ = stack[2].m_num;
lean_object* v_b_958_ = stack[3].m_obj;
lean_object* v_res_977_;
v_res_977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_as_955_, v_i_956_, v_stop_957_, v_b_958_);
stack->m_obj
 = v_res_977_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10___boxed(lean_object* v_as_978_, lean_object* v_i_979_, lean_object* v_stop_980_, lean_object* v_b_981_){
_start:
{
size_t v_i_boxed_982_; size_t v_stop_boxed_983_; lean_object* v_res_984_; 
v_i_boxed_982_ = lean_unbox_usize(v_i_979_);
lean_dec(v_i_979_);
v_stop_boxed_983_ = lean_unbox_usize(v_stop_980_);
lean_dec(v_stop_980_);
v_res_984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_as_978_, v_i_boxed_982_, v_stop_boxed_983_, v_b_981_);
lean_dec_ref(v_as_978_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(lean_object* v_x_985_, lean_object* v_x_986_, lean_object* v_x_987_){
_start:
{
if (lean_obj_tag(v_x_985_) == 5)
{
lean_object* v_fn_988_; lean_object* v_arg_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v_fn_988_ = lean_ctor_get(v_x_985_, 0);
lean_inc_ref(v_fn_988_);
v_arg_989_ = lean_ctor_get(v_x_985_, 1);
lean_inc_ref(v_arg_989_);
lean_dec_ref_known(v_x_985_, 2);
v___x_990_ = lean_array_set(v_x_986_, v_x_987_, v_arg_989_);
v___x_991_ = lean_unsigned_to_nat(1u);
v___x_992_ = lean_nat_sub(v_x_987_, v___x_991_);
lean_dec(v_x_987_);
v_x_985_ = v_fn_988_;
v_x_986_ = v___x_990_;
v_x_987_ = v___x_992_;
goto _start;
}
else
{
lean_object* v___x_994_; 
lean_dec(v_x_987_);
v___x_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_994_, 0, v_x_985_);
lean_ctor_set(v___x_994_, 1, v_x_986_);
return v___x_994_;
}
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0(void){
_start:
{
lean_object* v___x_995_; lean_object* v_dummy_996_; 
v___x_995_ = lean_box(0);
v_dummy_996_ = l_Lean_Expr_sort___override(v___x_995_);
return v_dummy_996_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(lean_object* v_snd_997_, lean_object* v_before_998_, lean_object* v_after_999_, size_t v_sz_1000_, size_t v_i_1001_, lean_object* v_bs_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
uint8_t v___x_1008_; 
v___x_1008_ = lean_usize_dec_lt(v_i_1001_, v_sz_1000_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1009_, 0, v_bs_1002_);
return v___x_1009_;
}
else
{
lean_object* v_v_1010_; lean_object* v_fst_1011_; lean_object* v_snd_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1042_; 
v_v_1010_ = lean_array_uget(v_bs_1002_, v_i_1001_);
v_fst_1011_ = lean_ctor_get(v_v_1010_, 0);
v_snd_1012_ = lean_ctor_get(v_v_1010_, 1);
v_isSharedCheck_1042_ = !lean_is_exclusive(v_v_1010_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1014_ = v_v_1010_;
v_isShared_1015_ = v_isSharedCheck_1042_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_snd_1012_);
lean_inc(v_fst_1011_);
lean_dec(v_v_1010_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1042_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v_pos_1016_; lean_object* v_pos_1017_; lean_object* v___x_1018_; lean_object* v_bs_x27_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
v_pos_1016_ = lean_ctor_get(v_before_998_, 1);
v_pos_1017_ = lean_ctor_get(v_after_999_, 1);
v___x_1018_ = lean_unsigned_to_nat(0u);
v_bs_x27_1019_ = lean_array_uset(v_bs_1002_, v_i_1001_, v___x_1018_);
v___x_1020_ = lean_usize_to_nat(v_i_1001_);
v___x_1021_ = lean_array_get_size(v_snd_997_);
v___x_1022_ = l_Lean_SubExpr_Pos_pushNaryArg(v___x_1021_, v___x_1020_, v_pos_1016_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 1, v___x_1022_);
v___x_1024_ = v___x_1014_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_fst_1011_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = l_Lean_SubExpr_Pos_pushNaryArg(v___x_1021_, v___x_1020_, v_pos_1017_);
lean_dec(v___x_1020_);
v___x_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1026_, 0, v_snd_1012_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1024_, v___x_1026_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; size_t v___x_1029_; size_t v___x_1030_; lean_object* v___x_1031_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_a_1028_);
lean_dec_ref_known(v___x_1027_, 1);
v___x_1029_ = ((size_t)1ULL);
v___x_1030_ = lean_usize_add(v_i_1001_, v___x_1029_);
v___x_1031_ = lean_array_uset(v_bs_x27_1019_, v_i_1001_, v_a_1028_);
v_i_1001_ = v___x_1030_;
v_bs_1002_ = v___x_1031_;
goto _start;
}
else
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
lean_dec_ref(v_bs_x27_1019_);
v_a_1033_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_1027_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1027_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_997_ = stack[0].m_obj;
lean_object* v_before_998_ = stack[1].m_obj;
lean_object* v_after_999_ = stack[2].m_obj;
size_t v_sz_1000_ = stack[3].m_num;
size_t v_i_1001_ = stack[4].m_num;
lean_object* v_bs_1002_ = stack[5].m_obj;
lean_object* v___y_1003_ = stack[6].m_obj;
lean_object* v___y_1004_ = stack[7].m_obj;
lean_object* v___y_1005_ = stack[8].m_obj;
lean_object* v___y_1006_ = stack[9].m_obj;
lean_object* v_res_1043_;
v_res_1043_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_997_, v_before_998_, v_after_999_, v_sz_1000_, v_i_1001_, v_bs_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
stack->m_obj
 = v_res_1043_;
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__0));
v___x_1046_ = l_Lean_stringToMessageData(v___x_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0___boxed(lean_object* v_body_1047_, lean_object* v_pos_1048_, lean_object* v_body_1049_, lean_object* v_pos_1050_, lean_object* v_x_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0(v_body_1047_, v_pos_1048_, v_body_1049_, v_pos_1050_, v_x_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec_ref(v_x_1051_);
lean_dec(v_pos_1050_);
lean_dec_ref(v_body_1049_);
lean_dec(v_pos_1048_);
lean_dec_ref(v_body_1047_);
return v_res_1057_;
}
}
lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(lean_object* v_before_1058_, lean_object* v_after_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v_a_1071_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; uint8_t v___y_1082_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v_a_1101_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v_expr_1142_; 
v_expr_1142_ = lean_ctor_get(v_before_1058_, 0);
if (lean_obj_tag(v_expr_1142_) == 7)
{
lean_object* v_pos_1143_; lean_object* v_binderName_1144_; lean_object* v_binderType_1145_; lean_object* v_body_1146_; uint8_t v_binderInfo_1147_; lean_object* v_expr_1148_; lean_object* v_pos_1149_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; 
v_pos_1143_ = lean_ctor_get(v_before_1058_, 1);
v_binderName_1144_ = lean_ctor_get(v_expr_1142_, 0);
v_binderType_1145_ = lean_ctor_get(v_expr_1142_, 1);
v_body_1146_ = lean_ctor_get(v_expr_1142_, 2);
v_binderInfo_1147_ = lean_ctor_get_uint8(v_expr_1142_, sizeof(void*)*3 + 8);
v_expr_1148_ = lean_ctor_get(v_after_1059_, 0);
v_pos_1149_ = lean_ctor_get(v_after_1059_, 1);
if (lean_obj_tag(v_expr_1148_) == 7)
{
lean_object* v_binderName_1175_; lean_object* v_binderType_1176_; lean_object* v_body_1177_; uint8_t v_binderInfo_1178_; lean_object* v___f_1179_; uint8_t v___y_1181_; uint8_t v___x_1231_; 
v_binderName_1175_ = lean_ctor_get(v_expr_1148_, 0);
v_binderType_1176_ = lean_ctor_get(v_expr_1148_, 1);
v_body_1177_ = lean_ctor_get(v_expr_1148_, 2);
v_binderInfo_1178_ = lean_ctor_get_uint8(v_expr_1148_, sizeof(void*)*3 + 8);
lean_inc(v_pos_1149_);
lean_inc_ref(v_body_1177_);
lean_inc(v_pos_1143_);
lean_inc_ref(v_body_1146_);
v___f_1179_ = lean_alloc_closure((void*)(l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1179_, 0, v_body_1146_);
lean_closure_set(v___f_1179_, 1, v_pos_1143_);
lean_closure_set(v___f_1179_, 2, v_body_1177_);
lean_closure_set(v___f_1179_, 3, v_pos_1149_);
v___x_1231_ = lean_name_eq(v_binderName_1144_, v_binderName_1175_);
if (v___x_1231_ == 0)
{
v___y_1181_ = v___x_1231_;
goto v___jp_1180_;
}
else
{
uint8_t v___x_1232_; 
v___x_1232_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1147_, v_binderInfo_1178_);
v___y_1181_ = v___x_1232_;
goto v___jp_1180_;
}
v___jp_1180_:
{
if (v___y_1181_ == 0)
{
lean_dec_ref(v___f_1179_);
v___y_1151_ = v_a_1060_;
v___y_1152_ = v_a_1061_;
v___y_1153_ = v_a_1062_;
v___y_1154_ = v_a_1063_;
goto v___jp_1150_;
}
else
{
lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1228_; 
lean_inc_ref(v_binderType_1176_);
lean_inc(v_pos_1149_);
lean_inc_ref(v_binderType_1145_);
lean_inc(v_binderName_1144_);
lean_inc(v_pos_1143_);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_before_1058_);
if (v_isSharedCheck_1228_ == 0)
{
lean_object* v_unused_1229_; lean_object* v_unused_1230_; 
v_unused_1229_ = lean_ctor_get(v_before_1058_, 1);
lean_dec(v_unused_1229_);
v_unused_1230_ = lean_ctor_get(v_before_1058_, 0);
lean_dec(v_unused_1230_);
v___x_1183_ = v_before_1058_;
v_isShared_1184_ = v_isSharedCheck_1228_;
goto v_resetjp_1182_;
}
else
{
lean_dec(v_before_1058_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1228_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1225_; 
v_isSharedCheck_1225_ = !lean_is_exclusive(v_after_1059_);
if (v_isSharedCheck_1225_ == 0)
{
lean_object* v_unused_1226_; lean_object* v_unused_1227_; 
v_unused_1226_ = lean_ctor_get(v_after_1059_, 1);
lean_dec(v_unused_1226_);
v_unused_1227_ = lean_ctor_get(v_after_1059_, 0);
lean_dec(v_unused_1227_);
v___x_1186_ = v_after_1059_;
v_isShared_1187_ = v_isSharedCheck_1225_;
goto v_resetjp_1185_;
}
else
{
lean_dec(v_after_1059_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1225_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1188_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1143_);
lean_inc_ref(v_binderType_1145_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 1, v___x_1188_);
lean_ctor_set(v___x_1186_, 0, v_binderType_1145_);
v___x_1190_ = v___x_1186_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_binderType_1145_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1191_; lean_object* v___x_1193_; 
v___x_1191_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1149_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 1, v___x_1191_);
lean_ctor_set(v___x_1183_, 0, v_binderType_1176_);
v___x_1193_ = v___x_1183_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_binderType_1176_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1194_; 
v___x_1194_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1190_, v___x_1193_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1222_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1197_ = v___x_1194_;
v_isShared_1198_ = v_isSharedCheck_1222_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1194_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1222_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
uint8_t v___x_1199_; 
v___x_1199_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_a_1195_);
if (v___x_1199_ == 0)
{
lean_object* v_changesBefore_1200_; lean_object* v_changesAfter_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; lean_object* v___x_1205_; lean_object* v_changesBefore_1206_; lean_object* v_changesAfter_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1219_; 
lean_dec_ref(v___f_1179_);
lean_dec_ref(v_binderType_1145_);
lean_dec(v_binderName_1144_);
v_changesBefore_1200_ = lean_ctor_get(v_a_1195_, 0);
lean_inc(v_changesBefore_1200_);
v_changesAfter_1201_ = lean_ctor_get(v_a_1195_, 1);
lean_inc(v_changesAfter_1201_);
lean_dec(v_a_1195_);
v___x_1202_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1143_);
lean_dec(v_pos_1143_);
v___x_1203_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1149_);
lean_dec(v_pos_1149_);
v___x_1204_ = 0;
v___x_1205_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v___x_1202_, v___x_1203_, v___x_1204_);
v_changesBefore_1206_ = lean_ctor_get(v___x_1205_, 0);
v_changesAfter_1207_ = lean_ctor_get(v___x_1205_, 1);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1209_ = v___x_1205_;
v_isShared_1210_ = v_isSharedCheck_1219_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_changesAfter_1207_);
lean_inc(v_changesBefore_1206_);
lean_dec(v___x_1205_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1219_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1211_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesBefore_1200_, v_changesBefore_1206_);
v___x_1212_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesAfter_1201_, v_changesAfter_1207_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 1, v___x_1212_);
lean_ctor_set(v___x_1209_, 0, v___x_1211_);
v___x_1214_ = v___x_1209_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1211_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1216_; 
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 0, v___x_1214_);
v___x_1216_ = v___x_1197_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
else
{
uint8_t v___x_1220_; lean_object* v___x_1221_; 
lean_del_object(v___x_1197_);
lean_dec(v_a_1195_);
lean_dec(v_pos_1149_);
lean_dec(v_pos_1143_);
v___x_1220_ = 0;
v___x_1221_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_binderName_1144_, v_binderInfo_1147_, v_binderType_1145_, v___f_1179_, v___x_1220_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
return v___x_1221_;
}
}
}
else
{
lean_dec_ref(v___f_1179_);
lean_dec(v_pos_1149_);
lean_dec_ref(v_binderType_1145_);
lean_dec(v_binderName_1144_);
lean_dec(v_pos_1143_);
return v___x_1194_;
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
v___y_1151_ = v_a_1060_;
v___y_1152_ = v_a_1061_;
v___y_1153_ = v_a_1062_;
v___y_1154_ = v_a_1063_;
goto v___jp_1150_;
}
v___jp_1150_:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1155_ = l_Lean_Expr_getForallBinderNames(v_expr_1148_);
v___x_1156_ = l_Lean_Expr_getForallBinderNames(v_expr_1142_);
v___x_1157_ = l_List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0(v___x_1155_, v___x_1156_);
if (lean_obj_tag(v___x_1157_) == 1)
{
lean_object* v_val_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; 
v_val_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_val_1158_);
lean_dec_ref_known(v___x_1157_, 1);
v___x_1159_ = l_List_lengthTR___redArg(v_val_1158_);
v___x_1160_ = lean_unsigned_to_nat(0u);
v___x_1161_ = lean_nat_dec_eq(v___x_1159_, v___x_1160_);
lean_dec(v___x_1159_);
if (v___x_1161_ == 0)
{
lean_inc_ref(v_expr_1142_);
lean_inc(v_pos_1143_);
v___y_1105_ = v_val_1158_;
v___y_1106_ = v_pos_1143_;
v___y_1107_ = v_expr_1142_;
v___y_1108_ = v___y_1151_;
v___y_1109_ = v___y_1152_;
v___y_1110_ = v___y_1153_;
v___y_1111_ = v___y_1154_;
goto v___jp_1104_;
}
else
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1, &l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1);
v___x_1163_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_1162_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_dec_ref_known(v___x_1163_, 1);
lean_inc_ref(v_expr_1142_);
lean_inc(v_pos_1143_);
v___y_1105_ = v_val_1158_;
v___y_1106_ = v_pos_1143_;
v___y_1107_ = v_expr_1142_;
v___y_1108_ = v___y_1151_;
v___y_1109_ = v___y_1152_;
v___y_1110_ = v___y_1153_;
v___y_1111_ = v___y_1154_;
goto v___jp_1104_;
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
lean_dec(v_val_1158_);
lean_dec_ref(v_after_1059_);
lean_dec_ref(v_before_1058_);
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1163_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1163_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
else
{
uint8_t v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
lean_dec(v___x_1157_);
v___x_1172_ = 0;
v___x_1173_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1058_, v_after_1059_, v___x_1172_);
v___x_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
return v___x_1174_;
}
}
}
else
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
lean_dec_ref(v_after_1059_);
lean_dec_ref(v_before_1058_);
v___x_1233_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___x_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
return v___x_1234_;
}
v___jp_1065_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_unsigned_to_nat(0u);
v___x_1073_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v___y_1069_, v_before_1058_, v___x_1072_, v_a_1071_);
lean_dec(v___y_1069_);
return v___x_1073_;
}
v___jp_1074_:
{
if (v___y_1082_ == 0)
{
lean_object* v___x_1083_; 
lean_dec_ref(v___y_1076_);
v___x_1083_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1077_, v___y_1078_, v___y_1081_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v___x_1084_; 
lean_dec_ref_known(v___x_1083_, 1);
v___x_1084_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___y_1066_ = v___y_1075_;
v___y_1067_ = v___y_1078_;
v___y_1068_ = v___y_1079_;
v___y_1069_ = v___y_1080_;
v___y_1070_ = v___y_1081_;
v_a_1071_ = v___x_1084_;
goto v___jp_1065_;
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
lean_dec(v___y_1080_);
lean_dec_ref(v_before_1058_);
v_a_1085_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1083_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1083_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
else
{
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1077_);
lean_dec_ref(v_before_1058_);
return v___y_1076_;
}
}
v___jp_1093_:
{
uint8_t v___x_1102_; 
v___x_1102_ = l_Lean_Exception_isInterrupt(v_a_1101_);
if (v___x_1102_ == 0)
{
uint8_t v___x_1103_; 
v___x_1103_ = l_Lean_Exception_isRuntime(v_a_1101_);
v___y_1075_ = v___y_1094_;
v___y_1076_ = v___y_1100_;
v___y_1077_ = v___y_1095_;
v___y_1078_ = v___y_1096_;
v___y_1079_ = v___y_1097_;
v___y_1080_ = v___y_1098_;
v___y_1081_ = v___y_1099_;
v___y_1082_ = v___x_1103_;
goto v___jp_1074_;
}
else
{
lean_dec_ref(v_a_1101_);
v___y_1075_ = v___y_1094_;
v___y_1076_ = v___y_1100_;
v___y_1077_ = v___y_1095_;
v___y_1078_ = v___y_1096_;
v___y_1079_ = v___y_1097_;
v___y_1080_ = v___y_1098_;
v___y_1081_ = v___y_1099_;
v___y_1082_ = v___x_1102_;
goto v___jp_1074_;
}
}
v___jp_1104_:
{
lean_object* v___x_1112_; lean_object* v_body_u2080_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1112_ = l_List_lengthTR___redArg(v___y_1105_);
lean_inc(v___x_1112_);
v_body_u2080_1113_ = l_Lean_Expr_getForallBodyMaxDepth(v___x_1112_, v___y_1107_);
lean_dec_ref(v___y_1107_);
v___x_1114_ = lean_box(0);
v___x_1115_ = l_Lean_Meta_saveState___redArg(v___y_1109_, v___y_1111_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1117_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
lean_dec_ref_known(v___x_1115_, 1);
v___x_1117_ = l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(v___y_1105_, v___x_1114_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1117_, 1);
v___x_1119_ = lean_array_mk(v_a_1118_);
v___x_1120_ = lean_expr_instantiate_rev(v_body_u2080_1113_, v___x_1119_);
lean_dec_ref(v___x_1119_);
lean_dec_ref(v_body_u2080_1113_);
lean_inc(v___x_1112_);
v___x_1121_ = l_Lean_SubExpr_Pos_pushNthBindingBody(v___x_1112_, v___y_1106_);
v___x_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1120_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1122_, v_after_1059_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; 
lean_dec(v_a_1116_);
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_a_1124_);
lean_dec_ref_known(v___x_1123_, 1);
v___y_1066_ = v___y_1108_;
v___y_1067_ = v___y_1109_;
v___y_1068_ = v___y_1110_;
v___y_1069_ = v___x_1112_;
v___y_1070_ = v___y_1111_;
v_a_1071_ = v_a_1124_;
goto v___jp_1065_;
}
else
{
lean_object* v_a_1125_; 
v_a_1125_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_a_1125_);
v___y_1094_ = v___y_1108_;
v___y_1095_ = v_a_1116_;
v___y_1096_ = v___y_1109_;
v___y_1097_ = v___y_1110_;
v___y_1098_ = v___x_1112_;
v___y_1099_ = v___y_1111_;
v___y_1100_ = v___x_1123_;
v_a_1101_ = v_a_1125_;
goto v___jp_1093_;
}
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_dec_ref(v_body_u2080_1113_);
lean_dec(v___y_1106_);
lean_dec_ref(v_after_1059_);
v_a_1126_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1117_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1117_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
lean_inc(v_a_1126_);
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
v___y_1094_ = v___y_1108_;
v___y_1095_ = v_a_1116_;
v___y_1096_ = v___y_1109_;
v___y_1097_ = v___y_1110_;
v___y_1098_ = v___x_1112_;
v___y_1099_ = v___y_1111_;
v___y_1100_ = v___x_1131_;
v_a_1101_ = v_a_1126_;
goto v___jp_1093_;
}
}
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec_ref(v_body_u2080_1113_);
lean_dec(v___x_1112_);
lean_dec(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v_after_1059_);
lean_dec_ref(v_before_1058_);
v_a_1134_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1115_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1115_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_0interp(lean_interpreter_value* stack)
{
lean_object* v_before_1058_ = stack[0].m_obj;
lean_object* v_after_1059_ = stack[1].m_obj;
lean_object* v_a_1060_ = stack[2].m_obj;
lean_object* v_a_1061_ = stack[3].m_obj;
lean_object* v_a_1062_ = stack[4].m_obj;
lean_object* v_a_1063_ = stack[5].m_obj;
lean_object* v_res_1235_;
v_res_1235_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(v_before_1058_, v_after_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
stack->m_obj
 = v_res_1235_;
}
lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(lean_object* v_before_1236_, lean_object* v_after_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_){
_start:
{
lean_object* v_expr_1259_; lean_object* v_pos_1260_; lean_object* v_expr_1261_; lean_object* v_pos_1262_; lean_object* v_e_u2081_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; uint8_t v___x_1271_; 
v_expr_1259_ = lean_ctor_get(v_before_1236_, 0);
v_pos_1260_ = lean_ctor_get(v_before_1236_, 1);
v_expr_1261_ = lean_ctor_get(v_after_1237_, 0);
v_pos_1262_ = lean_ctor_get(v_after_1237_, 1);
v___x_1271_ = lean_expr_eqv(v_expr_1259_, v_expr_1261_);
if (v___x_1271_ == 0)
{
switch(lean_obj_tag(v_expr_1259_))
{
case 10:
{
lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1280_; 
lean_inc_ref(v_expr_1259_);
lean_inc(v_pos_1260_);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_before_1236_);
if (v_isSharedCheck_1280_ == 0)
{
lean_object* v_unused_1281_; lean_object* v_unused_1282_; 
v_unused_1281_ = lean_ctor_get(v_before_1236_, 1);
lean_dec(v_unused_1281_);
v_unused_1282_ = lean_ctor_get(v_before_1236_, 0);
lean_dec(v_unused_1282_);
v___x_1273_ = v_before_1236_;
v_isShared_1274_ = v_isSharedCheck_1280_;
goto v_resetjp_1272_;
}
else
{
lean_dec(v_before_1236_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1280_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v_expr_1275_; lean_object* v___x_1277_; 
v_expr_1275_ = lean_ctor_get(v_expr_1259_, 1);
lean_inc_ref(v_expr_1275_);
lean_dec_ref_known(v_expr_1259_, 2);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v_expr_1275_);
v___x_1277_ = v___x_1273_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_expr_1275_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v_pos_1260_);
v___x_1277_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
v_before_1236_ = v___x_1277_;
goto _start;
}
}
}
case 5:
{
switch(lean_obj_tag(v_expr_1261_))
{
case 10:
{
lean_object* v_expr_1283_; 
lean_inc_ref(v_expr_1261_);
lean_inc(v_pos_1262_);
lean_dec_ref(v_after_1237_);
v_expr_1283_ = lean_ctor_get(v_expr_1261_, 1);
lean_inc_ref(v_expr_1283_);
lean_dec_ref_known(v_expr_1261_, 2);
v_e_u2081_1264_ = v_expr_1283_;
v___y_1265_ = v_a_1238_;
v___y_1266_ = v_a_1239_;
v___y_1267_ = v_a_1240_;
v___y_1268_ = v_a_1241_;
goto v___jp_1263_;
}
case 5:
{
lean_object* v_dummy_1284_; lean_object* v_nargs_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v_fst_1290_; lean_object* v_snd_1291_; lean_object* v_nargs_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v_fst_1296_; lean_object* v_snd_1297_; uint8_t v___x_1298_; 
v_dummy_1284_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0, &l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0);
v_nargs_1285_ = l_Lean_Expr_getAppNumArgs(v_expr_1261_);
lean_inc(v_nargs_1285_);
v___x_1286_ = lean_mk_array(v_nargs_1285_, v_dummy_1284_);
v___x_1287_ = lean_unsigned_to_nat(1u);
v___x_1288_ = lean_nat_sub(v_nargs_1285_, v___x_1287_);
lean_dec(v_nargs_1285_);
lean_inc_ref(v_expr_1261_);
v___x_1289_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(v_expr_1261_, v___x_1286_, v___x_1288_);
v_fst_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_fst_1290_);
v_snd_1291_ = lean_ctor_get(v___x_1289_, 1);
lean_inc(v_snd_1291_);
lean_dec_ref(v___x_1289_);
v_nargs_1292_ = l_Lean_Expr_getAppNumArgs(v_expr_1259_);
lean_inc(v_nargs_1292_);
v___x_1293_ = lean_mk_array(v_nargs_1292_, v_dummy_1284_);
v___x_1294_ = lean_nat_sub(v_nargs_1292_, v___x_1287_);
lean_dec(v_nargs_1292_);
lean_inc_ref(v_expr_1259_);
v___x_1295_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(v_expr_1259_, v___x_1293_, v___x_1294_);
v_fst_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_fst_1296_);
v_snd_1297_ = lean_ctor_get(v___x_1295_, 1);
lean_inc(v_snd_1297_);
lean_dec_ref(v___x_1295_);
v___x_1298_ = lean_expr_eqv(v_fst_1290_, v_fst_1296_);
lean_dec(v_fst_1296_);
lean_dec(v_fst_1290_);
if (v___x_1298_ == 0)
{
lean_dec(v_snd_1297_);
lean_dec(v_snd_1291_);
goto v___jp_1251_;
}
else
{
if (v___x_1271_ == 0)
{
lean_object* v___x_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v___x_1299_ = lean_array_get_size(v_snd_1291_);
v___x_1300_ = lean_array_get_size(v_snd_1297_);
v___x_1301_ = lean_nat_dec_eq(v___x_1299_, v___x_1300_);
if (v___x_1301_ == 0)
{
lean_dec(v_snd_1297_);
lean_dec(v_snd_1291_);
goto v___jp_1251_;
}
else
{
if (v___x_1271_ == 0)
{
lean_object* v_args_1302_; size_t v_sz_1303_; size_t v___x_1304_; lean_object* v___x_1305_; 
v_args_1302_ = l_Array_zip___redArg(v_snd_1291_, v_snd_1297_);
lean_dec(v_snd_1297_);
v_sz_1303_ = lean_array_size(v_args_1302_);
v___x_1304_ = ((size_t)0ULL);
v___x_1305_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_1291_, v_before_1236_, v_after_1237_, v_sz_1303_, v___x_1304_, v_args_1302_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
lean_dec_ref(v_after_1237_);
lean_dec_ref(v_before_1236_);
lean_dec(v_snd_1291_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1331_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1308_ = v___x_1305_;
v_isShared_1309_ = v_isSharedCheck_1331_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1305_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1331_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; 
v___x_1310_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___x_1311_ = lean_unsigned_to_nat(0u);
v___x_1312_ = lean_array_get_size(v_a_1306_);
v___x_1313_ = lean_nat_dec_lt(v___x_1311_, v___x_1312_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1315_; 
lean_dec(v_a_1306_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v___x_1310_);
v___x_1315_ = v___x_1308_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
else
{
uint8_t v___x_1317_; 
v___x_1317_ = lean_nat_dec_le(v___x_1312_, v___x_1312_);
if (v___x_1317_ == 0)
{
if (v___x_1313_ == 0)
{
lean_object* v___x_1319_; 
lean_dec(v_a_1306_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v___x_1310_);
v___x_1319_ = v___x_1308_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1310_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
else
{
size_t v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1324_; 
v___x_1321_ = lean_usize_of_nat(v___x_1312_);
v___x_1322_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_a_1306_, v___x_1304_, v___x_1321_, v___x_1310_);
lean_dec(v_a_1306_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v___x_1322_);
v___x_1324_ = v___x_1308_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
else
{
size_t v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1329_; 
v___x_1326_ = lean_usize_of_nat(v___x_1312_);
v___x_1327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_a_1306_, v___x_1304_, v___x_1326_, v___x_1310_);
lean_dec(v_a_1306_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v___x_1327_);
v___x_1329_ = v___x_1308_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1327_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
}
else
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
v_a_1332_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1305_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1305_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
else
{
lean_dec(v_snd_1297_);
lean_dec(v_snd_1291_);
goto v___jp_1251_;
}
}
}
else
{
lean_dec(v_snd_1297_);
lean_dec(v_snd_1291_);
goto v___jp_1251_;
}
}
}
default: 
{
goto v___jp_1255_;
}
}
}
case 7:
{
if (lean_obj_tag(v_expr_1261_) == 10)
{
lean_object* v_expr_1340_; 
lean_inc_ref(v_expr_1261_);
lean_inc(v_pos_1262_);
lean_dec_ref(v_after_1237_);
v_expr_1340_ = lean_ctor_get(v_expr_1261_, 1);
lean_inc_ref(v_expr_1340_);
lean_dec_ref_known(v_expr_1261_, 2);
v_e_u2081_1264_ = v_expr_1340_;
v___y_1265_ = v_a_1238_;
v___y_1266_ = v_a_1239_;
v___y_1267_ = v_a_1240_;
v___y_1268_ = v_a_1241_;
goto v___jp_1263_;
}
else
{
lean_object* v___x_1341_; 
v___x_1341_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(v_before_1236_, v_after_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
return v___x_1341_;
}
}
case 6:
{
switch(lean_obj_tag(v_expr_1261_))
{
case 10:
{
lean_object* v_expr_1342_; 
lean_inc_ref(v_expr_1261_);
lean_inc(v_pos_1262_);
lean_dec_ref(v_after_1237_);
v_expr_1342_ = lean_ctor_get(v_expr_1261_, 1);
lean_inc_ref(v_expr_1342_);
lean_dec_ref_known(v_expr_1261_, 2);
v_e_u2081_1264_ = v_expr_1342_;
v___y_1265_ = v_a_1238_;
v___y_1266_ = v_a_1239_;
v___y_1267_ = v_a_1240_;
v___y_1268_ = v_a_1241_;
goto v___jp_1263_;
}
case 6:
{
lean_object* v_binderName_1343_; lean_object* v_binderType_1344_; lean_object* v_body_1345_; uint8_t v_binderInfo_1346_; lean_object* v_binderName_1347_; lean_object* v_binderType_1348_; lean_object* v_body_1349_; uint8_t v_binderInfo_1350_; uint8_t v___x_1351_; 
v_binderName_1343_ = lean_ctor_get(v_expr_1259_, 0);
v_binderType_1344_ = lean_ctor_get(v_expr_1259_, 1);
v_body_1345_ = lean_ctor_get(v_expr_1259_, 2);
v_binderInfo_1346_ = lean_ctor_get_uint8(v_expr_1259_, sizeof(void*)*3 + 8);
v_binderName_1347_ = lean_ctor_get(v_expr_1261_, 0);
v_binderType_1348_ = lean_ctor_get(v_expr_1261_, 1);
v_body_1349_ = lean_ctor_get(v_expr_1261_, 2);
v_binderInfo_1350_ = lean_ctor_get_uint8(v_expr_1261_, sizeof(void*)*3 + 8);
v___x_1351_ = lean_name_eq(v_binderName_1343_, v_binderName_1347_);
if (v___x_1351_ == 0)
{
goto v___jp_1247_;
}
else
{
if (v___x_1271_ == 0)
{
uint8_t v___x_1352_; 
v___x_1352_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1346_, v_binderInfo_1350_);
if (v___x_1352_ == 0)
{
goto v___jp_1247_;
}
else
{
if (v___x_1271_ == 0)
{
lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1402_; 
lean_inc_ref(v_body_1349_);
lean_inc_ref(v_binderType_1348_);
lean_inc_ref(v_body_1345_);
lean_inc_ref(v_binderType_1344_);
lean_inc(v_pos_1262_);
lean_inc(v_pos_1260_);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_before_1236_);
if (v_isSharedCheck_1402_ == 0)
{
lean_object* v_unused_1403_; lean_object* v_unused_1404_; 
v_unused_1403_ = lean_ctor_get(v_before_1236_, 1);
lean_dec(v_unused_1403_);
v_unused_1404_ = lean_ctor_get(v_before_1236_, 0);
lean_dec(v_unused_1404_);
v___x_1354_ = v_before_1236_;
v_isShared_1355_ = v_isSharedCheck_1402_;
goto v_resetjp_1353_;
}
else
{
lean_dec(v_before_1236_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1402_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1399_; 
v_isSharedCheck_1399_ = !lean_is_exclusive(v_after_1237_);
if (v_isSharedCheck_1399_ == 0)
{
lean_object* v_unused_1400_; lean_object* v_unused_1401_; 
v_unused_1400_ = lean_ctor_get(v_after_1237_, 1);
lean_dec(v_unused_1400_);
v_unused_1401_ = lean_ctor_get(v_after_1237_, 0);
lean_dec(v_unused_1401_);
v___x_1357_ = v_after_1237_;
v_isShared_1358_ = v_isSharedCheck_1399_;
goto v_resetjp_1356_;
}
else
{
lean_dec(v_after_1237_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1399_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1359_; lean_object* v___x_1361_; 
v___x_1359_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1260_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 1, v___x_1359_);
lean_ctor_set(v___x_1357_, 0, v_binderType_1344_);
v___x_1361_ = v___x_1357_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_binderType_1344_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v___x_1359_);
v___x_1361_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
lean_object* v___x_1362_; lean_object* v___x_1364_; 
v___x_1362_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1262_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 1, v___x_1362_);
lean_ctor_set(v___x_1354_, 0, v_binderType_1348_);
v___x_1364_ = v___x_1354_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_binderType_1348_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v___x_1362_);
v___x_1364_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
lean_object* v___x_1365_; 
v___x_1365_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1361_, v___x_1364_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1396_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1368_ = v___x_1365_;
v_isShared_1369_ = v_isSharedCheck_1396_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1365_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1396_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
uint8_t v___x_1370_; 
v___x_1370_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_a_1366_);
if (v___x_1370_ == 0)
{
lean_object* v_changesBefore_1371_; lean_object* v_changesAfter_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; uint8_t v___x_1375_; lean_object* v___x_1376_; lean_object* v_changesBefore_1377_; lean_object* v_changesAfter_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1390_; 
lean_dec_ref(v_body_1349_);
lean_dec_ref(v_body_1345_);
v_changesBefore_1371_ = lean_ctor_get(v_a_1366_, 0);
lean_inc(v_changesBefore_1371_);
v_changesAfter_1372_ = lean_ctor_get(v_a_1366_, 1);
lean_inc(v_changesAfter_1372_);
lean_dec(v_a_1366_);
v___x_1373_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1260_);
lean_dec(v_pos_1260_);
v___x_1374_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1262_);
lean_dec(v_pos_1262_);
v___x_1375_ = 0;
v___x_1376_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v___x_1373_, v___x_1374_, v___x_1375_);
v_changesBefore_1377_ = lean_ctor_get(v___x_1376_, 0);
v_changesAfter_1378_ = lean_ctor_get(v___x_1376_, 1);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1380_ = v___x_1376_;
v_isShared_1381_ = v_isSharedCheck_1390_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_changesAfter_1378_);
lean_inc(v_changesBefore_1377_);
lean_dec(v___x_1376_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1390_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1385_; 
v___x_1382_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesBefore_1371_, v_changesBefore_1377_);
v___x_1383_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesAfter_1372_, v_changesAfter_1378_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 1, v___x_1383_);
lean_ctor_set(v___x_1380_, 0, v___x_1382_);
v___x_1385_ = v___x_1380_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v___x_1383_);
v___x_1385_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
lean_object* v___x_1387_; 
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 0, v___x_1385_);
v___x_1387_ = v___x_1368_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
else
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
lean_del_object(v___x_1368_);
lean_dec(v_a_1366_);
v___x_1391_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1260_);
lean_dec(v_pos_1260_);
v___x_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1392_, 0, v_body_1345_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
v___x_1393_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1262_);
lean_dec(v_pos_1262_);
v___x_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1394_, 0, v_body_1349_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
v_before_1236_ = v___x_1392_;
v_after_1237_ = v___x_1394_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_body_1349_);
lean_dec_ref(v_body_1345_);
lean_dec(v_pos_1262_);
lean_dec(v_pos_1260_);
return v___x_1365_;
}
}
}
}
}
}
else
{
goto v___jp_1247_;
}
}
}
else
{
goto v___jp_1247_;
}
}
}
default: 
{
goto v___jp_1255_;
}
}
}
case 11:
{
switch(lean_obj_tag(v_expr_1261_))
{
case 10:
{
lean_object* v_expr_1405_; 
lean_inc_ref(v_expr_1261_);
lean_inc(v_pos_1262_);
lean_dec_ref(v_after_1237_);
v_expr_1405_ = lean_ctor_get(v_expr_1261_, 1);
lean_inc_ref(v_expr_1405_);
lean_dec_ref_known(v_expr_1261_, 2);
v_e_u2081_1264_ = v_expr_1405_;
v___y_1265_ = v_a_1238_;
v___y_1266_ = v_a_1239_;
v___y_1267_ = v_a_1240_;
v___y_1268_ = v_a_1241_;
goto v___jp_1263_;
}
case 11:
{
lean_object* v_typeName_1406_; lean_object* v_idx_1407_; lean_object* v_struct_1408_; lean_object* v_typeName_1409_; lean_object* v_idx_1410_; lean_object* v_struct_1411_; uint8_t v___x_1412_; 
v_typeName_1406_ = lean_ctor_get(v_expr_1259_, 0);
v_idx_1407_ = lean_ctor_get(v_expr_1259_, 1);
v_struct_1408_ = lean_ctor_get(v_expr_1259_, 2);
v_typeName_1409_ = lean_ctor_get(v_expr_1261_, 0);
v_idx_1410_ = lean_ctor_get(v_expr_1261_, 1);
v_struct_1411_ = lean_ctor_get(v_expr_1261_, 2);
v___x_1412_ = lean_name_eq(v_typeName_1406_, v_typeName_1409_);
if (v___x_1412_ == 0)
{
goto v___jp_1243_;
}
else
{
if (v___x_1271_ == 0)
{
uint8_t v___x_1413_; 
v___x_1413_ = lean_nat_dec_eq(v_idx_1407_, v_idx_1410_);
if (v___x_1413_ == 0)
{
goto v___jp_1243_;
}
else
{
if (v___x_1271_ == 0)
{
lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1432_; 
lean_inc_ref(v_struct_1411_);
lean_inc_ref(v_struct_1408_);
lean_inc(v_pos_1262_);
lean_inc(v_pos_1260_);
v_isSharedCheck_1432_ = !lean_is_exclusive(v_before_1236_);
if (v_isSharedCheck_1432_ == 0)
{
lean_object* v_unused_1433_; lean_object* v_unused_1434_; 
v_unused_1433_ = lean_ctor_get(v_before_1236_, 1);
lean_dec(v_unused_1433_);
v_unused_1434_ = lean_ctor_get(v_before_1236_, 0);
lean_dec(v_unused_1434_);
v___x_1415_ = v_before_1236_;
v_isShared_1416_ = v_isSharedCheck_1432_;
goto v_resetjp_1414_;
}
else
{
lean_dec(v_before_1236_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1432_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1429_; 
v_isSharedCheck_1429_ = !lean_is_exclusive(v_after_1237_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; lean_object* v_unused_1431_; 
v_unused_1430_ = lean_ctor_get(v_after_1237_, 1);
lean_dec(v_unused_1430_);
v_unused_1431_ = lean_ctor_get(v_after_1237_, 0);
lean_dec(v_unused_1431_);
v___x_1418_ = v_after_1237_;
v_isShared_1419_ = v_isSharedCheck_1429_;
goto v_resetjp_1417_;
}
else
{
lean_dec(v_after_1237_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1429_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1420_ = l_Lean_SubExpr_Pos_pushProj(v_pos_1260_);
lean_dec(v_pos_1260_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 1, v___x_1420_);
lean_ctor_set(v___x_1418_, 0, v_struct_1408_);
v___x_1422_ = v___x_1418_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_struct_1408_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v___x_1420_);
v___x_1422_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
lean_object* v___x_1423_; lean_object* v___x_1425_; 
v___x_1423_ = l_Lean_SubExpr_Pos_pushProj(v_pos_1262_);
lean_dec(v_pos_1262_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 1, v___x_1423_);
lean_ctor_set(v___x_1415_, 0, v_struct_1411_);
v___x_1425_ = v___x_1415_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_struct_1411_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v___x_1423_);
v___x_1425_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
v_before_1236_ = v___x_1422_;
v_after_1237_ = v___x_1425_;
goto _start;
}
}
}
}
}
else
{
goto v___jp_1243_;
}
}
}
else
{
goto v___jp_1243_;
}
}
}
default: 
{
goto v___jp_1255_;
}
}
}
default: 
{
if (lean_obj_tag(v_expr_1261_) == 10)
{
lean_object* v_expr_1435_; 
lean_inc_ref(v_expr_1261_);
lean_inc(v_pos_1262_);
lean_dec_ref(v_after_1237_);
v_expr_1435_ = lean_ctor_get(v_expr_1261_, 1);
lean_inc_ref(v_expr_1435_);
lean_dec_ref_known(v_expr_1261_, 2);
v_e_u2081_1264_ = v_expr_1435_;
v___y_1265_ = v_a_1238_;
v___y_1266_ = v_a_1239_;
v___y_1267_ = v_a_1240_;
v___y_1268_ = v_a_1241_;
goto v___jp_1263_;
}
else
{
goto v___jp_1255_;
}
}
}
}
else
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
lean_dec_ref(v_after_1237_);
lean_dec_ref(v_before_1236_);
v___x_1436_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___x_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1436_);
return v___x_1437_;
}
v___jp_1243_:
{
uint8_t v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1244_ = 0;
v___x_1245_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1236_, v_after_1237_, v___x_1244_);
v___x_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
return v___x_1246_;
}
v___jp_1247_:
{
uint8_t v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1248_ = 0;
v___x_1249_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1236_, v_after_1237_, v___x_1248_);
v___x_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
return v___x_1250_;
}
v___jp_1251_:
{
uint8_t v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1252_ = 0;
v___x_1253_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1236_, v_after_1237_, v___x_1252_);
v___x_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
return v___x_1254_;
}
v___jp_1255_:
{
uint8_t v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1256_ = 0;
v___x_1257_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1236_, v_after_1237_, v___x_1256_);
v___x_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
return v___x_1258_;
}
v___jp_1263_:
{
lean_object* v___x_1269_; 
v___x_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1269_, 0, v_e_u2081_1264_);
lean_ctor_set(v___x_1269_, 1, v_pos_1262_);
v_after_1237_ = v___x_1269_;
v_a_1238_ = v___y_1265_;
v_a_1239_ = v___y_1266_;
v_a_1240_ = v___y_1267_;
v_a_1241_ = v___y_1268_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_before_1236_ = stack[0].m_obj;
lean_object* v_after_1237_ = stack[1].m_obj;
lean_object* v_a_1238_ = stack[2].m_obj;
lean_object* v_a_1239_ = stack[3].m_obj;
lean_object* v_a_1240_ = stack[4].m_obj;
lean_object* v_a_1241_ = stack[5].m_obj;
lean_object* v_res_1438_;
v_res_1438_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v_before_1236_, v_after_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
stack->m_obj
 = v_res_1438_;
}
lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0(lean_object* v_body_1439_, lean_object* v_pos_1440_, lean_object* v_body_1441_, lean_object* v_pos_1442_, lean_object* v_x_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1449_ = lean_expr_instantiate1(v_body_1439_, v_x_1443_);
v___x_1450_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1440_);
v___x_1451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1449_);
lean_ctor_set(v___x_1451_, 1, v___x_1450_);
v___x_1452_ = lean_expr_instantiate1(v_body_1441_, v_x_1443_);
v___x_1453_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1442_);
v___x_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1452_);
lean_ctor_set(v___x_1454_, 1, v___x_1453_);
v___x_1455_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1451_, v___x_1454_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
return v___x_1455_;
}
}
LEAN_EXPORT void l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_body_1439_ = stack[0].m_obj;
lean_object* v_pos_1440_ = stack[1].m_obj;
lean_object* v_body_1441_ = stack[2].m_obj;
lean_object* v_pos_1442_ = stack[3].m_obj;
lean_object* v_x_1443_ = stack[4].m_obj;
lean_object* v___y_1444_ = stack[5].m_obj;
lean_object* v___y_1445_ = stack[6].m_obj;
lean_object* v___y_1446_ = stack[7].m_obj;
lean_object* v___y_1447_ = stack[8].m_obj;
lean_object* v_res_1456_;
v_res_1456_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0(v_body_1439_, v_pos_1440_, v_body_1441_, v_pos_1442_, v_x_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
stack->m_obj
 = v_res_1456_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg___boxed(lean_object* v_snd_1457_, lean_object* v_before_1458_, lean_object* v_after_1459_, lean_object* v_sz_1460_, lean_object* v_i_1461_, lean_object* v_bs_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
size_t v_sz_boxed_1468_; size_t v_i_boxed_1469_; lean_object* v_res_1470_; 
v_sz_boxed_1468_ = lean_unbox_usize(v_sz_1460_);
lean_dec(v_sz_1460_);
v_i_boxed_1469_ = lean_unbox_usize(v_i_1461_);
lean_dec(v_i_1461_);
v_res_1470_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_1457_, v_before_1458_, v_after_1459_, v_sz_boxed_1468_, v_i_boxed_1469_, v_bs_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec_ref(v_after_1459_);
lean_dec_ref(v_before_1458_);
lean_dec_ref(v_snd_1457_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___boxed(lean_object* v_before_1471_, lean_object* v_after_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(v_before_1471_, v_after_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_);
lean_dec(v_a_1476_);
lean_dec_ref(v_a_1475_);
lean_dec(v_a_1474_);
lean_dec_ref(v_a_1473_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___boxed(lean_object* v_before_1479_, lean_object* v_after_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v_before_1479_, v_after_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
lean_dec(v_a_1482_);
lean_dec_ref(v_a_1481_);
return v_res_1486_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1(lean_object* v_upperBound_1487_, lean_object* v_before_1488_, lean_object* v_inst_1489_, lean_object* v_R_1490_, lean_object* v_a_1491_, lean_object* v_b_1492_, lean_object* v_c_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v_upperBound_1487_, v_before_1488_, v_a_1491_, v_b_1492_);
return v___x_1499_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1487_ = stack[0].m_obj;
lean_object* v_before_1488_ = stack[1].m_obj;
lean_object* v_a_1491_ = stack[4].m_obj;
lean_object* v_b_1492_ = stack[5].m_obj;
lean_object* v___y_1494_ = stack[7].m_obj;
lean_object* v___y_1495_ = stack[8].m_obj;
lean_object* v___y_1496_ = stack[9].m_obj;
lean_object* v___y_1497_ = stack[10].m_obj;
lean_object* v_res_1500_;
v_res_1500_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1(v_upperBound_1487_, v_before_1488_, lean_box(0), lean_box(0), v_a_1491_, v_b_1492_, lean_box(0), v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
stack->m_obj
 = v_res_1500_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___boxed(lean_object* v_upperBound_1501_, lean_object* v_before_1502_, lean_object* v_inst_1503_, lean_object* v_R_1504_, lean_object* v_a_1505_, lean_object* v_b_1506_, lean_object* v_c_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1(v_upperBound_1501_, v_before_1502_, v_inst_1503_, v_R_1504_, v_a_1505_, v_b_1506_, v_c_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v_upperBound_1501_);
return v_res_1513_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3(lean_object* v_00_u03b1_1514_, lean_object* v_msg_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v_msg_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1515_ = stack[1].m_obj;
lean_object* v___y_1516_ = stack[2].m_obj;
lean_object* v___y_1517_ = stack[3].m_obj;
lean_object* v___y_1518_ = stack[4].m_obj;
lean_object* v___y_1519_ = stack[5].m_obj;
lean_object* v_res_1522_;
v_res_1522_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3(lean_box(0), v_msg_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
stack->m_obj
 = v_res_1522_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___boxed(lean_object* v_00_u03b1_1523_, lean_object* v_msg_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3(v_00_u03b1_1523_, v_msg_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
return v_res_1530_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4(uint8_t v_b_u2082_1531_, lean_object* v_k_1532_, lean_object* v_t_1533_, lean_object* v_hl_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_1531_, v_k_1532_, v_t_1533_);
return v___x_1535_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_u2082_1531_ = stack[0].m_num;
lean_object* v_k_1532_ = stack[1].m_obj;
lean_object* v_t_1533_ = stack[2].m_obj;
lean_object* v_res_1536_;
v_res_1536_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4(v_b_u2082_1531_, v_k_1532_, v_t_1533_, lean_box(0));
stack->m_obj
 = v_res_1536_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___boxed(lean_object* v_b_u2082_1537_, lean_object* v_k_1538_, lean_object* v_t_1539_, lean_object* v_hl_1540_){
_start:
{
uint8_t v_b_u2082_boxed_1541_; lean_object* v_res_1542_; 
v_b_u2082_boxed_1541_ = lean_unbox(v_b_u2082_1537_);
v_res_1542_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4(v_b_u2082_boxed_1541_, v_k_1538_, v_t_1539_, v_hl_1540_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5(lean_object* v_init_1543_, lean_object* v_t_1544_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_init_1543_, v_t_1544_);
return v___x_1545_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9(lean_object* v_snd_1546_, lean_object* v_before_1547_, lean_object* v_after_1548_, lean_object* v_as_1549_, size_t v_sz_1550_, size_t v_i_1551_, lean_object* v_bs_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_1546_, v_before_1547_, v_after_1548_, v_sz_1550_, v_i_1551_, v_bs_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
return v___x_1558_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_1546_ = stack[0].m_obj;
lean_object* v_before_1547_ = stack[1].m_obj;
lean_object* v_after_1548_ = stack[2].m_obj;
lean_object* v_as_1549_ = stack[3].m_obj;
size_t v_sz_1550_ = stack[4].m_num;
size_t v_i_1551_ = stack[5].m_num;
lean_object* v_bs_1552_ = stack[6].m_obj;
lean_object* v___y_1553_ = stack[7].m_obj;
lean_object* v___y_1554_ = stack[8].m_obj;
lean_object* v___y_1555_ = stack[9].m_obj;
lean_object* v___y_1556_ = stack[10].m_obj;
lean_object* v_res_1559_;
v_res_1559_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9(v_snd_1546_, v_before_1547_, v_after_1548_, v_as_1549_, v_sz_1550_, v_i_1551_, v_bs_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
stack->m_obj
 = v_res_1559_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___boxed(lean_object* v_snd_1560_, lean_object* v_before_1561_, lean_object* v_after_1562_, lean_object* v_as_1563_, lean_object* v_sz_1564_, lean_object* v_i_1565_, lean_object* v_bs_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
size_t v_sz_boxed_1572_; size_t v_i_boxed_1573_; lean_object* v_res_1574_; 
v_sz_boxed_1572_ = lean_unbox_usize(v_sz_1564_);
lean_dec(v_sz_1564_);
v_i_boxed_1573_ = lean_unbox_usize(v_i_1565_);
lean_dec(v_i_1565_);
v_res_1574_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9(v_snd_1560_, v_before_1561_, v_after_1562_, v_as_1563_, v_sz_boxed_1572_, v_i_boxed_1573_, v_bs_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec_ref(v_as_1563_);
lean_dec_ref(v_after_1562_);
lean_dec_ref(v_before_1561_);
lean_dec_ref(v_snd_1560_);
return v_res_1574_;
}
}
lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(lean_object* v_e_u2080_1575_, lean_object* v_e_u2081_1576_, uint8_t v_useAfter_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v___x_1583_; lean_object* v_s_u2080_1584_; lean_object* v_s_u2081_1585_; 
v___x_1583_ = l_Lean_SubExpr_Pos_root;
v_s_u2080_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_u2080_1584_, 0, v_e_u2080_1575_);
lean_ctor_set(v_s_u2080_1584_, 1, v___x_1583_);
v_s_u2081_1585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_u2081_1585_, 0, v_e_u2081_1576_);
lean_ctor_set(v_s_u2081_1585_, 1, v___x_1583_);
if (v_useAfter_1577_ == 0)
{
lean_object* v___x_1586_; 
v___x_1586_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v_s_u2081_1585_, v_s_u2080_1584_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
return v___x_1586_;
}
else
{
lean_object* v___x_1587_; 
v___x_1587_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v_s_u2080_1584_, v_s_u2081_1585_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
return v___x_1587_;
}
}
}
LEAN_EXPORT void l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_u2080_1575_ = stack[0].m_obj;
lean_object* v_e_u2081_1576_ = stack[1].m_obj;
uint8_t v_useAfter_1577_ = stack[2].m_num;
lean_object* v_a_1578_ = stack[3].m_obj;
lean_object* v_a_1579_ = stack[4].m_obj;
lean_object* v_a_1580_ = stack[5].m_obj;
lean_object* v_a_1581_ = stack[6].m_obj;
lean_object* v_res_1588_;
v_res_1588_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(v_e_u2080_1575_, v_e_u2081_1576_, v_useAfter_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
stack->m_obj
 = v_res_1588_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff___boxed(lean_object* v_e_u2080_1589_, lean_object* v_e_u2081_1590_, lean_object* v_useAfter_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_){
_start:
{
uint8_t v_useAfter_boxed_1597_; lean_object* v_res_1598_; 
v_useAfter_boxed_1597_ = lean_unbox(v_useAfter_1591_);
v_res_1598_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(v_e_u2080_1589_, v_e_u2081_1590_, v_useAfter_boxed_1597_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_);
lean_dec(v_a_1595_);
lean_dec_ref(v_a_1594_);
lean_dec(v_a_1593_);
lean_dec_ref(v_a_1592_);
return v_res_1598_;
}
}
lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0(uint8_t v_useAfter_1599_, lean_object* v_info_1600_, uint8_t v_d_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
uint8_t v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1607_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag(v_useAfter_1599_, v_d_1601_);
v___x_1608_ = l_Lean_Widget_SubexprInfo_withDiffTag(v___x_1607_, v_info_1600_);
v___x_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT void l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_useAfter_1599_ = stack[0].m_num;
lean_object* v_info_1600_ = stack[1].m_obj;
uint8_t v_d_1601_ = stack[2].m_num;
lean_object* v___y_1602_ = stack[3].m_obj;
lean_object* v___y_1603_ = stack[4].m_obj;
lean_object* v___y_1604_ = stack[5].m_obj;
lean_object* v___y_1605_ = stack[6].m_obj;
lean_object* v_res_1610_;
v_res_1610_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0(v_useAfter_1599_, v_info_1600_, v_d_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
stack->m_obj
 = v_res_1610_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0___boxed(lean_object* v_useAfter_1611_, lean_object* v_info_1612_, lean_object* v_d_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
uint8_t v_useAfter_boxed_1619_; uint8_t v_d_boxed_1620_; lean_object* v_res_1621_; 
v_useAfter_boxed_1619_ = lean_unbox(v_useAfter_1611_);
v_d_boxed_1620_ = lean_unbox(v_d_1613_);
v_res_1621_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0(v_useAfter_boxed_1619_, v_info_1612_, v_d_boxed_1620_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
return v_res_1621_;
}
}
lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(lean_object* v_f_1622_, lean_object* v_x_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
switch(lean_obj_tag(v_x_1623_))
{
case 0:
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1637_; 
lean_dec_ref(v_f_1622_);
v_a_1629_ = lean_ctor_get(v_x_1623_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v_x_1623_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1631_ = v_x_1623_;
v_isShared_1632_ = v_isSharedCheck_1637_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v_x_1623_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1637_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1635_; 
v___x_1635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1634_);
return v___x_1635_;
}
}
}
case 1:
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1664_; 
v_a_1638_ = lean_ctor_get(v_x_1623_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_x_1623_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1640_ = v_x_1623_;
v_isShared_1641_ = v_isSharedCheck_1664_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v_x_1623_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1664_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
size_t v_sz_1642_; size_t v___x_1643_; lean_object* v___x_1644_; 
v_sz_1642_ = lean_array_size(v_a_1638_);
v___x_1643_ = ((size_t)0ULL);
v___x_1644_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_1622_, v_sz_1642_, v___x_1643_, v_a_1638_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1655_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1647_ = v___x_1644_;
v_isShared_1648_ = v_isSharedCheck_1655_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1644_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1655_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v_a_1645_);
v___x_1650_ = v___x_1640_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
lean_object* v___x_1652_; 
if (v_isShared_1648_ == 0)
{
lean_ctor_set(v___x_1647_, 0, v___x_1650_);
v___x_1652_ = v___x_1647_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1650_);
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
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_del_object(v___x_1640_);
v_a_1656_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1644_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1644_);
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
default: 
{
lean_object* v_a_1665_; lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1692_; 
v_a_1665_ = lean_ctor_get(v_x_1623_, 0);
v_a_1666_ = lean_ctor_get(v_x_1623_, 1);
v_isSharedCheck_1692_ = !lean_is_exclusive(v_x_1623_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1668_ = v_x_1623_;
v_isShared_1669_ = v_isSharedCheck_1692_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_inc(v_a_1665_);
lean_dec(v_x_1623_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1692_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1670_; 
lean_inc_ref(v_f_1622_);
lean_inc(v___y_1627_);
lean_inc_ref(v___y_1626_);
lean_inc(v___y_1625_);
lean_inc_ref(v___y_1624_);
v___x_1670_ = lean_apply_6(v_f_1622_, v_a_1665_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, lean_box(0));
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1672_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1671_);
lean_dec_ref_known(v___x_1670_, 1);
v___x_1672_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1622_, v_a_1666_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1683_; 
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1675_ = v___x_1672_;
v_isShared_1676_ = v_isSharedCheck_1683_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1672_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1683_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 1, v_a_1673_);
lean_ctor_set(v___x_1668_, 0, v_a_1671_);
v___x_1678_ = v___x_1668_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1671_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
lean_object* v___x_1680_; 
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 0, v___x_1678_);
v___x_1680_ = v___x_1675_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
else
{
lean_dec(v_a_1671_);
lean_del_object(v___x_1668_);
return v___x_1672_;
}
}
else
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1691_; 
lean_del_object(v___x_1668_);
lean_dec_ref(v_a_1666_);
lean_dec_ref(v_f_1622_);
v_a_1684_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1686_ = v___x_1670_;
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1670_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1689_; 
if (v_isShared_1687_ == 0)
{
v___x_1689_ = v___x_1686_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_a_1684_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1622_ = stack[0].m_obj;
lean_object* v_x_1623_ = stack[1].m_obj;
lean_object* v___y_1624_ = stack[2].m_obj;
lean_object* v___y_1625_ = stack[3].m_obj;
lean_object* v___y_1626_ = stack[4].m_obj;
lean_object* v___y_1627_ = stack[5].m_obj;
lean_object* v_res_1693_;
v_res_1693_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1622_, v_x_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
stack->m_obj
 = v_res_1693_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(lean_object* v_f_1694_, size_t v_sz_1695_, size_t v_i_1696_, lean_object* v_bs_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
uint8_t v___x_1703_; 
v___x_1703_ = lean_usize_dec_lt(v_i_1696_, v_sz_1695_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; 
lean_dec_ref(v_f_1694_);
v___x_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1704_, 0, v_bs_1697_);
return v___x_1704_;
}
else
{
lean_object* v_v_1705_; lean_object* v___x_1706_; lean_object* v_bs_x27_1707_; lean_object* v___x_1708_; 
v_v_1705_ = lean_array_uget(v_bs_1697_, v_i_1696_);
v___x_1706_ = lean_unsigned_to_nat(0u);
v_bs_x27_1707_ = lean_array_uset(v_bs_1697_, v_i_1696_, v___x_1706_);
lean_inc_ref(v_f_1694_);
v___x_1708_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1694_, v_v_1705_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; size_t v___x_1710_; size_t v___x_1711_; lean_object* v___x_1712_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_a_1709_);
lean_dec_ref_known(v___x_1708_, 1);
v___x_1710_ = ((size_t)1ULL);
v___x_1711_ = lean_usize_add(v_i_1696_, v___x_1710_);
v___x_1712_ = lean_array_uset(v_bs_x27_1707_, v_i_1696_, v_a_1709_);
v_i_1696_ = v___x_1711_;
v_bs_1697_ = v___x_1712_;
goto _start;
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_dec_ref(v_bs_x27_1707_);
lean_dec_ref(v_f_1694_);
v_a_1714_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1708_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1708_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1694_ = stack[0].m_obj;
size_t v_sz_1695_ = stack[1].m_num;
size_t v_i_1696_ = stack[2].m_num;
lean_object* v_bs_1697_ = stack[3].m_obj;
lean_object* v___y_1698_ = stack[4].m_obj;
lean_object* v___y_1699_ = stack[5].m_obj;
lean_object* v___y_1700_ = stack[6].m_obj;
lean_object* v___y_1701_ = stack[7].m_obj;
lean_object* v_res_1722_;
v_res_1722_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_1694_, v_sz_1695_, v_i_1696_, v_bs_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
stack->m_obj
 = v_res_1722_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_1723_, lean_object* v_sz_1724_, lean_object* v_i_1725_, lean_object* v_bs_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
size_t v_sz_boxed_1732_; size_t v_i_boxed_1733_; lean_object* v_res_1734_; 
v_sz_boxed_1732_ = lean_unbox_usize(v_sz_1724_);
lean_dec(v_sz_1724_);
v_i_boxed_1733_ = lean_unbox_usize(v_i_1725_);
lean_dec(v_i_1725_);
v_res_1734_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_1723_, v_sz_boxed_1732_, v_i_boxed_1733_, v_bs_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg___boxed(lean_object* v_f_1735_, lean_object* v_x_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1735_, v_x_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(lean_object* v_t_1743_, lean_object* v_k_1744_){
_start:
{
if (lean_obj_tag(v_t_1743_) == 0)
{
lean_object* v_k_1745_; lean_object* v_v_1746_; lean_object* v_l_1747_; lean_object* v_r_1748_; uint8_t v___x_1749_; 
v_k_1745_ = lean_ctor_get(v_t_1743_, 1);
v_v_1746_ = lean_ctor_get(v_t_1743_, 2);
v_l_1747_ = lean_ctor_get(v_t_1743_, 3);
v_r_1748_ = lean_ctor_get(v_t_1743_, 4);
v___x_1749_ = lean_nat_dec_lt(v_k_1744_, v_k_1745_);
if (v___x_1749_ == 0)
{
uint8_t v___x_1750_; 
v___x_1750_ = lean_nat_dec_eq(v_k_1744_, v_k_1745_);
if (v___x_1750_ == 0)
{
v_t_1743_ = v_r_1748_;
goto _start;
}
else
{
lean_object* v___x_1752_; 
lean_inc(v_v_1746_);
v___x_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1752_, 0, v_v_1746_);
return v___x_1752_;
}
}
else
{
v_t_1743_ = v_l_1747_;
goto _start;
}
}
else
{
lean_object* v___x_1754_; 
v___x_1754_ = lean_box(0);
return v___x_1754_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg___boxed(lean_object* v_t_1755_, lean_object* v_k_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_t_1755_, v_k_1756_);
lean_dec(v_k_1756_);
lean_dec(v_t_1755_);
return v_res_1757_;
}
}
lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0(lean_object* v_pm_1758_, lean_object* v_merger_1759_, lean_object* v_info_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v_subexprPos_1766_; lean_object* v___x_1767_; 
v_subexprPos_1766_ = lean_ctor_get(v_info_1760_, 1);
v___x_1767_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_pm_1758_, v_subexprPos_1766_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v___x_1768_; 
lean_dec_ref(v_merger_1759_);
v___x_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1768_, 0, v_info_1760_);
return v___x_1768_;
}
else
{
lean_object* v_val_1769_; lean_object* v___x_1770_; 
v_val_1769_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_val_1769_);
lean_dec_ref_known(v___x_1767_, 1);
lean_inc(v___y_1764_);
lean_inc_ref(v___y_1763_);
lean_inc(v___y_1762_);
lean_inc_ref(v___y_1761_);
v___x_1770_ = lean_apply_7(v_merger_1759_, v_info_1760_, v_val_1769_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, lean_box(0));
return v___x_1770_;
}
}
}
LEAN_EXPORT void l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pm_1758_ = stack[0].m_obj;
lean_object* v_merger_1759_ = stack[1].m_obj;
lean_object* v_info_1760_ = stack[2].m_obj;
lean_object* v___y_1761_ = stack[3].m_obj;
lean_object* v___y_1762_ = stack[4].m_obj;
lean_object* v___y_1763_ = stack[5].m_obj;
lean_object* v___y_1764_ = stack[6].m_obj;
lean_object* v_res_1771_;
v_res_1771_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0(v_pm_1758_, v_merger_1759_, v_info_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
stack->m_obj
 = v_res_1771_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0___boxed(lean_object* v_pm_1772_, lean_object* v_merger_1773_, lean_object* v_info_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0(v_pm_1772_, v_merger_1773_, v_info_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec(v_pm_1772_);
return v_res_1780_;
}
}
lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(lean_object* v_merger_1781_, lean_object* v_pm_1782_, lean_object* v_tt_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
if (lean_obj_tag(v_pm_1782_) == 0)
{
lean_object* v___f_1789_; lean_object* v___x_1790_; 
v___f_1789_ = lean_alloc_closure((void*)(l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1789_, 0, v_pm_1782_);
lean_closure_set(v___f_1789_, 1, v_merger_1781_);
v___x_1790_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v___f_1789_, v_tt_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
return v___x_1790_;
}
else
{
lean_object* v___x_1791_; 
lean_dec_ref(v_merger_1781_);
v___x_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1791_, 0, v_tt_1783_);
return v___x_1791_;
}
}
}
LEAN_EXPORT void l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_merger_1781_ = stack[0].m_obj;
lean_object* v_pm_1782_ = stack[1].m_obj;
lean_object* v_tt_1783_ = stack[2].m_obj;
lean_object* v___y_1784_ = stack[3].m_obj;
lean_object* v___y_1785_ = stack[4].m_obj;
lean_object* v___y_1786_ = stack[5].m_obj;
lean_object* v___y_1787_ = stack[6].m_obj;
lean_object* v_res_1792_;
v_res_1792_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v_merger_1781_, v_pm_1782_, v_tt_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
stack->m_obj
 = v_res_1792_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___boxed(lean_object* v_merger_1793_, lean_object* v_pm_1794_, lean_object* v_tt_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v_merger_1793_, v_pm_1794_, v_tt_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
return v_res_1801_;
}
}
lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(uint8_t v_useAfter_1802_, lean_object* v_diff_1803_, lean_object* v_info_u2081_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_){
_start:
{
lean_object* v___x_1810_; lean_object* v___f_1811_; 
v___x_1810_ = lean_box(v_useAfter_1802_);
v___f_1811_ = lean_alloc_closure((void*)(l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1811_, 0, v___x_1810_);
if (v_useAfter_1802_ == 0)
{
lean_object* v_changesBefore_1812_; lean_object* v___x_1813_; 
v_changesBefore_1812_ = lean_ctor_get(v_diff_1803_, 0);
lean_inc(v_changesBefore_1812_);
lean_dec_ref(v_diff_1803_);
v___x_1813_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v___f_1811_, v_changesBefore_1812_, v_info_u2081_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
return v___x_1813_;
}
else
{
lean_object* v_changesAfter_1814_; lean_object* v___x_1815_; 
v_changesAfter_1814_ = lean_ctor_get(v_diff_1803_, 1);
lean_inc(v_changesAfter_1814_);
lean_dec_ref(v_diff_1803_);
v___x_1815_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v___f_1811_, v_changesAfter_1814_, v_info_u2081_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
return v___x_1815_;
}
}
}
LEAN_EXPORT void l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_0interp(lean_interpreter_value* stack)
{
uint8_t v_useAfter_1802_ = stack[0].m_num;
lean_object* v_diff_1803_ = stack[1].m_obj;
lean_object* v_info_u2081_1804_ = stack[2].m_obj;
lean_object* v_a_1805_ = stack[3].m_obj;
lean_object* v_a_1806_ = stack[4].m_obj;
lean_object* v_a_1807_ = stack[5].m_obj;
lean_object* v_a_1808_ = stack[6].m_obj;
lean_object* v_res_1816_;
v_res_1816_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(v_useAfter_1802_, v_diff_1803_, v_info_u2081_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
stack->m_obj
 = v_res_1816_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___boxed(lean_object* v_useAfter_1817_, lean_object* v_diff_1818_, lean_object* v_info_u2081_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_){
_start:
{
uint8_t v_useAfter_boxed_1825_; lean_object* v_res_1826_; 
v_useAfter_boxed_1825_ = lean_unbox(v_useAfter_1817_);
v_res_1826_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(v_useAfter_boxed_1825_, v_diff_1818_, v_info_u2081_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
lean_dec(v_a_1823_);
lean_dec_ref(v_a_1822_);
lean_dec(v_a_1821_);
lean_dec_ref(v_a_1820_);
return v_res_1826_;
}
}
lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0(lean_object* v_00_u03b1_1827_, lean_object* v_merger_1828_, lean_object* v_pm_1829_, lean_object* v_tt_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v_merger_1828_, v_pm_1829_, v_tt_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
return v___x_1836_;
}
}
LEAN_EXPORT void l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_merger_1828_ = stack[1].m_obj;
lean_object* v_pm_1829_ = stack[2].m_obj;
lean_object* v_tt_1830_ = stack[3].m_obj;
lean_object* v___y_1831_ = stack[4].m_obj;
lean_object* v___y_1832_ = stack[5].m_obj;
lean_object* v___y_1833_ = stack[6].m_obj;
lean_object* v___y_1834_ = stack[7].m_obj;
lean_object* v_res_1837_;
v_res_1837_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0(lean_box(0), v_merger_1828_, v_pm_1829_, v_tt_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
stack->m_obj
 = v_res_1837_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___boxed(lean_object* v_00_u03b1_1838_, lean_object* v_merger_1839_, lean_object* v_pm_1840_, lean_object* v_tt_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0(v_00_u03b1_1838_, v_merger_1839_, v_pm_1840_, v_tt_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0(lean_object* v_00_u03b4_1848_, lean_object* v_t_1849_, lean_object* v_k_1850_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_t_1849_, v_k_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___boxed(lean_object* v_00_u03b4_1852_, lean_object* v_t_1853_, lean_object* v_k_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0(v_00_u03b4_1852_, v_t_1853_, v_k_1854_);
lean_dec(v_k_1854_);
lean_dec(v_t_1853_);
return v_res_1855_;
}
}
lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1(lean_object* v_00_u03b1_1856_, lean_object* v_00_u03b2_1857_, lean_object* v_f_1858_, lean_object* v_x_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1858_, v_x_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
return v___x_1865_;
}
}
LEAN_EXPORT void l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1858_ = stack[2].m_obj;
lean_object* v_x_1859_ = stack[3].m_obj;
lean_object* v___y_1860_ = stack[4].m_obj;
lean_object* v___y_1861_ = stack[5].m_obj;
lean_object* v___y_1862_ = stack[6].m_obj;
lean_object* v___y_1863_ = stack[7].m_obj;
lean_object* v_res_1866_;
v_res_1866_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1(lean_box(0), lean_box(0), v_f_1858_, v_x_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
stack->m_obj
 = v_res_1866_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1867_, lean_object* v_00_u03b2_1868_, lean_object* v_f_1869_, lean_object* v_x_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1(v_00_u03b1_1867_, v_00_u03b2_1868_, v_f_1869_, v_x_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
return v_res_1876_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1877_, lean_object* v_00_u03b2_1878_, lean_object* v_f_1879_, size_t v_sz_1880_, size_t v_i_1881_, lean_object* v_bs_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_1879_, v_sz_1880_, v_i_1881_, v_bs_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
return v___x_1888_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1879_ = stack[2].m_obj;
size_t v_sz_1880_ = stack[3].m_num;
size_t v_i_1881_ = stack[4].m_num;
lean_object* v_bs_1882_ = stack[5].m_obj;
lean_object* v___y_1883_ = stack[6].m_obj;
lean_object* v___y_1884_ = stack[7].m_obj;
lean_object* v___y_1885_ = stack[8].m_obj;
lean_object* v___y_1886_ = stack[9].m_obj;
lean_object* v_res_1889_;
v_res_1889_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2(lean_box(0), lean_box(0), v_f_1879_, v_sz_1880_, v_i_1881_, v_bs_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
stack->m_obj
 = v_res_1889_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1890_, lean_object* v_00_u03b2_1891_, lean_object* v_f_1892_, lean_object* v_sz_1893_, lean_object* v_i_1894_, lean_object* v_bs_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
size_t v_sz_boxed_1901_; size_t v_i_boxed_1902_; lean_object* v_res_1903_; 
v_sz_boxed_1901_ = lean_unbox_usize(v_sz_1893_);
lean_dec(v_sz_1893_);
v_i_boxed_1902_ = lean_unbox_usize(v_i_1894_);
lean_dec(v_i_1894_);
v_res_1903_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2(v_00_u03b1_1890_, v_00_u03b2_1891_, v_f_1892_, v_sz_boxed_1901_, v_i_boxed_1902_, v_bs_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
return v_res_1903_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(lean_object* v_e_1904_, lean_object* v___y_1905_){
_start:
{
uint8_t v___x_1907_; 
v___x_1907_ = l_Lean_Expr_hasMVar(v_e_1904_);
if (v___x_1907_ == 0)
{
lean_object* v___x_1908_; 
v___x_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1908_, 0, v_e_1904_);
return v___x_1908_;
}
else
{
lean_object* v___x_1909_; lean_object* v_mctx_1910_; lean_object* v___x_1911_; lean_object* v_fst_1912_; lean_object* v_snd_1913_; lean_object* v___x_1914_; lean_object* v_cache_1915_; lean_object* v_zetaDeltaFVarIds_1916_; lean_object* v_postponed_1917_; lean_object* v_diag_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1927_; 
v___x_1909_ = lean_st_ref_get(v___y_1905_);
v_mctx_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc_ref(v_mctx_1910_);
lean_dec(v___x_1909_);
v___x_1911_ = l_Lean_instantiateMVarsCore(v_mctx_1910_, v_e_1904_);
v_fst_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_fst_1912_);
v_snd_1913_ = lean_ctor_get(v___x_1911_, 1);
lean_inc(v_snd_1913_);
lean_dec_ref(v___x_1911_);
v___x_1914_ = lean_st_ref_take(v___y_1905_);
v_cache_1915_ = lean_ctor_get(v___x_1914_, 1);
v_zetaDeltaFVarIds_1916_ = lean_ctor_get(v___x_1914_, 2);
v_postponed_1917_ = lean_ctor_get(v___x_1914_, 3);
v_diag_1918_ = lean_ctor_get(v___x_1914_, 4);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1927_ == 0)
{
lean_object* v_unused_1928_; 
v_unused_1928_ = lean_ctor_get(v___x_1914_, 0);
lean_dec(v_unused_1928_);
v___x_1920_ = v___x_1914_;
v_isShared_1921_ = v_isSharedCheck_1927_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_diag_1918_);
lean_inc(v_postponed_1917_);
lean_inc(v_zetaDeltaFVarIds_1916_);
lean_inc(v_cache_1915_);
lean_dec(v___x_1914_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1927_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v_snd_1913_);
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_snd_1913_);
lean_ctor_set(v_reuseFailAlloc_1926_, 1, v_cache_1915_);
lean_ctor_set(v_reuseFailAlloc_1926_, 2, v_zetaDeltaFVarIds_1916_);
lean_ctor_set(v_reuseFailAlloc_1926_, 3, v_postponed_1917_);
lean_ctor_set(v_reuseFailAlloc_1926_, 4, v_diag_1918_);
v___x_1923_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = lean_st_ref_put(v___y_1905_, v___x_1923_);
v___x_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1925_, 0, v_fst_1912_);
return v___x_1925_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1904_ = stack[0].m_obj;
lean_object* v___y_1905_ = stack[1].m_obj;
lean_object* v_res_1929_;
v_res_1929_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_e_1904_, v___y_1905_);
stack->m_obj
 = v_res_1929_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg___boxed(lean_object* v_e_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_e_1930_, v___y_1931_);
lean_dec(v___y_1931_);
return v_res_1933_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0(lean_object* v_e_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_e_1934_, v___y_1936_);
return v___x_1940_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1934_ = stack[0].m_obj;
lean_object* v___y_1935_ = stack[1].m_obj;
lean_object* v___y_1936_ = stack[2].m_obj;
lean_object* v___y_1937_ = stack[3].m_obj;
lean_object* v___y_1938_ = stack[4].m_obj;
lean_object* v_res_1941_;
v_res_1941_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0(v_e_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
stack->m_obj
 = v_res_1941_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___boxed(lean_object* v_e_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0(v_e_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
return v_res_1948_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1(void){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1950_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__0));
v___x_1951_ = l_Lean_stringToMessageData(v___x_1950_);
return v___x_1951_;
}
}
lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(uint8_t v_useAfter_1952_, lean_object* v_t_u2080_1953_, lean_object* v_h_u2081_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_){
_start:
{
lean_object* v_names_1960_; lean_object* v_fvarIds_1961_; lean_object* v_type_1962_; lean_object* v_val_x3f_1963_; lean_object* v_isInstance_x3f_1964_; lean_object* v_isType_x3f_1965_; lean_object* v_isInserted_x3f_1966_; lean_object* v_isRemoved_x3f_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_2022_; 
v_names_1960_ = lean_ctor_get(v_h_u2081_1954_, 0);
v_fvarIds_1961_ = lean_ctor_get(v_h_u2081_1954_, 1);
v_type_1962_ = lean_ctor_get(v_h_u2081_1954_, 2);
v_val_x3f_1963_ = lean_ctor_get(v_h_u2081_1954_, 3);
v_isInstance_x3f_1964_ = lean_ctor_get(v_h_u2081_1954_, 4);
v_isType_x3f_1965_ = lean_ctor_get(v_h_u2081_1954_, 5);
v_isInserted_x3f_1966_ = lean_ctor_get(v_h_u2081_1954_, 6);
v_isRemoved_x3f_1967_ = lean_ctor_get(v_h_u2081_1954_, 7);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_h_u2081_1954_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_1969_ = v_h_u2081_1954_;
v_isShared_1970_ = v_isSharedCheck_2022_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_isRemoved_x3f_1967_);
lean_inc(v_isInserted_x3f_1966_);
lean_inc(v_isType_x3f_1965_);
lean_inc(v_isInstance_x3f_1964_);
lean_inc(v_val_x3f_1963_);
lean_inc(v_type_1962_);
lean_inc(v_fvarIds_1961_);
lean_inc(v_names_1960_);
lean_dec(v_h_u2081_1954_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_2022_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___y_1972_; lean_object* v___x_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; 
v___x_2012_ = lean_unsigned_to_nat(0u);
v___x_2013_ = lean_array_get_size(v_fvarIds_1961_);
v___x_2014_ = lean_nat_dec_lt(v___x_2012_, v___x_2013_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
lean_del_object(v___x_1969_);
lean_dec(v_isRemoved_x3f_1967_);
lean_dec(v_isInserted_x3f_1966_);
lean_dec(v_isType_x3f_1965_);
lean_dec(v_isInstance_x3f_1964_);
lean_dec(v_val_x3f_1963_);
lean_dec_ref(v_type_1962_);
lean_dec_ref(v_fvarIds_1961_);
lean_dec_ref(v_names_1960_);
lean_dec_ref(v_t_u2080_1953_);
v___x_2015_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1);
v___x_2016_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_2015_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_);
return v___x_2016_;
}
else
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2017_ = lean_array_fget_borrowed(v_fvarIds_1961_, v___x_2012_);
lean_inc(v___x_2017_);
v___x_2018_ = l_Lean_Expr_fvar___override(v___x_2017_);
lean_inc(v_a_1958_);
lean_inc_ref(v_a_1957_);
lean_inc(v_a_1956_);
lean_inc_ref(v_a_1955_);
v___x_2019_ = lean_infer_type(v___x_2018_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2021_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2020_);
lean_dec_ref_known(v___x_2019_, 1);
v___x_2021_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_a_2020_, v_a_1956_);
v___y_1972_ = v___x_2021_;
goto v___jp_1971_;
}
else
{
v___y_1972_ = v___x_2019_;
goto v___jp_1971_;
}
}
v___jp_1971_:
{
if (lean_obj_tag(v___y_1972_) == 0)
{
lean_object* v_a_1973_; lean_object* v___x_1974_; 
v_a_1973_ = lean_ctor_get(v___y_1972_, 0);
lean_inc(v_a_1973_);
lean_dec_ref_known(v___y_1972_, 1);
v___x_1974_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(v_t_u2080_1953_, v_a_1973_, v_useAfter_1952_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; lean_object* v___x_1976_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_a_1975_);
lean_dec_ref_known(v___x_1974_, 1);
v___x_1976_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(v_useAfter_1952_, v_a_1975_, v_type_1962_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1987_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1979_ = v___x_1976_;
v_isShared_1980_ = v_isSharedCheck_1987_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1976_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1987_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 2, v_a_1977_);
v___x_1982_ = v___x_1969_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_names_1960_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v_fvarIds_1961_);
lean_ctor_set(v_reuseFailAlloc_1986_, 2, v_a_1977_);
lean_ctor_set(v_reuseFailAlloc_1986_, 3, v_val_x3f_1963_);
lean_ctor_set(v_reuseFailAlloc_1986_, 4, v_isInstance_x3f_1964_);
lean_ctor_set(v_reuseFailAlloc_1986_, 5, v_isType_x3f_1965_);
lean_ctor_set(v_reuseFailAlloc_1986_, 6, v_isInserted_x3f_1966_);
lean_ctor_set(v_reuseFailAlloc_1986_, 7, v_isRemoved_x3f_1967_);
v___x_1982_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_object* v___x_1984_; 
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 0, v___x_1982_);
v___x_1984_ = v___x_1979_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1982_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_del_object(v___x_1969_);
lean_dec(v_isRemoved_x3f_1967_);
lean_dec(v_isInserted_x3f_1966_);
lean_dec(v_isType_x3f_1965_);
lean_dec(v_isInstance_x3f_1964_);
lean_dec(v_val_x3f_1963_);
lean_dec_ref(v_fvarIds_1961_);
lean_dec_ref(v_names_1960_);
v_a_1988_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1976_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1976_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_del_object(v___x_1969_);
lean_dec(v_isRemoved_x3f_1967_);
lean_dec(v_isInserted_x3f_1966_);
lean_dec(v_isType_x3f_1965_);
lean_dec(v_isInstance_x3f_1964_);
lean_dec(v_val_x3f_1963_);
lean_dec_ref(v_type_1962_);
lean_dec_ref(v_fvarIds_1961_);
lean_dec_ref(v_names_1960_);
v_a_1996_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1974_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1974_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
else
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
lean_del_object(v___x_1969_);
lean_dec(v_isRemoved_x3f_1967_);
lean_dec(v_isInserted_x3f_1966_);
lean_dec(v_isType_x3f_1965_);
lean_dec(v_isInstance_x3f_1964_);
lean_dec(v_val_x3f_1963_);
lean_dec_ref(v_type_1962_);
lean_dec_ref(v_fvarIds_1961_);
lean_dec_ref(v_names_1960_);
lean_dec_ref(v_t_u2080_1953_);
v_a_2004_ = lean_ctor_get(v___y_1972_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___y_1972_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___y_1972_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___y_1972_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_0interp(lean_interpreter_value* stack)
{
uint8_t v_useAfter_1952_ = stack[0].m_num;
lean_object* v_t_u2080_1953_ = stack[1].m_obj;
lean_object* v_h_u2081_1954_ = stack[2].m_obj;
lean_object* v_a_1955_ = stack[3].m_obj;
lean_object* v_a_1956_ = stack[4].m_obj;
lean_object* v_a_1957_ = stack[5].m_obj;
lean_object* v_a_1958_ = stack[6].m_obj;
lean_object* v_res_2023_;
v_res_2023_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(v_useAfter_1952_, v_t_u2080_1953_, v_h_u2081_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_);
stack->m_obj
 = v_res_2023_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___boxed(lean_object* v_useAfter_2024_, lean_object* v_t_u2080_2025_, lean_object* v_h_u2081_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_){
_start:
{
uint8_t v_useAfter_boxed_2032_; lean_object* v_res_2033_; 
v_useAfter_boxed_2032_ = lean_unbox(v_useAfter_2024_);
v_res_2033_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(v_useAfter_boxed_2032_, v_t_u2080_2025_, v_h_u2081_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_);
lean_dec(v_a_2030_);
lean_dec_ref(v_a_2029_);
lean_dec(v_a_2028_);
lean_dec_ref(v_a_2027_);
return v_res_2033_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(lean_object* v_ctx_u2080_2037_, uint8_t v_useAfter_2038_, lean_object* v_h_u2081_2039_, lean_object* v___x_2040_, lean_object* v___x_2041_, lean_object* v_as_2042_, size_t v_sz_2043_, size_t v_i_2044_, lean_object* v_b_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
uint8_t v___x_2051_; 
v___x_2051_ = lean_usize_dec_lt(v_i_2044_, v_sz_2043_);
if (v___x_2051_ == 0)
{
lean_object* v___x_2052_; 
lean_dec_ref(v___x_2041_);
lean_dec_ref(v___x_2040_);
lean_dec_ref(v_h_u2081_2039_);
v___x_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2052_, 0, v_b_2045_);
return v___x_2052_;
}
else
{
lean_object* v_a_2053_; lean_object* v_fst_2054_; lean_object* v_snd_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2151_; 
lean_dec_ref(v_b_2045_);
v_a_2053_ = lean_array_uget(v_as_2042_, v_i_2044_);
v_fst_2054_ = lean_ctor_get(v_a_2053_, 0);
v_snd_2055_ = lean_ctor_get(v_a_2053_, 1);
v_isSharedCheck_2151_ = !lean_is_exclusive(v_a_2053_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2057_ = v_a_2053_;
v_isShared_2058_ = v_isSharedCheck_2151_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_snd_2055_);
lean_inc(v_fst_2054_);
lean_dec(v_a_2053_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2151_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2059_; uint8_t v___x_2060_; 
v___x_2059_ = lean_box(0);
v___x_2060_ = l_Lean_LocalContext_contains(v_ctx_u2080_2037_, v_snd_2055_);
lean_dec(v_snd_2055_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2061_ = lean_box(0);
v___x_2062_ = l_Lean_Name_str___override(v___x_2061_, v_fst_2054_);
v___x_2063_ = l_Lean_LocalContext_findFromUserName_x3f(v_ctx_u2080_2037_, v___x_2062_);
lean_dec(v___x_2062_);
if (lean_obj_tag(v___x_2063_) == 1)
{
lean_object* v_val_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2102_; 
lean_dec_ref(v___x_2041_);
lean_dec_ref(v___x_2040_);
v_val_2064_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2066_ = v___x_2063_;
v_isShared_2067_ = v_isSharedCheck_2102_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_val_2064_);
lean_dec(v___x_2063_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2102_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2068_ = l_Lean_LocalDecl_type(v_val_2064_);
lean_dec(v_val_2064_);
v___x_2069_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v___x_2068_, v___y_2047_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; lean_object* v___x_2071_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_a_2070_);
lean_dec_ref_known(v___x_2069_, 1);
v___x_2071_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(v_useAfter_2038_, v_a_2070_, v_h_u2081_2039_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2085_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2074_ = v___x_2071_;
v_isShared_2075_ = v_isSharedCheck_2085_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2071_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2085_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 0, v_a_2072_);
v___x_2077_ = v___x_2066_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
lean_object* v___x_2079_; 
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 1, v___x_2059_);
lean_ctor_set(v___x_2057_, 0, v___x_2077_);
v___x_2079_ = v___x_2057_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2077_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v___x_2059_);
v___x_2079_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2081_; 
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 0, v___x_2079_);
v___x_2081_ = v___x_2074_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2079_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
lean_del_object(v___x_2066_);
lean_del_object(v___x_2057_);
v_a_2086_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_2071_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2071_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
else
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2101_; 
lean_del_object(v___x_2066_);
lean_del_object(v___x_2057_);
lean_dec_ref(v_h_u2081_2039_);
v_a_2094_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2096_ = v___x_2069_;
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2069_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2097_ == 0)
{
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
}
else
{
lean_dec(v___x_2063_);
if (v_useAfter_2038_ == 0)
{
lean_object* v_type_2103_; lean_object* v_val_x3f_2104_; lean_object* v_isInstance_x3f_2105_; lean_object* v_isType_x3f_2106_; lean_object* v_isInserted_x3f_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2121_; 
v_type_2103_ = lean_ctor_get(v_h_u2081_2039_, 2);
v_val_x3f_2104_ = lean_ctor_get(v_h_u2081_2039_, 3);
v_isInstance_x3f_2105_ = lean_ctor_get(v_h_u2081_2039_, 4);
v_isType_x3f_2106_ = lean_ctor_get(v_h_u2081_2039_, 5);
v_isInserted_x3f_2107_ = lean_ctor_get(v_h_u2081_2039_, 6);
v_isSharedCheck_2121_ = !lean_is_exclusive(v_h_u2081_2039_);
if (v_isSharedCheck_2121_ == 0)
{
lean_object* v_unused_2122_; lean_object* v_unused_2123_; lean_object* v_unused_2124_; 
v_unused_2122_ = lean_ctor_get(v_h_u2081_2039_, 7);
lean_dec(v_unused_2122_);
v_unused_2123_ = lean_ctor_get(v_h_u2081_2039_, 1);
lean_dec(v_unused_2123_);
v_unused_2124_ = lean_ctor_get(v_h_u2081_2039_, 0);
lean_dec(v_unused_2124_);
v___x_2109_ = v_h_u2081_2039_;
v_isShared_2110_ = v_isSharedCheck_2121_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_isInserted_x3f_2107_);
lean_inc(v_isType_x3f_2106_);
lean_inc(v_isInstance_x3f_2105_);
lean_inc(v_val_x3f_2104_);
lean_inc(v_type_2103_);
lean_dec(v_h_u2081_2039_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2121_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2114_; 
v___x_2111_ = lean_box(v___x_2051_);
v___x_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 7, v___x_2112_);
lean_ctor_set(v___x_2109_, 1, v___x_2041_);
lean_ctor_set(v___x_2109_, 0, v___x_2040_);
v___x_2114_ = v___x_2109_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2040_);
lean_ctor_set(v_reuseFailAlloc_2120_, 1, v___x_2041_);
lean_ctor_set(v_reuseFailAlloc_2120_, 2, v_type_2103_);
lean_ctor_set(v_reuseFailAlloc_2120_, 3, v_val_x3f_2104_);
lean_ctor_set(v_reuseFailAlloc_2120_, 4, v_isInstance_x3f_2105_);
lean_ctor_set(v_reuseFailAlloc_2120_, 5, v_isType_x3f_2106_);
lean_ctor_set(v_reuseFailAlloc_2120_, 6, v_isInserted_x3f_2107_);
lean_ctor_set(v_reuseFailAlloc_2120_, 7, v___x_2112_);
v___x_2114_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
lean_object* v___x_2115_; lean_object* v___x_2117_; 
v___x_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 1, v___x_2059_);
lean_ctor_set(v___x_2057_, 0, v___x_2115_);
v___x_2117_ = v___x_2057_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2115_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v___x_2059_);
v___x_2117_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
lean_object* v___x_2118_; 
v___x_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
return v___x_2118_;
}
}
}
}
else
{
lean_object* v_type_2125_; lean_object* v_val_x3f_2126_; lean_object* v_isInstance_x3f_2127_; lean_object* v_isType_x3f_2128_; lean_object* v_isRemoved_x3f_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2143_; 
v_type_2125_ = lean_ctor_get(v_h_u2081_2039_, 2);
v_val_x3f_2126_ = lean_ctor_get(v_h_u2081_2039_, 3);
v_isInstance_x3f_2127_ = lean_ctor_get(v_h_u2081_2039_, 4);
v_isType_x3f_2128_ = lean_ctor_get(v_h_u2081_2039_, 5);
v_isRemoved_x3f_2129_ = lean_ctor_get(v_h_u2081_2039_, 7);
v_isSharedCheck_2143_ = !lean_is_exclusive(v_h_u2081_2039_);
if (v_isSharedCheck_2143_ == 0)
{
lean_object* v_unused_2144_; lean_object* v_unused_2145_; lean_object* v_unused_2146_; 
v_unused_2144_ = lean_ctor_get(v_h_u2081_2039_, 6);
lean_dec(v_unused_2144_);
v_unused_2145_ = lean_ctor_get(v_h_u2081_2039_, 1);
lean_dec(v_unused_2145_);
v_unused_2146_ = lean_ctor_get(v_h_u2081_2039_, 0);
lean_dec(v_unused_2146_);
v___x_2131_ = v_h_u2081_2039_;
v_isShared_2132_ = v_isSharedCheck_2143_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_isRemoved_x3f_2129_);
lean_inc(v_isType_x3f_2128_);
lean_inc(v_isInstance_x3f_2127_);
lean_inc(v_val_x3f_2126_);
lean_inc(v_type_2125_);
lean_dec(v_h_u2081_2039_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2143_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2136_; 
v___x_2133_ = lean_box(v___x_2051_);
v___x_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 6, v___x_2134_);
lean_ctor_set(v___x_2131_, 1, v___x_2041_);
lean_ctor_set(v___x_2131_, 0, v___x_2040_);
v___x_2136_ = v___x_2131_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2040_);
lean_ctor_set(v_reuseFailAlloc_2142_, 1, v___x_2041_);
lean_ctor_set(v_reuseFailAlloc_2142_, 2, v_type_2125_);
lean_ctor_set(v_reuseFailAlloc_2142_, 3, v_val_x3f_2126_);
lean_ctor_set(v_reuseFailAlloc_2142_, 4, v_isInstance_x3f_2127_);
lean_ctor_set(v_reuseFailAlloc_2142_, 5, v_isType_x3f_2128_);
lean_ctor_set(v_reuseFailAlloc_2142_, 6, v___x_2134_);
lean_ctor_set(v_reuseFailAlloc_2142_, 7, v_isRemoved_x3f_2129_);
v___x_2136_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
lean_object* v___x_2137_; lean_object* v___x_2139_; 
v___x_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2136_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 1, v___x_2059_);
lean_ctor_set(v___x_2057_, 0, v___x_2137_);
v___x_2139_ = v___x_2057_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2137_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v___x_2059_);
v___x_2139_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
lean_object* v___x_2140_; 
v___x_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2139_);
return v___x_2140_;
}
}
}
}
}
}
else
{
lean_object* v___x_2147_; size_t v___x_2148_; size_t v___x_2149_; 
lean_del_object(v___x_2057_);
lean_dec(v_fst_2054_);
v___x_2147_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___closed__0));
v___x_2148_ = ((size_t)1ULL);
v___x_2149_ = lean_usize_add(v_i_2044_, v___x_2148_);
v_i_2044_ = v___x_2149_;
v_b_2045_ = v___x_2147_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_u2080_2037_ = stack[0].m_obj;
uint8_t v_useAfter_2038_ = stack[1].m_num;
lean_object* v_h_u2081_2039_ = stack[2].m_obj;
lean_object* v___x_2040_ = stack[3].m_obj;
lean_object* v___x_2041_ = stack[4].m_obj;
lean_object* v_as_2042_ = stack[5].m_obj;
size_t v_sz_2043_ = stack[6].m_num;
size_t v_i_2044_ = stack[7].m_num;
lean_object* v_b_2045_ = stack[8].m_obj;
lean_object* v___y_2046_ = stack[9].m_obj;
lean_object* v___y_2047_ = stack[10].m_obj;
lean_object* v___y_2048_ = stack[11].m_obj;
lean_object* v___y_2049_ = stack[12].m_obj;
lean_object* v_res_2152_;
v_res_2152_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(v_ctx_u2080_2037_, v_useAfter_2038_, v_h_u2081_2039_, v___x_2040_, v___x_2041_, v_as_2042_, v_sz_2043_, v_i_2044_, v_b_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
stack->m_obj
 = v_res_2152_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___boxed(lean_object* v_ctx_u2080_2153_, lean_object* v_useAfter_2154_, lean_object* v_h_u2081_2155_, lean_object* v___x_2156_, lean_object* v___x_2157_, lean_object* v_as_2158_, lean_object* v_sz_2159_, lean_object* v_i_2160_, lean_object* v_b_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
uint8_t v_useAfter_boxed_2167_; size_t v_sz_boxed_2168_; size_t v_i_boxed_2169_; lean_object* v_res_2170_; 
v_useAfter_boxed_2167_ = lean_unbox(v_useAfter_2154_);
v_sz_boxed_2168_ = lean_unbox_usize(v_sz_2159_);
lean_dec(v_sz_2159_);
v_i_boxed_2169_ = lean_unbox_usize(v_i_2160_);
lean_dec(v_i_2160_);
v_res_2170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(v_ctx_u2080_2153_, v_useAfter_boxed_2167_, v_h_u2081_2155_, v___x_2156_, v___x_2157_, v_as_2158_, v_sz_boxed_2168_, v_i_boxed_2169_, v_b_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec_ref(v_as_2158_);
lean_dec_ref(v_ctx_u2080_2153_);
return v_res_2170_;
}
}
lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(uint8_t v_useAfter_2171_, lean_object* v_ctx_u2080_2172_, lean_object* v_h_u2081_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_){
_start:
{
lean_object* v_names_2179_; lean_object* v_fvarIds_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; size_t v_sz_2183_; size_t v___x_2184_; lean_object* v___x_2185_; 
v_names_2179_ = lean_ctor_get(v_h_u2081_2173_, 0);
v_fvarIds_2180_ = lean_ctor_get(v_h_u2081_2173_, 1);
v___x_2181_ = l_Array_zip___redArg(v_names_2179_, v_fvarIds_2180_);
v___x_2182_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___closed__0));
v_sz_2183_ = lean_array_size(v___x_2181_);
v___x_2184_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_2180_);
lean_inc_ref(v_names_2179_);
lean_inc_ref(v_h_u2081_2173_);
v___x_2185_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(v_ctx_u2080_2172_, v_useAfter_2171_, v_h_u2081_2173_, v_names_2179_, v_fvarIds_2180_, v___x_2181_, v_sz_2183_, v___x_2184_, v___x_2182_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
lean_dec_ref(v___x_2181_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2198_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2188_ = v___x_2185_;
v_isShared_2189_ = v_isSharedCheck_2198_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2185_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2198_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v_fst_2190_; 
v_fst_2190_ = lean_ctor_get(v_a_2186_, 0);
lean_inc(v_fst_2190_);
lean_dec(v_a_2186_);
if (lean_obj_tag(v_fst_2190_) == 0)
{
lean_object* v___x_2192_; 
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 0, v_h_u2081_2173_);
v___x_2192_ = v___x_2188_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_h_u2081_2173_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
else
{
lean_object* v_val_2194_; lean_object* v___x_2196_; 
lean_dec_ref(v_h_u2081_2173_);
v_val_2194_ = lean_ctor_get(v_fst_2190_, 0);
lean_inc(v_val_2194_);
lean_dec_ref_known(v_fst_2190_, 1);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 0, v_val_2194_);
v___x_2196_ = v___x_2188_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_val_2194_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
lean_dec_ref(v_h_u2081_2173_);
v_a_2199_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2185_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2185_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_0interp(lean_interpreter_value* stack)
{
uint8_t v_useAfter_2171_ = stack[0].m_num;
lean_object* v_ctx_u2080_2172_ = stack[1].m_obj;
lean_object* v_h_u2081_2173_ = stack[2].m_obj;
lean_object* v_a_2174_ = stack[3].m_obj;
lean_object* v_a_2175_ = stack[4].m_obj;
lean_object* v_a_2176_ = stack[5].m_obj;
lean_object* v_a_2177_ = stack[6].m_obj;
lean_object* v_res_2207_;
v_res_2207_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(v_useAfter_2171_, v_ctx_u2080_2172_, v_h_u2081_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
stack->m_obj
 = v_res_2207_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle___boxed(lean_object* v_useAfter_2208_, lean_object* v_ctx_u2080_2209_, lean_object* v_h_u2081_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_){
_start:
{
uint8_t v_useAfter_boxed_2216_; lean_object* v_res_2217_; 
v_useAfter_boxed_2216_ = lean_unbox(v_useAfter_2208_);
v_res_2217_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(v_useAfter_boxed_2216_, v_ctx_u2080_2209_, v_h_u2081_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_);
lean_dec(v_a_2214_);
lean_dec_ref(v_a_2213_);
lean_dec(v_a_2212_);
lean_dec_ref(v_a_2211_);
lean_dec_ref(v_ctx_u2080_2209_);
return v_res_2217_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(uint8_t v_useAfter_2218_, lean_object* v_lctx_u2080_2219_, size_t v_sz_2220_, size_t v_i_2221_, lean_object* v_bs_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
uint8_t v___x_2228_; 
v___x_2228_ = lean_usize_dec_lt(v_i_2221_, v_sz_2220_);
if (v___x_2228_ == 0)
{
lean_object* v___x_2229_; 
v___x_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2229_, 0, v_bs_2222_);
return v___x_2229_;
}
else
{
lean_object* v_v_2230_; lean_object* v___x_2231_; lean_object* v_bs_x27_2232_; lean_object* v___x_2233_; 
v_v_2230_ = lean_array_uget(v_bs_2222_, v_i_2221_);
v___x_2231_ = lean_unsigned_to_nat(0u);
v_bs_x27_2232_ = lean_array_uset(v_bs_2222_, v_i_2221_, v___x_2231_);
v___x_2233_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(v_useAfter_2218_, v_lctx_u2080_2219_, v_v_2230_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; size_t v___x_2235_; size_t v___x_2236_; lean_object* v___x_2237_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_a_2234_);
lean_dec_ref_known(v___x_2233_, 1);
v___x_2235_ = ((size_t)1ULL);
v___x_2236_ = lean_usize_add(v_i_2221_, v___x_2235_);
v___x_2237_ = lean_array_uset(v_bs_x27_2232_, v_i_2221_, v_a_2234_);
v_i_2221_ = v___x_2236_;
v_bs_2222_ = v___x_2237_;
goto _start;
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_dec_ref(v_bs_x27_2232_);
v_a_2239_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2233_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2233_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_useAfter_2218_ = stack[0].m_num;
lean_object* v_lctx_u2080_2219_ = stack[1].m_obj;
size_t v_sz_2220_ = stack[2].m_num;
size_t v_i_2221_ = stack[3].m_num;
lean_object* v_bs_2222_ = stack[4].m_obj;
lean_object* v___y_2223_ = stack[5].m_obj;
lean_object* v___y_2224_ = stack[6].m_obj;
lean_object* v___y_2225_ = stack[7].m_obj;
lean_object* v___y_2226_ = stack[8].m_obj;
lean_object* v_res_2247_;
v_res_2247_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(v_useAfter_2218_, v_lctx_u2080_2219_, v_sz_2220_, v_i_2221_, v_bs_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
stack->m_obj
 = v_res_2247_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0___boxed(lean_object* v_useAfter_2248_, lean_object* v_lctx_u2080_2249_, lean_object* v_sz_2250_, lean_object* v_i_2251_, lean_object* v_bs_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
uint8_t v_useAfter_boxed_2258_; size_t v_sz_boxed_2259_; size_t v_i_boxed_2260_; lean_object* v_res_2261_; 
v_useAfter_boxed_2258_ = lean_unbox(v_useAfter_2248_);
v_sz_boxed_2259_ = lean_unbox_usize(v_sz_2250_);
lean_dec(v_sz_2250_);
v_i_boxed_2260_ = lean_unbox_usize(v_i_2251_);
lean_dec(v_i_2251_);
v_res_2261_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(v_useAfter_boxed_2258_, v_lctx_u2080_2249_, v_sz_boxed_2259_, v_i_boxed_2260_, v_bs_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec_ref(v_lctx_u2080_2249_);
return v_res_2261_;
}
}
lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(uint8_t v_useAfter_2262_, lean_object* v_lctx_u2080_2263_, lean_object* v_hs_u2081_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_){
_start:
{
size_t v_sz_2270_; size_t v___x_2271_; lean_object* v___x_2272_; 
v_sz_2270_ = lean_array_size(v_hs_u2081_2264_);
v___x_2271_ = ((size_t)0ULL);
v___x_2272_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(v_useAfter_2262_, v_lctx_u2080_2263_, v_sz_2270_, v___x_2271_, v_hs_u2081_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_);
return v___x_2272_;
}
}
LEAN_EXPORT void l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_0interp(lean_interpreter_value* stack)
{
uint8_t v_useAfter_2262_ = stack[0].m_num;
lean_object* v_lctx_u2080_2263_ = stack[1].m_obj;
lean_object* v_hs_u2081_2264_ = stack[2].m_obj;
lean_object* v_a_2265_ = stack[3].m_obj;
lean_object* v_a_2266_ = stack[4].m_obj;
lean_object* v_a_2267_ = stack[5].m_obj;
lean_object* v_a_2268_ = stack[6].m_obj;
lean_object* v_res_2273_;
v_res_2273_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(v_useAfter_2262_, v_lctx_u2080_2263_, v_hs_u2081_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_);
stack->m_obj
 = v_res_2273_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses___boxed(lean_object* v_useAfter_2274_, lean_object* v_lctx_u2080_2275_, lean_object* v_hs_u2081_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_){
_start:
{
uint8_t v_useAfter_boxed_2282_; lean_object* v_res_2283_; 
v_useAfter_boxed_2282_ = lean_unbox(v_useAfter_2274_);
v_res_2283_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(v_useAfter_boxed_2282_, v_lctx_u2080_2275_, v_hs_u2081_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_);
lean_dec(v_a_2280_);
lean_dec_ref(v_a_2279_);
lean_dec(v_a_2278_);
lean_dec_ref(v_a_2277_);
lean_dec_ref(v_lctx_u2080_2275_);
return v_res_2283_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2(void){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__1));
v___x_2289_ = l_Lean_stringToMessageData(v___x_2288_);
return v___x_2289_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4(void){
_start:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__3));
v___x_2292_ = l_Lean_stringToMessageData(v___x_2291_);
return v___x_2292_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6(void){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2294_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__5));
v___x_2295_ = l_Lean_stringToMessageData(v___x_2294_);
return v___x_2295_;
}
}
lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(uint8_t v_useAfter_2296_, lean_object* v_g_u2080_2297_, lean_object* v_i_u2081_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v___x_2304_; lean_object* v_mctx_2305_; lean_object* v___x_2306_; 
v___x_2304_ = lean_st_ref_get(v_a_2300_);
v_mctx_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc_ref(v_mctx_2305_);
lean_dec(v___x_2304_);
v___x_2306_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2305_, v_g_u2080_2297_);
lean_dec_ref(v_mctx_2305_);
if (lean_obj_tag(v___x_2306_) == 1)
{
lean_object* v_val_2307_; lean_object* v_lctx_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v_toInteractiveGoalCore_2313_; lean_object* v_fst_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2411_; 
v_val_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_val_2307_);
lean_dec_ref_known(v___x_2306_, 1);
v_lctx_2308_ = lean_ctor_get(v_val_2307_, 1);
lean_inc_ref(v_lctx_2308_);
lean_dec(v_val_2307_);
v___x_2309_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2301_);
v___x_2310_ = lean_box(1);
v___x_2311_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2309_);
lean_ctor_set(v___x_2311_, 1, v___x_2310_);
lean_ctor_set(v___x_2311_, 2, v___x_2310_);
v___x_2312_ = l_Lean_LocalContext_sanitizeNames(v_lctx_2308_, v___x_2311_);
v_toInteractiveGoalCore_2313_ = lean_ctor_get(v_i_u2081_2298_, 0);
lean_inc_ref(v_toInteractiveGoalCore_2313_);
v_fst_2314_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2411_ == 0)
{
lean_object* v_unused_2412_; 
v_unused_2412_ = lean_ctor_get(v___x_2312_, 1);
lean_dec(v_unused_2412_);
v___x_2316_ = v___x_2312_;
v_isShared_2317_ = v_isSharedCheck_2411_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_fst_2314_);
lean_dec(v___x_2312_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2411_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v_userName_x3f_2318_; lean_object* v_goalPrefix_2319_; lean_object* v_mvarId_2320_; lean_object* v_isRemoved_x3f_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2408_; 
v_userName_x3f_2318_ = lean_ctor_get(v_i_u2081_2298_, 1);
v_goalPrefix_2319_ = lean_ctor_get(v_i_u2081_2298_, 2);
v_mvarId_2320_ = lean_ctor_get(v_i_u2081_2298_, 3);
v_isRemoved_x3f_2321_ = lean_ctor_get(v_i_u2081_2298_, 5);
v_isSharedCheck_2408_ = !lean_is_exclusive(v_i_u2081_2298_);
if (v_isSharedCheck_2408_ == 0)
{
lean_object* v_unused_2409_; lean_object* v_unused_2410_; 
v_unused_2409_ = lean_ctor_get(v_i_u2081_2298_, 4);
lean_dec(v_unused_2409_);
v_unused_2410_ = lean_ctor_get(v_i_u2081_2298_, 0);
lean_dec(v_unused_2410_);
v___x_2323_ = v_i_u2081_2298_;
v_isShared_2324_ = v_isSharedCheck_2408_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_isRemoved_x3f_2321_);
lean_inc(v_mvarId_2320_);
lean_inc(v_goalPrefix_2319_);
lean_inc(v_userName_x3f_2318_);
lean_dec(v_i_u2081_2298_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2408_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v_hyps_2325_; lean_object* v_type_2326_; lean_object* v_ctx_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2407_; 
v_hyps_2325_ = lean_ctor_get(v_toInteractiveGoalCore_2313_, 0);
v_type_2326_ = lean_ctor_get(v_toInteractiveGoalCore_2313_, 1);
v_ctx_2327_ = lean_ctor_get(v_toInteractiveGoalCore_2313_, 2);
v_isSharedCheck_2407_ = !lean_is_exclusive(v_toInteractiveGoalCore_2313_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2329_ = v_toInteractiveGoalCore_2313_;
v_isShared_2330_ = v_isSharedCheck_2407_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_ctx_2327_);
lean_inc(v_type_2326_);
lean_inc(v_hyps_2325_);
lean_dec(v_toInteractiveGoalCore_2313_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2407_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2331_; 
v___x_2331_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(v_useAfter_2296_, v_fst_2314_, v_hyps_2325_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v_fst_2314_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2332_);
lean_dec_ref_known(v___x_2331_, 1);
v___x_2333_ = l_Lean_Expr_mvar___override(v_g_u2080_2297_);
lean_inc(v_a_2302_);
lean_inc_ref(v_a_2301_);
lean_inc(v_a_2300_);
lean_inc_ref(v_a_2299_);
v___x_2334_ = lean_infer_type(v___x_2333_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v___x_2336_; lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2390_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref_known(v___x_2334_, 1);
v___x_2336_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_a_2335_, v_a_2300_);
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2339_ = v___x_2336_;
v_isShared_2340_ = v_isSharedCheck_2390_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2336_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2390_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2341_; lean_object* v_mctx_2342_; lean_object* v___x_2343_; 
v___x_2341_ = lean_st_ref_get(v_a_2300_);
v_mctx_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc_ref(v_mctx_2342_);
lean_dec(v___x_2341_);
v___x_2343_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2342_, v_mvarId_2320_);
lean_dec_ref(v_mctx_2342_);
if (lean_obj_tag(v___x_2343_) == 1)
{
lean_object* v_val_2344_; lean_object* v_type_2345_; lean_object* v___x_2346_; lean_object* v_a_2347_; lean_object* v___x_2348_; 
lean_del_object(v___x_2339_);
lean_del_object(v___x_2316_);
v_val_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_val_2344_);
lean_dec_ref_known(v___x_2343_, 1);
v_type_2345_ = lean_ctor_get(v_val_2344_, 2);
lean_inc_ref(v_type_2345_);
lean_dec(v_val_2344_);
v___x_2346_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_type_2345_, v_a_2300_);
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_a_2347_);
lean_dec_ref(v___x_2346_);
v___x_2348_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(v_a_2337_, v_a_2347_, v_useAfter_2296_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2350_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2349_);
lean_dec_ref_known(v___x_2348_, 1);
v___x_2350_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(v_useAfter_2296_, v_a_2349_, v_type_2326_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2365_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2353_ = v___x_2350_;
v_isShared_2354_ = v_isSharedCheck_2365_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2350_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2365_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 1, v_a_2351_);
lean_ctor_set(v___x_2329_, 0, v_a_2332_);
v___x_2356_ = v___x_2329_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2332_);
lean_ctor_set(v_reuseFailAlloc_2364_, 1, v_a_2351_);
lean_ctor_set(v_reuseFailAlloc_2364_, 2, v_ctx_2327_);
v___x_2356_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
lean_object* v___x_2357_; lean_object* v___x_2359_; 
v___x_2357_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__0));
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 4, v___x_2357_);
lean_ctor_set(v___x_2323_, 0, v___x_2356_);
v___x_2359_ = v___x_2323_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2356_);
lean_ctor_set(v_reuseFailAlloc_2363_, 1, v_userName_x3f_2318_);
lean_ctor_set(v_reuseFailAlloc_2363_, 2, v_goalPrefix_2319_);
lean_ctor_set(v_reuseFailAlloc_2363_, 3, v_mvarId_2320_);
lean_ctor_set(v_reuseFailAlloc_2363_, 4, v___x_2357_);
lean_ctor_set(v_reuseFailAlloc_2363_, 5, v_isRemoved_x3f_2321_);
v___x_2359_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
lean_object* v___x_2361_; 
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v___x_2359_);
v___x_2361_ = v___x_2353_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2359_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_dec(v_a_2332_);
lean_del_object(v___x_2329_);
lean_dec_ref(v_ctx_2327_);
lean_del_object(v___x_2323_);
lean_dec(v_isRemoved_x3f_2321_);
lean_dec(v_mvarId_2320_);
lean_dec_ref(v_goalPrefix_2319_);
lean_dec(v_userName_x3f_2318_);
v_a_2366_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2350_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2350_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2381_; 
lean_dec(v_a_2332_);
lean_del_object(v___x_2329_);
lean_dec_ref(v_ctx_2327_);
lean_dec_ref(v_type_2326_);
lean_del_object(v___x_2323_);
lean_dec(v_isRemoved_x3f_2321_);
lean_dec(v_mvarId_2320_);
lean_dec_ref(v_goalPrefix_2319_);
lean_dec(v_userName_x3f_2318_);
v_a_2374_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2376_ = v___x_2348_;
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2348_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2377_ == 0)
{
v___x_2379_ = v___x_2376_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
else
{
lean_object* v___x_2382_; lean_object* v___x_2384_; 
lean_dec(v___x_2343_);
lean_dec(v_a_2337_);
lean_dec(v_a_2332_);
lean_del_object(v___x_2329_);
lean_dec_ref(v_ctx_2327_);
lean_dec_ref(v_type_2326_);
lean_del_object(v___x_2323_);
lean_dec(v_isRemoved_x3f_2321_);
lean_dec_ref(v_goalPrefix_2319_);
lean_dec(v_userName_x3f_2318_);
v___x_2382_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2);
if (v_isShared_2340_ == 0)
{
lean_ctor_set_tag(v___x_2339_, 1);
lean_ctor_set(v___x_2339_, 0, v_mvarId_2320_);
v___x_2384_ = v___x_2339_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_mvarId_2320_);
v___x_2384_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
lean_object* v___x_2386_; 
if (v_isShared_2317_ == 0)
{
lean_ctor_set_tag(v___x_2316_, 7);
lean_ctor_set(v___x_2316_, 1, v___x_2384_);
lean_ctor_set(v___x_2316_, 0, v___x_2382_);
v___x_2386_ = v___x_2316_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2382_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v___x_2384_);
v___x_2386_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
lean_object* v___x_2387_; 
v___x_2387_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_2386_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_2387_;
}
}
}
}
}
else
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
lean_dec(v_a_2332_);
lean_del_object(v___x_2329_);
lean_dec_ref(v_ctx_2327_);
lean_dec_ref(v_type_2326_);
lean_del_object(v___x_2323_);
lean_dec(v_isRemoved_x3f_2321_);
lean_dec(v_mvarId_2320_);
lean_dec_ref(v_goalPrefix_2319_);
lean_dec(v_userName_x3f_2318_);
lean_del_object(v___x_2316_);
v_a_2391_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2393_ = v___x_2334_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2334_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2391_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
else
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
lean_del_object(v___x_2329_);
lean_dec_ref(v_ctx_2327_);
lean_dec_ref(v_type_2326_);
lean_del_object(v___x_2323_);
lean_dec(v_isRemoved_x3f_2321_);
lean_dec(v_mvarId_2320_);
lean_dec_ref(v_goalPrefix_2319_);
lean_dec(v_userName_x3f_2318_);
lean_del_object(v___x_2316_);
lean_dec(v_g_u2080_2297_);
v_a_2399_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2331_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2331_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2402_ == 0)
{
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2399_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
lean_dec(v___x_2306_);
lean_dec_ref(v_i_u2081_2298_);
v___x_2413_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4);
v___x_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2414_, 0, v_g_u2080_2297_);
v___x_2415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2413_);
lean_ctor_set(v___x_2415_, 1, v___x_2414_);
v___x_2416_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6);
v___x_2417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2415_);
lean_ctor_set(v___x_2417_, 1, v___x_2416_);
v___x_2418_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_2417_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_2418_;
}
}
}
LEAN_EXPORT void l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal_0interp(lean_interpreter_value* stack)
{
uint8_t v_useAfter_2296_ = stack[0].m_num;
lean_object* v_g_u2080_2297_ = stack[1].m_obj;
lean_object* v_i_u2081_2298_ = stack[2].m_obj;
lean_object* v_a_2299_ = stack[3].m_obj;
lean_object* v_a_2300_ = stack[4].m_obj;
lean_object* v_a_2301_ = stack[5].m_obj;
lean_object* v_a_2302_ = stack[6].m_obj;
lean_object* v_res_2419_;
v_res_2419_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(v_useAfter_2296_, v_g_u2080_2297_, v_i_u2081_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
stack->m_obj
 = v_res_2419_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___boxed(lean_object* v_useAfter_2420_, lean_object* v_g_u2080_2421_, lean_object* v_i_u2081_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_){
_start:
{
uint8_t v_useAfter_boxed_2428_; lean_object* v_res_2429_; 
v_useAfter_boxed_2428_ = lean_unbox(v_useAfter_2420_);
v_res_2429_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(v_useAfter_boxed_2428_, v_g_u2080_2421_, v_i_u2081_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
lean_dec(v_a_2426_);
lean_dec_ref(v_a_2425_);
lean_dec(v_a_2424_);
lean_dec_ref(v_a_2423_);
return v_res_2429_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(lean_object* v_opts_2430_, lean_object* v_opt_2431_){
_start:
{
lean_object* v_name_2432_; lean_object* v_defValue_2433_; lean_object* v_map_2434_; lean_object* v___x_2435_; 
v_name_2432_ = lean_ctor_get(v_opt_2431_, 0);
v_defValue_2433_ = lean_ctor_get(v_opt_2431_, 1);
v_map_2434_ = lean_ctor_get(v_opts_2430_, 0);
v___x_2435_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2434_, v_name_2432_);
if (lean_obj_tag(v___x_2435_) == 0)
{
uint8_t v___x_2436_; 
v___x_2436_ = lean_unbox(v_defValue_2433_);
return v___x_2436_;
}
else
{
lean_object* v_val_2437_; 
v_val_2437_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_val_2437_);
lean_dec_ref_known(v___x_2435_, 1);
if (lean_obj_tag(v_val_2437_) == 1)
{
uint8_t v_v_2438_; 
v_v_2438_ = lean_ctor_get_uint8(v_val_2437_, 0);
lean_dec_ref_known(v_val_2437_, 0);
return v_v_2438_;
}
else
{
uint8_t v___x_2439_; 
lean_dec(v_val_2437_);
v___x_2439_ = lean_unbox(v_defValue_2433_);
return v___x_2439_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_2430_ = stack[0].m_obj;
lean_object* v_opt_2431_ = stack[1].m_obj;
uint8_t v_res_2440_;
v_res_2440_ = l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(v_opts_2430_, v_opt_2431_);
stack->m_num = v_res_2440_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0___boxed(lean_object* v_opts_2441_, lean_object* v_opt_2442_){
_start:
{
uint8_t v_res_2443_; lean_object* v_r_2444_; 
v_res_2443_ = l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(v_opts_2441_, v_opt_2442_);
lean_dec_ref(v_opt_2442_);
lean_dec_ref(v_opts_2441_);
v_r_2444_ = lean_box(v_res_2443_);
return v_r_2444_;
}
}
lean_object* l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(lean_object* v_x_2445_, lean_object* v_x_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
if (lean_obj_tag(v_x_2446_) == 0)
{
lean_object* v___x_2452_; 
v___x_2452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2452_, 0, v_x_2445_);
return v___x_2452_;
}
else
{
lean_object* v_head_2453_; lean_object* v_tail_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
v_head_2453_ = lean_ctor_get(v_x_2446_, 0);
lean_inc_n(v_head_2453_, 2);
v_tail_2454_ = lean_ctor_get(v_x_2446_, 1);
lean_inc(v_tail_2454_);
lean_dec_ref_known(v_x_2446_, 2);
v___x_2455_ = l_Lean_Expr_mvar___override(v_head_2453_);
v___x_2456_ = l_Lean_Meta_getMVars(v___x_2455_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_a_2457_);
lean_dec_ref_known(v___x_2456_, 1);
v___x_2458_ = l_Lean_MVarIdSet_ofArray(v_a_2457_);
lean_dec(v_a_2457_);
v___x_2459_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_head_2453_, v___x_2458_, v_x_2445_);
v_x_2445_ = v___x_2459_;
v_x_2446_ = v_tail_2454_;
goto _start;
}
else
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
lean_dec(v_tail_2454_);
lean_dec(v_head_2453_);
lean_dec(v_x_2445_);
v_a_2461_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2456_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2456_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2445_ = stack[0].m_obj;
lean_object* v_x_2446_ = stack[1].m_obj;
lean_object* v___y_2447_ = stack[2].m_obj;
lean_object* v___y_2448_ = stack[3].m_obj;
lean_object* v___y_2449_ = stack[4].m_obj;
lean_object* v___y_2450_ = stack[5].m_obj;
lean_object* v_res_2469_;
v_res_2469_ = l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(v_x_2445_, v_x_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
stack->m_obj
 = v_res_2469_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1___boxed(lean_object* v_x_2470_, lean_object* v_x_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(v_x_2470_, v_x_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
return v_res_2477_;
}
}
lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(lean_object* v_lctx_2478_, lean_object* v_localInsts_2479_, lean_object* v_x_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v___x_2486_; 
v___x_2486_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2478_, v_localInsts_2479_, v_x_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___x_2486_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2486_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2487_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
v_a_2495_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2486_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2486_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_2478_ = stack[0].m_obj;
lean_object* v_localInsts_2479_ = stack[1].m_obj;
lean_object* v_x_2480_ = stack[2].m_obj;
lean_object* v___y_2481_ = stack[3].m_obj;
lean_object* v___y_2482_ = stack[4].m_obj;
lean_object* v___y_2483_ = stack[5].m_obj;
lean_object* v___y_2484_ = stack[6].m_obj;
lean_object* v_res_2503_;
v_res_2503_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(v_lctx_2478_, v_localInsts_2479_, v_x_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
stack->m_obj
 = v_res_2503_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg___boxed(lean_object* v_lctx_2504_, lean_object* v_localInsts_2505_, lean_object* v_x_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(v_lctx_2504_, v_localInsts_2505_, v_x_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
return v_res_2512_;
}
}
static lean_object* _init_l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2514_ = ((lean_object*)(l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__0));
v___x_2515_ = l_Lean_stringToMessageData(v___x_2514_);
return v___x_2515_;
}
}
lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(lean_object* v_goal_2516_, lean_object* v_action_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v___x_2523_; lean_object* v_mctx_2524_; lean_object* v___x_2525_; 
v___x_2523_ = lean_st_ref_get(v___y_2519_);
v_mctx_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc_ref(v_mctx_2524_);
lean_dec(v___x_2523_);
v___x_2525_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2524_, v_goal_2516_);
lean_dec_ref(v_mctx_2524_);
if (lean_obj_tag(v___x_2525_) == 1)
{
lean_object* v_val_2526_; lean_object* v_lctx_2527_; lean_object* v_localInstances_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v_fst_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
lean_dec(v_goal_2516_);
v_val_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_val_2526_);
lean_dec_ref_known(v___x_2525_, 1);
v_lctx_2527_ = lean_ctor_get(v_val_2526_, 1);
v_localInstances_2528_ = lean_ctor_get(v_val_2526_, 4);
lean_inc_ref(v_localInstances_2528_);
v___x_2529_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2520_);
v___x_2530_ = lean_box(1);
v___x_2531_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2529_);
lean_ctor_set(v___x_2531_, 1, v___x_2530_);
lean_ctor_set(v___x_2531_, 2, v___x_2530_);
lean_inc_ref(v_lctx_2527_);
v___x_2532_ = l_Lean_LocalContext_sanitizeNames(v_lctx_2527_, v___x_2531_);
v_fst_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc_n(v_fst_2533_, 2);
lean_dec_ref(v___x_2532_);
v___x_2534_ = lean_apply_2(v_action_2517_, v_fst_2533_, v_val_2526_);
v___x_2535_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(v_fst_2533_, v_localInstances_2528_, v___x_2534_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
return v___x_2535_;
}
else
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
lean_dec(v___x_2525_);
lean_dec_ref(v_action_2517_);
v___x_2536_ = lean_obj_once(&l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1, &l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1_once, _init_l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1);
v___x_2537_ = l_Lean_MessageData_ofName(v_goal_2516_);
v___x_2538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2536_);
lean_ctor_set(v___x_2538_, 1, v___x_2537_);
v___x_2539_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_2538_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
return v___x_2539_;
}
}
}
LEAN_EXPORT void l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_2516_ = stack[0].m_obj;
lean_object* v_action_2517_ = stack[1].m_obj;
lean_object* v___y_2518_ = stack[2].m_obj;
lean_object* v___y_2519_ = stack[3].m_obj;
lean_object* v___y_2520_ = stack[4].m_obj;
lean_object* v___y_2521_ = stack[5].m_obj;
lean_object* v_res_2540_;
v_res_2540_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(v_goal_2516_, v_action_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
stack->m_obj
 = v_res_2540_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___boxed(lean_object* v_goal_2541_, lean_object* v_action_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(v_goal_2541_, v_action_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
return v_res_2548_;
}
}
uint8_t l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4(lean_object* v___x_2549_, lean_object* v_x_2550_){
_start:
{
if (lean_obj_tag(v_x_2550_) == 0)
{
uint8_t v___x_2551_; 
v___x_2551_ = 0;
return v___x_2551_;
}
else
{
lean_object* v_head_2552_; lean_object* v_tail_2553_; uint8_t v___x_2554_; 
v_head_2552_ = lean_ctor_get(v_x_2550_, 0);
v_tail_2553_ = lean_ctor_get(v_x_2550_, 1);
v___x_2554_ = l_Lean_instBEqMVarId_beq(v_head_2552_, v___x_2549_);
if (v___x_2554_ == 0)
{
v_x_2550_ = v_tail_2553_;
goto _start;
}
else
{
return v___x_2554_;
}
}
}
}
LEAN_EXPORT void l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2549_ = stack[0].m_obj;
lean_object* v_x_2550_ = stack[1].m_obj;
uint8_t v_res_2556_;
v_res_2556_ = l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4(v___x_2549_, v_x_2550_);
stack->m_num = v_res_2556_;
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4___boxed(lean_object* v___x_2557_, lean_object* v_x_2558_){
_start:
{
uint8_t v_res_2559_; lean_object* v_r_2560_; 
v_res_2559_ = l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4(v___x_2557_, v_x_2558_);
lean_dec(v_x_2558_);
lean_dec(v___x_2557_);
v_r_2560_ = lean_box(v_res_2559_);
return v_r_2560_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(lean_object* v_t_2561_, lean_object* v_k_2562_){
_start:
{
if (lean_obj_tag(v_t_2561_) == 0)
{
lean_object* v_k_2563_; lean_object* v_v_2564_; lean_object* v_l_2565_; lean_object* v_r_2566_; uint8_t v___x_2567_; 
v_k_2563_ = lean_ctor_get(v_t_2561_, 1);
v_v_2564_ = lean_ctor_get(v_t_2561_, 2);
v_l_2565_ = lean_ctor_get(v_t_2561_, 3);
v_r_2566_ = lean_ctor_get(v_t_2561_, 4);
v___x_2567_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2562_, v_k_2563_);
switch(v___x_2567_)
{
case 0:
{
v_t_2561_ = v_l_2565_;
goto _start;
}
case 1:
{
lean_object* v___x_2569_; 
lean_inc(v_v_2564_);
v___x_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2569_, 0, v_v_2564_);
return v___x_2569_;
}
default: 
{
v_t_2561_ = v_r_2566_;
goto _start;
}
}
}
else
{
lean_object* v___x_2571_; 
v___x_2571_ = lean_box(0);
return v___x_2571_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg___boxed(lean_object* v_t_2572_, lean_object* v_k_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(v_t_2572_, v_k_2573_);
lean_dec(v_k_2573_);
lean_dec(v_t_2572_);
return v_res_2574_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(lean_object* v_k_2575_, lean_object* v_t_2576_){
_start:
{
if (lean_obj_tag(v_t_2576_) == 0)
{
lean_object* v_k_2577_; lean_object* v_l_2578_; lean_object* v_r_2579_; uint8_t v___x_2580_; 
v_k_2577_ = lean_ctor_get(v_t_2576_, 1);
v_l_2578_ = lean_ctor_get(v_t_2576_, 3);
v_r_2579_ = lean_ctor_get(v_t_2576_, 4);
v___x_2580_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2575_, v_k_2577_);
switch(v___x_2580_)
{
case 0:
{
v_t_2576_ = v_l_2578_;
goto _start;
}
case 1:
{
uint8_t v___x_2582_; 
v___x_2582_ = 1;
return v___x_2582_;
}
default: 
{
v_t_2576_ = v_r_2579_;
goto _start;
}
}
}
else
{
uint8_t v___x_2584_; 
v___x_2584_ = 0;
return v___x_2584_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2575_ = stack[0].m_obj;
lean_object* v_t_2576_ = stack[1].m_obj;
uint8_t v_res_2585_;
v_res_2585_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_k_2575_, v_t_2576_);
stack->m_num = v_res_2585_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg___boxed(lean_object* v_k_2586_, lean_object* v_t_2587_){
_start:
{
uint8_t v_res_2588_; lean_object* v_r_2589_; 
v_res_2588_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_k_2586_, v_t_2587_);
lean_dec(v_t_2587_);
lean_dec(v_k_2586_);
v_r_2589_ = lean_box(v_res_2588_);
return v_r_2589_;
}
}
uint8_t l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(lean_object* v_a_2590_, uint8_t v___x_2591_, lean_object* v_before_2592_, lean_object* v_after_2593_){
_start:
{
lean_object* v___x_2594_; 
v___x_2594_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(v_a_2590_, v_before_2592_);
if (lean_obj_tag(v___x_2594_) == 0)
{
return v___x_2591_;
}
else
{
lean_object* v_val_2595_; uint8_t v___x_2596_; 
v_val_2595_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_val_2595_);
lean_dec_ref_known(v___x_2594_, 1);
v___x_2596_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_after_2593_, v_val_2595_);
lean_dec(v_val_2595_);
return v___x_2596_;
}
}
}
LEAN_EXPORT void l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2590_ = stack[0].m_obj;
uint8_t v___x_2591_ = stack[1].m_num;
lean_object* v_before_2592_ = stack[2].m_obj;
lean_object* v_after_2593_ = stack[3].m_obj;
uint8_t v_res_2597_;
v_res_2597_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(v_a_2590_, v___x_2591_, v_before_2592_, v_after_2593_);
stack->m_num = v_res_2597_;
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0___boxed(lean_object* v_a_2598_, lean_object* v___x_2599_, lean_object* v_before_2600_, lean_object* v_after_2601_){
_start:
{
uint8_t v___x_3389__boxed_2602_; uint8_t v_res_2603_; lean_object* v_r_2604_; 
v___x_3389__boxed_2602_ = lean_unbox(v___x_2599_);
v_res_2603_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(v_a_2598_, v___x_3389__boxed_2602_, v_before_2600_, v_after_2601_);
lean_dec(v_after_2601_);
lean_dec(v_before_2600_);
lean_dec(v_a_2598_);
v_r_2604_ = lean_box(v_res_2603_);
return v_r_2604_;
}
}
lean_object* l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5(uint8_t v_useAfter_2605_, lean_object* v_a_2606_, lean_object* v___x_2607_, lean_object* v_x_2608_){
_start:
{
if (lean_obj_tag(v_x_2608_) == 0)
{
lean_object* v___x_2609_; 
v___x_2609_ = lean_box(0);
return v___x_2609_;
}
else
{
lean_object* v_head_2610_; lean_object* v_tail_2611_; uint8_t v___y_2613_; uint8_t v___x_2616_; 
v_head_2610_ = lean_ctor_get(v_x_2608_, 0);
v_tail_2611_ = lean_ctor_get(v_x_2608_, 1);
v___x_2616_ = 0;
if (v_useAfter_2605_ == 0)
{
uint8_t v___x_2617_; 
v___x_2617_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(v_a_2606_, v___x_2616_, v___x_2607_, v_head_2610_);
v___y_2613_ = v___x_2617_;
goto v___jp_2612_;
}
else
{
uint8_t v___x_2618_; 
v___x_2618_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(v_a_2606_, v___x_2616_, v_head_2610_, v___x_2607_);
v___y_2613_ = v___x_2618_;
goto v___jp_2612_;
}
v___jp_2612_:
{
if (v___y_2613_ == 0)
{
v_x_2608_ = v_tail_2611_;
goto _start;
}
else
{
lean_object* v___x_2615_; 
lean_inc(v_head_2610_);
v___x_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2615_, 0, v_head_2610_);
return v___x_2615_;
}
}
}
}
}
LEAN_EXPORT void l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5_0interp(lean_interpreter_value* stack)
{
uint8_t v_useAfter_2605_ = stack[0].m_num;
lean_object* v_a_2606_ = stack[1].m_obj;
lean_object* v___x_2607_ = stack[2].m_obj;
lean_object* v_x_2608_ = stack[3].m_obj;
lean_object* v_res_2619_;
v_res_2619_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5(v_useAfter_2605_, v_a_2606_, v___x_2607_, v_x_2608_);
stack->m_obj
 = v_res_2619_;
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___boxed(lean_object* v_useAfter_2620_, lean_object* v_a_2621_, lean_object* v___x_2622_, lean_object* v_x_2623_){
_start:
{
uint8_t v_useAfter_boxed_2624_; lean_object* v_res_2625_; 
v_useAfter_boxed_2624_ = lean_unbox(v_useAfter_2620_);
v_res_2625_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5(v_useAfter_boxed_2624_, v_a_2621_, v___x_2622_, v_x_2623_);
lean_dec(v_x_2623_);
lean_dec(v___x_2622_);
lean_dec(v_a_2621_);
return v_res_2625_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0(lean_object* v_mvarId_2626_, lean_object* v___y_2627_, uint8_t v_useAfter_2628_, lean_object* v_a_2629_, lean_object* v_v_2630_, uint8_t v___x_2631_, lean_object* v_toInteractiveGoalCore_2632_, lean_object* v_userName_x3f_2633_, lean_object* v_goalPrefix_2634_, lean_object* v_isInserted_x3f_2635_, lean_object* v_isRemoved_x3f_2636_, lean_object* v___lctx_u2081_2637_, lean_object* v___md_u2081_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
uint8_t v___x_2644_; 
v___x_2644_ = l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4(v_mvarId_2626_, v___y_2627_);
if (v___x_2644_ == 0)
{
lean_object* v___x_2645_; 
v___x_2645_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5(v_useAfter_2628_, v_a_2629_, v_mvarId_2626_, v___y_2627_);
if (lean_obj_tag(v___x_2645_) == 1)
{
lean_object* v_val_2646_; lean_object* v___x_2647_; 
lean_dec(v_isRemoved_x3f_2636_);
lean_dec(v_isInserted_x3f_2635_);
lean_dec_ref(v_goalPrefix_2634_);
lean_dec(v_userName_x3f_2633_);
lean_dec_ref(v_toInteractiveGoalCore_2632_);
lean_dec(v_mvarId_2626_);
v_val_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_val_2646_);
lean_dec_ref_known(v___x_2645_, 1);
v___x_2647_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(v_useAfter_2628_, v_val_2646_, v_v_2630_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
return v___x_2647_;
}
else
{
lean_dec(v___x_2645_);
lean_dec(v_v_2630_);
if (v_useAfter_2628_ == 0)
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
lean_dec(v_isRemoved_x3f_2636_);
v___x_2648_ = lean_box(v___x_2631_);
v___x_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2648_);
v___x_2650_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2650_, 0, v_toInteractiveGoalCore_2632_);
lean_ctor_set(v___x_2650_, 1, v_userName_x3f_2633_);
lean_ctor_set(v___x_2650_, 2, v_goalPrefix_2634_);
lean_ctor_set(v___x_2650_, 3, v_mvarId_2626_);
lean_ctor_set(v___x_2650_, 4, v_isInserted_x3f_2635_);
lean_ctor_set(v___x_2650_, 5, v___x_2649_);
v___x_2651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2650_);
return v___x_2651_;
}
else
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
lean_dec(v_isInserted_x3f_2635_);
v___x_2652_ = lean_box(v___x_2631_);
v___x_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2652_);
v___x_2654_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2654_, 0, v_toInteractiveGoalCore_2632_);
lean_ctor_set(v___x_2654_, 1, v_userName_x3f_2633_);
lean_ctor_set(v___x_2654_, 2, v_goalPrefix_2634_);
lean_ctor_set(v___x_2654_, 3, v_mvarId_2626_);
lean_ctor_set(v___x_2654_, 4, v___x_2653_);
lean_ctor_set(v___x_2654_, 5, v_isRemoved_x3f_2636_);
v___x_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2654_);
return v___x_2655_;
}
}
}
else
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
lean_dec(v_isInserted_x3f_2635_);
lean_dec(v_v_2630_);
v___x_2656_ = lean_box(0);
v___x_2657_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2657_, 0, v_toInteractiveGoalCore_2632_);
lean_ctor_set(v___x_2657_, 1, v_userName_x3f_2633_);
lean_ctor_set(v___x_2657_, 2, v_goalPrefix_2634_);
lean_ctor_set(v___x_2657_, 3, v_mvarId_2626_);
lean_ctor_set(v___x_2657_, 4, v___x_2656_);
lean_ctor_set(v___x_2657_, 5, v_isRemoved_x3f_2636_);
v___x_2658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2657_);
return v___x_2658_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2626_ = stack[0].m_obj;
lean_object* v___y_2627_ = stack[1].m_obj;
uint8_t v_useAfter_2628_ = stack[2].m_num;
lean_object* v_a_2629_ = stack[3].m_obj;
lean_object* v_v_2630_ = stack[4].m_obj;
uint8_t v___x_2631_ = stack[5].m_num;
lean_object* v_toInteractiveGoalCore_2632_ = stack[6].m_obj;
lean_object* v_userName_x3f_2633_ = stack[7].m_obj;
lean_object* v_goalPrefix_2634_ = stack[8].m_obj;
lean_object* v_isInserted_x3f_2635_ = stack[9].m_obj;
lean_object* v_isRemoved_x3f_2636_ = stack[10].m_obj;
lean_object* v___lctx_u2081_2637_ = stack[11].m_obj;
lean_object* v___md_u2081_2638_ = stack[12].m_obj;
lean_object* v___y_2639_ = stack[13].m_obj;
lean_object* v___y_2640_ = stack[14].m_obj;
lean_object* v___y_2641_ = stack[15].m_obj;
lean_object* v___y_2642_ = stack[16].m_obj;
lean_object* v_res_2659_;
v_res_2659_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0(v_mvarId_2626_, v___y_2627_, v_useAfter_2628_, v_a_2629_, v_v_2630_, v___x_2631_, v_toInteractiveGoalCore_2632_, v_userName_x3f_2633_, v_goalPrefix_2634_, v_isInserted_x3f_2635_, v_isRemoved_x3f_2636_, v___lctx_u2081_2637_, v___md_u2081_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
stack->m_obj
 = v_res_2659_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0___boxed(lean_object** _args){
lean_object* v_mvarId_2660_ = _args[0];
lean_object* v___y_2661_ = _args[1];
lean_object* v_useAfter_2662_ = _args[2];
lean_object* v_a_2663_ = _args[3];
lean_object* v_v_2664_ = _args[4];
lean_object* v___x_2665_ = _args[5];
lean_object* v_toInteractiveGoalCore_2666_ = _args[6];
lean_object* v_userName_x3f_2667_ = _args[7];
lean_object* v_goalPrefix_2668_ = _args[8];
lean_object* v_isInserted_x3f_2669_ = _args[9];
lean_object* v_isRemoved_x3f_2670_ = _args[10];
lean_object* v___lctx_u2081_2671_ = _args[11];
lean_object* v___md_u2081_2672_ = _args[12];
lean_object* v___y_2673_ = _args[13];
lean_object* v___y_2674_ = _args[14];
lean_object* v___y_2675_ = _args[15];
lean_object* v___y_2676_ = _args[16];
lean_object* v___y_2677_ = _args[17];
_start:
{
uint8_t v_useAfter_boxed_2678_; uint8_t v___x_3454__boxed_2679_; lean_object* v_res_2680_; 
v_useAfter_boxed_2678_ = lean_unbox(v_useAfter_2662_);
v___x_3454__boxed_2679_ = lean_unbox(v___x_2665_);
v_res_2680_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0(v_mvarId_2660_, v___y_2661_, v_useAfter_boxed_2678_, v_a_2663_, v_v_2664_, v___x_3454__boxed_2679_, v_toInteractiveGoalCore_2666_, v_userName_x3f_2667_, v_goalPrefix_2668_, v_isInserted_x3f_2669_, v_isRemoved_x3f_2670_, v___lctx_u2081_2671_, v___md_u2081_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec_ref(v___md_u2081_2672_);
lean_dec_ref(v___lctx_u2081_2671_);
lean_dec(v_a_2663_);
lean_dec(v___y_2661_);
return v_res_2680_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8(lean_object* v___y_2681_, uint8_t v_useAfter_2682_, lean_object* v_a_2683_, uint8_t v___x_2684_, size_t v_sz_2685_, size_t v_i_2686_, lean_object* v_bs_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
uint8_t v___x_2693_; 
v___x_2693_ = lean_usize_dec_lt(v_i_2686_, v_sz_2685_);
if (v___x_2693_ == 0)
{
lean_object* v___x_2694_; 
lean_dec(v_a_2683_);
lean_dec(v___y_2681_);
v___x_2694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2694_, 0, v_bs_2687_);
return v___x_2694_;
}
else
{
lean_object* v_v_2695_; lean_object* v_toInteractiveGoalCore_2696_; lean_object* v_userName_x3f_2697_; lean_object* v_goalPrefix_2698_; lean_object* v_mvarId_2699_; lean_object* v_isInserted_x3f_2700_; lean_object* v_isRemoved_x3f_2701_; lean_object* v___x_2702_; lean_object* v_bs_x27_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___f_2706_; lean_object* v___x_2707_; 
v_v_2695_ = lean_array_uget(v_bs_2687_, v_i_2686_);
v_toInteractiveGoalCore_2696_ = lean_ctor_get(v_v_2695_, 0);
lean_inc_ref(v_toInteractiveGoalCore_2696_);
v_userName_x3f_2697_ = lean_ctor_get(v_v_2695_, 1);
lean_inc(v_userName_x3f_2697_);
v_goalPrefix_2698_ = lean_ctor_get(v_v_2695_, 2);
lean_inc_ref(v_goalPrefix_2698_);
v_mvarId_2699_ = lean_ctor_get(v_v_2695_, 3);
lean_inc_n(v_mvarId_2699_, 2);
v_isInserted_x3f_2700_ = lean_ctor_get(v_v_2695_, 4);
lean_inc(v_isInserted_x3f_2700_);
v_isRemoved_x3f_2701_ = lean_ctor_get(v_v_2695_, 5);
lean_inc(v_isRemoved_x3f_2701_);
v___x_2702_ = lean_unsigned_to_nat(0u);
v_bs_x27_2703_ = lean_array_uset(v_bs_2687_, v_i_2686_, v___x_2702_);
v___x_2704_ = lean_box(v_useAfter_2682_);
v___x_2705_ = lean_box(v___x_2684_);
lean_inc(v_a_2683_);
lean_inc(v___y_2681_);
v___f_2706_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0___boxed), 18, 11);
lean_closure_set(v___f_2706_, 0, v_mvarId_2699_);
lean_closure_set(v___f_2706_, 1, v___y_2681_);
lean_closure_set(v___f_2706_, 2, v___x_2704_);
lean_closure_set(v___f_2706_, 3, v_a_2683_);
lean_closure_set(v___f_2706_, 4, v_v_2695_);
lean_closure_set(v___f_2706_, 5, v___x_2705_);
lean_closure_set(v___f_2706_, 6, v_toInteractiveGoalCore_2696_);
lean_closure_set(v___f_2706_, 7, v_userName_x3f_2697_);
lean_closure_set(v___f_2706_, 8, v_goalPrefix_2698_);
lean_closure_set(v___f_2706_, 9, v_isInserted_x3f_2700_);
lean_closure_set(v___f_2706_, 10, v_isRemoved_x3f_2701_);
v___x_2707_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(v_mvarId_2699_, v___f_2706_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; size_t v___x_2709_; size_t v___x_2710_; lean_object* v___x_2711_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
lean_inc(v_a_2708_);
lean_dec_ref_known(v___x_2707_, 1);
v___x_2709_ = ((size_t)1ULL);
v___x_2710_ = lean_usize_add(v_i_2686_, v___x_2709_);
v___x_2711_ = lean_array_uset(v_bs_x27_2703_, v_i_2686_, v_a_2708_);
v_i_2686_ = v___x_2710_;
v_bs_2687_ = v___x_2711_;
goto _start;
}
else
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
lean_dec_ref(v_bs_x27_2703_);
lean_dec(v_a_2683_);
lean_dec(v___y_2681_);
v_a_2713_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v___x_2707_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2707_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2681_ = stack[0].m_obj;
uint8_t v_useAfter_2682_ = stack[1].m_num;
lean_object* v_a_2683_ = stack[2].m_obj;
uint8_t v___x_2684_ = stack[3].m_num;
size_t v_sz_2685_ = stack[4].m_num;
size_t v_i_2686_ = stack[5].m_num;
lean_object* v_bs_2687_ = stack[6].m_obj;
lean_object* v___y_2688_ = stack[7].m_obj;
lean_object* v___y_2689_ = stack[8].m_obj;
lean_object* v___y_2690_ = stack[9].m_obj;
lean_object* v___y_2691_ = stack[10].m_obj;
lean_object* v_res_2721_;
v_res_2721_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8(v___y_2681_, v_useAfter_2682_, v_a_2683_, v___x_2684_, v_sz_2685_, v_i_2686_, v_bs_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
stack->m_obj
 = v_res_2721_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8___boxed(lean_object* v___y_2722_, lean_object* v_useAfter_2723_, lean_object* v_a_2724_, lean_object* v___x_2725_, lean_object* v_sz_2726_, lean_object* v_i_2727_, lean_object* v_bs_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
uint8_t v_useAfter_boxed_2734_; uint8_t v___x_3539__boxed_2735_; size_t v_sz_boxed_2736_; size_t v_i_boxed_2737_; lean_object* v_res_2738_; 
v_useAfter_boxed_2734_ = lean_unbox(v_useAfter_2723_);
v___x_3539__boxed_2735_ = lean_unbox(v___x_2725_);
v_sz_boxed_2736_ = lean_unbox_usize(v_sz_2726_);
lean_dec(v_sz_2726_);
v_i_boxed_2737_ = lean_unbox_usize(v_i_2727_);
lean_dec(v_i_2727_);
v_res_2738_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8(v___y_2722_, v_useAfter_boxed_2734_, v_a_2724_, v___x_3539__boxed_2735_, v_sz_boxed_2736_, v_i_boxed_2737_, v_bs_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
return v_res_2738_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7(uint8_t v_useAfter_2739_, lean_object* v_a_2740_, lean_object* v___y_2741_, uint8_t v___x_2742_, size_t v_sz_2743_, size_t v_i_2744_, lean_object* v_bs_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
uint8_t v___x_2751_; 
v___x_2751_ = lean_usize_dec_lt(v_i_2744_, v_sz_2743_);
if (v___x_2751_ == 0)
{
lean_object* v___x_2752_; 
lean_dec(v___y_2741_);
lean_dec(v_a_2740_);
v___x_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2752_, 0, v_bs_2745_);
return v___x_2752_;
}
else
{
lean_object* v_v_2753_; lean_object* v_toInteractiveGoalCore_2754_; lean_object* v_userName_x3f_2755_; lean_object* v_goalPrefix_2756_; lean_object* v_mvarId_2757_; lean_object* v_isInserted_x3f_2758_; lean_object* v_isRemoved_x3f_2759_; lean_object* v___x_2760_; lean_object* v_bs_x27_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___f_2764_; lean_object* v___x_2765_; 
v_v_2753_ = lean_array_uget(v_bs_2745_, v_i_2744_);
v_toInteractiveGoalCore_2754_ = lean_ctor_get(v_v_2753_, 0);
lean_inc_ref(v_toInteractiveGoalCore_2754_);
v_userName_x3f_2755_ = lean_ctor_get(v_v_2753_, 1);
lean_inc(v_userName_x3f_2755_);
v_goalPrefix_2756_ = lean_ctor_get(v_v_2753_, 2);
lean_inc_ref(v_goalPrefix_2756_);
v_mvarId_2757_ = lean_ctor_get(v_v_2753_, 3);
lean_inc_n(v_mvarId_2757_, 2);
v_isInserted_x3f_2758_ = lean_ctor_get(v_v_2753_, 4);
lean_inc(v_isInserted_x3f_2758_);
v_isRemoved_x3f_2759_ = lean_ctor_get(v_v_2753_, 5);
lean_inc(v_isRemoved_x3f_2759_);
v___x_2760_ = lean_unsigned_to_nat(0u);
v_bs_x27_2761_ = lean_array_uset(v_bs_2745_, v_i_2744_, v___x_2760_);
v___x_2762_ = lean_box(v_useAfter_2739_);
v___x_2763_ = lean_box(v___x_2742_);
lean_inc(v_a_2740_);
lean_inc(v___y_2741_);
v___f_2764_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0___boxed), 18, 11);
lean_closure_set(v___f_2764_, 0, v_mvarId_2757_);
lean_closure_set(v___f_2764_, 1, v___y_2741_);
lean_closure_set(v___f_2764_, 2, v___x_2762_);
lean_closure_set(v___f_2764_, 3, v_a_2740_);
lean_closure_set(v___f_2764_, 4, v_v_2753_);
lean_closure_set(v___f_2764_, 5, v___x_2763_);
lean_closure_set(v___f_2764_, 6, v_toInteractiveGoalCore_2754_);
lean_closure_set(v___f_2764_, 7, v_userName_x3f_2755_);
lean_closure_set(v___f_2764_, 8, v_goalPrefix_2756_);
lean_closure_set(v___f_2764_, 9, v_isInserted_x3f_2758_);
lean_closure_set(v___f_2764_, 10, v_isRemoved_x3f_2759_);
v___x_2765_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(v_mvarId_2757_, v___f_2764_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_a_2766_; size_t v___x_2767_; size_t v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_a_2766_);
lean_dec_ref_known(v___x_2765_, 1);
v___x_2767_ = ((size_t)1ULL);
v___x_2768_ = lean_usize_add(v_i_2744_, v___x_2767_);
v___x_2769_ = lean_array_uset(v_bs_x27_2761_, v_i_2744_, v_a_2766_);
v___x_2770_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8(v___y_2741_, v_useAfter_2739_, v_a_2740_, v___x_2742_, v_sz_2743_, v___x_2768_, v___x_2769_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
return v___x_2770_;
}
else
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
lean_dec_ref(v_bs_x27_2761_);
lean_dec(v___y_2741_);
lean_dec(v_a_2740_);
v_a_2771_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2765_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2765_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_0interp(lean_interpreter_value* stack)
{
uint8_t v_useAfter_2739_ = stack[0].m_num;
lean_object* v_a_2740_ = stack[1].m_obj;
lean_object* v___y_2741_ = stack[2].m_obj;
uint8_t v___x_2742_ = stack[3].m_num;
size_t v_sz_2743_ = stack[4].m_num;
size_t v_i_2744_ = stack[5].m_num;
lean_object* v_bs_2745_ = stack[6].m_obj;
lean_object* v___y_2746_ = stack[7].m_obj;
lean_object* v___y_2747_ = stack[8].m_obj;
lean_object* v___y_2748_ = stack[9].m_obj;
lean_object* v___y_2749_ = stack[10].m_obj;
lean_object* v_res_2779_;
v_res_2779_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7(v_useAfter_2739_, v_a_2740_, v___y_2741_, v___x_2742_, v_sz_2743_, v_i_2744_, v_bs_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
stack->m_obj
 = v_res_2779_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___boxed(lean_object* v_useAfter_2780_, lean_object* v_a_2781_, lean_object* v___y_2782_, lean_object* v___x_2783_, lean_object* v_sz_2784_, lean_object* v_i_2785_, lean_object* v_bs_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
uint8_t v_useAfter_boxed_2792_; uint8_t v___x_3639__boxed_2793_; size_t v_sz_boxed_2794_; size_t v_i_boxed_2795_; lean_object* v_res_2796_; 
v_useAfter_boxed_2792_ = lean_unbox(v_useAfter_2780_);
v___x_3639__boxed_2793_ = lean_unbox(v___x_2783_);
v_sz_boxed_2794_ = lean_unbox_usize(v_sz_2784_);
lean_dec(v_sz_2784_);
v_i_boxed_2795_ = lean_unbox_usize(v_i_2785_);
lean_dec(v_i_2785_);
v_res_2796_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7(v_useAfter_boxed_2792_, v_a_2781_, v___y_2782_, v___x_3639__boxed_2793_, v_sz_boxed_2794_, v_i_boxed_2795_, v_bs_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
return v_res_2796_;
}
}
lean_object* l_Lean_Widget_diffInteractiveGoals(uint8_t v_useAfter_2797_, lean_object* v_info_2798_, lean_object* v_igs_u2081_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_){
_start:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; uint8_t v___x_2807_; lean_object* v___y_2809_; 
v___x_2805_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2802_);
v___x_2806_ = l___private_Lean_Widget_Diff_0__Lean_Widget_showTacticDiff;
v___x_2807_ = l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(v___x_2805_, v___x_2806_);
lean_dec_ref(v___x_2805_);
if (v___x_2807_ == 0)
{
lean_object* v___x_2841_; 
lean_dec_ref(v_info_2798_);
v___x_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2841_, 0, v_igs_u2081_2799_);
return v___x_2841_;
}
else
{
if (v_useAfter_2797_ == 0)
{
lean_object* v_goalsAfter_2842_; 
v_goalsAfter_2842_ = lean_ctor_get(v_info_2798_, 4);
lean_inc(v_goalsAfter_2842_);
v___y_2809_ = v_goalsAfter_2842_;
goto v___jp_2808_;
}
else
{
lean_object* v_goalsBefore_2843_; 
v_goalsBefore_2843_ = lean_ctor_get(v_info_2798_, 2);
lean_inc(v_goalsBefore_2843_);
v___y_2809_ = v_goalsBefore_2843_;
goto v___jp_2808_;
}
}
v___jp_2808_:
{
lean_object* v_goalsBefore_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v_goalsBefore_2810_ = lean_ctor_get(v_info_2798_, 2);
lean_inc(v_goalsBefore_2810_);
lean_dec_ref(v_info_2798_);
v___x_2811_ = lean_box(1);
v___x_2812_ = l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(v___x_2811_, v_goalsBefore_2810_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; size_t v_sz_2814_; size_t v___x_2815_; lean_object* v___x_2816_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2813_);
lean_dec_ref_known(v___x_2812_, 1);
v_sz_2814_ = lean_array_size(v_igs_u2081_2799_);
v___x_2815_ = ((size_t)0ULL);
v___x_2816_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7(v_useAfter_2797_, v_a_2813_, v___y_2809_, v___x_2807_, v_sz_2814_, v___x_2815_, v_igs_u2081_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v___x_2816_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2816_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2822_; 
if (v_isShared_2820_ == 0)
{
v___x_2822_ = v___x_2819_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2817_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
v_a_2825_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2816_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2816_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2825_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
else
{
lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2840_; 
lean_dec(v___y_2809_);
lean_dec_ref(v_igs_u2081_2799_);
v_a_2833_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2835_ = v___x_2812_;
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___x_2812_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2838_; 
if (v_isShared_2836_ == 0)
{
v___x_2838_ = v___x_2835_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2833_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Widget_diffInteractiveGoals_0interp(lean_interpreter_value* stack)
{
uint8_t v_useAfter_2797_ = stack[0].m_num;
lean_object* v_info_2798_ = stack[1].m_obj;
lean_object* v_igs_u2081_2799_ = stack[2].m_obj;
lean_object* v_a_2800_ = stack[3].m_obj;
lean_object* v_a_2801_ = stack[4].m_obj;
lean_object* v_a_2802_ = stack[5].m_obj;
lean_object* v_a_2803_ = stack[6].m_obj;
lean_object* v_res_2844_;
v_res_2844_ = l_Lean_Widget_diffInteractiveGoals(v_useAfter_2797_, v_info_2798_, v_igs_u2081_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
stack->m_obj
 = v_res_2844_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_diffInteractiveGoals___boxed(lean_object* v_useAfter_2845_, lean_object* v_info_2846_, lean_object* v_igs_u2081_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_){
_start:
{
uint8_t v_useAfter_boxed_2853_; lean_object* v_res_2854_; 
v_useAfter_boxed_2853_ = lean_unbox(v_useAfter_2845_);
v_res_2854_ = l_Lean_Widget_diffInteractiveGoals(v_useAfter_boxed_2853_, v_info_2846_, v_igs_u2081_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
lean_dec(v_a_2851_);
lean_dec_ref(v_a_2850_);
lean_dec(v_a_2849_);
lean_dec_ref(v_a_2848_);
return v_res_2854_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2(lean_object* v_00_u03b4_2855_, lean_object* v_t_2856_, lean_object* v_k_2857_){
_start:
{
lean_object* v___x_2858_; 
v___x_2858_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(v_t_2856_, v_k_2857_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___boxed(lean_object* v_00_u03b4_2859_, lean_object* v_t_2860_, lean_object* v_k_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2(v_00_u03b4_2859_, v_t_2860_, v_k_2861_);
lean_dec(v_k_2861_);
lean_dec(v_t_2860_);
return v_res_2862_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3(lean_object* v_00_u03b2_2863_, lean_object* v_k_2864_, lean_object* v_t_2865_){
_start:
{
uint8_t v___x_2866_; 
v___x_2866_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_k_2864_, v_t_2865_);
return v___x_2866_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2864_ = stack[1].m_obj;
lean_object* v_t_2865_ = stack[2].m_obj;
uint8_t v_res_2867_;
v_res_2867_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3(lean_box(0), v_k_2864_, v_t_2865_);
stack->m_num = v_res_2867_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___boxed(lean_object* v_00_u03b2_2868_, lean_object* v_k_2869_, lean_object* v_t_2870_){
_start:
{
uint8_t v_res_2871_; lean_object* v_r_2872_; 
v_res_2871_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3(v_00_u03b2_2868_, v_k_2869_, v_t_2870_);
lean_dec(v_t_2870_);
lean_dec(v_k_2869_);
v_r_2872_ = lean_box(v_res_2871_);
return v_r_2872_;
}
}
lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6(lean_object* v_00_u03b1_2873_, lean_object* v_lctx_2874_, lean_object* v_localInsts_2875_, lean_object* v_x_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v___x_2882_; 
v___x_2882_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(v_lctx_2874_, v_localInsts_2875_, v_x_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
return v___x_2882_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_2874_ = stack[1].m_obj;
lean_object* v_localInsts_2875_ = stack[2].m_obj;
lean_object* v_x_2876_ = stack[3].m_obj;
lean_object* v___y_2877_ = stack[4].m_obj;
lean_object* v___y_2878_ = stack[5].m_obj;
lean_object* v___y_2879_ = stack[6].m_obj;
lean_object* v___y_2880_ = stack[7].m_obj;
lean_object* v_res_2883_;
v_res_2883_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6(lean_box(0), v_lctx_2874_, v_localInsts_2875_, v_x_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
stack->m_obj
 = v_res_2883_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___boxed(lean_object* v_00_u03b1_2884_, lean_object* v_lctx_2885_, lean_object* v_localInsts_2886_, lean_object* v_x_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6(v_00_u03b1_2884_, v_lctx_2885_, v_localInsts_2886_, v_x_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
return v_res_2893_;
}
}
lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6(lean_object* v_00_u03b1_2894_, lean_object* v_goal_2895_, lean_object* v_action_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
lean_object* v___x_2902_; 
v___x_2902_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(v_goal_2895_, v_action_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
return v___x_2902_;
}
}
LEAN_EXPORT void l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_2895_ = stack[1].m_obj;
lean_object* v_action_2896_ = stack[2].m_obj;
lean_object* v___y_2897_ = stack[3].m_obj;
lean_object* v___y_2898_ = stack[4].m_obj;
lean_object* v___y_2899_ = stack[5].m_obj;
lean_object* v___y_2900_ = stack[6].m_obj;
lean_object* v_res_2903_;
v_res_2903_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6(lean_box(0), v_goal_2895_, v_action_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
stack->m_obj
 = v_res_2903_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___boxed(lean_object* v_00_u03b1_2904_, lean_object* v_goal_2905_, lean_object* v_action_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6(v_00_u03b1_2904_, v_goal_2905_, v_action_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
return v_res_2912_;
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
