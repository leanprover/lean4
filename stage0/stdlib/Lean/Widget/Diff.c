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
lean_object* l_Lean_MetavarContext_findDecl_x3f(lean_object*, lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
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
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8(lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx(uint8_t v_x_78_){
_start:
{
switch(v_x_78_)
{
case 0:
{
lean_object* v___x_79_; 
v___x_79_ = lean_unsigned_to_nat(0u);
return v___x_79_;
}
case 1:
{
lean_object* v___x_80_; 
v___x_80_ = lean_unsigned_to_nat(1u);
return v___x_80_;
}
default: 
{
lean_object* v___x_81_; 
v___x_81_ = lean_unsigned_to_nat(2u);
return v___x_81_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx___boxed(lean_object* v_x_82_){
_start:
{
uint8_t v_x_boxed_83_; lean_object* v_res_84_; 
v_x_boxed_83_ = lean_unbox(v_x_82_);
v_res_84_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx(v_x_boxed_83_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___redArg(lean_object* v_k_85_){
_start:
{
lean_inc(v_k_85_);
return v_k_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___redArg___boxed(lean_object* v_k_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___redArg(v_k_86_);
lean_dec(v_k_86_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim(lean_object* v_motive_88_, lean_object* v_ctorIdx_89_, uint8_t v_t_90_, lean_object* v_h_91_, lean_object* v_k_92_){
_start:
{
lean_inc(v_k_92_);
return v_k_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___boxed(lean_object* v_motive_93_, lean_object* v_ctorIdx_94_, lean_object* v_t_95_, lean_object* v_h_96_, lean_object* v_k_97_){
_start:
{
uint8_t v_t_boxed_98_; lean_object* v_res_99_; 
v_t_boxed_98_ = lean_unbox(v_t_95_);
v_res_99_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim(v_motive_93_, v_ctorIdx_94_, v_t_boxed_98_, v_h_96_, v_k_97_);
lean_dec(v_k_97_);
lean_dec(v_ctorIdx_94_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___redArg(lean_object* v_change_100_){
_start:
{
lean_inc(v_change_100_);
return v_change_100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___redArg___boxed(lean_object* v_change_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___redArg(v_change_101_);
lean_dec(v_change_101_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim(lean_object* v_motive_103_, uint8_t v_t_104_, lean_object* v_h_105_, lean_object* v_change_106_){
_start:
{
lean_inc(v_change_106_);
return v_change_106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___boxed(lean_object* v_motive_107_, lean_object* v_t_108_, lean_object* v_h_109_, lean_object* v_change_110_){
_start:
{
uint8_t v_t_boxed_111_; lean_object* v_res_112_; 
v_t_boxed_111_ = lean_unbox(v_t_108_);
v_res_112_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim(v_motive_107_, v_t_boxed_111_, v_h_109_, v_change_110_);
lean_dec(v_change_110_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___redArg(lean_object* v_delete_113_){
_start:
{
lean_inc(v_delete_113_);
return v_delete_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___redArg___boxed(lean_object* v_delete_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___redArg(v_delete_114_);
lean_dec(v_delete_114_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim(lean_object* v_motive_116_, uint8_t v_t_117_, lean_object* v_h_118_, lean_object* v_delete_119_){
_start:
{
lean_inc(v_delete_119_);
return v_delete_119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___boxed(lean_object* v_motive_120_, lean_object* v_t_121_, lean_object* v_h_122_, lean_object* v_delete_123_){
_start:
{
uint8_t v_t_boxed_124_; lean_object* v_res_125_; 
v_t_boxed_124_ = lean_unbox(v_t_121_);
v_res_125_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim(v_motive_120_, v_t_boxed_124_, v_h_122_, v_delete_123_);
lean_dec(v_delete_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___redArg(lean_object* v_insert_126_){
_start:
{
lean_inc(v_insert_126_);
return v_insert_126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___redArg___boxed(lean_object* v_insert_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___redArg(v_insert_127_);
lean_dec(v_insert_127_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim(lean_object* v_motive_129_, uint8_t v_t_130_, lean_object* v_h_131_, lean_object* v_insert_132_){
_start:
{
lean_inc(v_insert_132_);
return v_insert_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___boxed(lean_object* v_motive_133_, lean_object* v_t_134_, lean_object* v_h_135_, lean_object* v_insert_136_){
_start:
{
uint8_t v_t_boxed_137_; lean_object* v_res_138_; 
v_t_boxed_137_ = lean_unbox(v_t_134_);
v_res_138_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim(v_motive_133_, v_t_boxed_137_, v_h_135_, v_insert_136_);
lean_dec(v_insert_136_);
return v_res_138_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag(uint8_t v_x_139_, uint8_t v_x_140_){
_start:
{
if (v_x_139_ == 0)
{
switch(v_x_140_)
{
case 0:
{
uint8_t v___x_141_; 
v___x_141_ = 1;
return v___x_141_;
}
case 1:
{
uint8_t v___x_142_; 
v___x_142_ = 3;
return v___x_142_;
}
default: 
{
uint8_t v___x_143_; 
v___x_143_ = 5;
return v___x_143_;
}
}
}
else
{
switch(v_x_140_)
{
case 0:
{
uint8_t v___x_144_; 
v___x_144_ = 0;
return v___x_144_;
}
case 1:
{
uint8_t v___x_145_; 
v___x_145_ = 2;
return v___x_145_;
}
default: 
{
uint8_t v___x_146_; 
v___x_146_ = 4;
return v___x_146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag___boxed(lean_object* v_x_147_, lean_object* v_x_148_){
_start:
{
uint8_t v_x_49__boxed_149_; uint8_t v_x_50__boxed_150_; uint8_t v_res_151_; lean_object* v_r_152_; 
v_x_49__boxed_149_ = lean_unbox(v_x_147_);
v_x_50__boxed_150_ = lean_unbox(v_x_148_);
v_res_151_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag(v_x_49__boxed_149_, v_x_50__boxed_150_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString(uint8_t v_x_156_){
_start:
{
switch(v_x_156_)
{
case 0:
{
lean_object* v___x_157_; 
v___x_157_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__0));
return v___x_157_;
}
case 1:
{
lean_object* v___x_158_; 
v___x_158_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__1));
return v___x_158_;
}
default: 
{
lean_object* v___x_159_; 
v___x_159_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__2));
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___boxed(lean_object* v_x_160_){
_start:
{
uint8_t v_x_31__boxed_161_; lean_object* v_res_162_; 
v_x_31__boxed_161_ = lean_unbox(v_x_160_);
v_res_162_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString(v_x_31__boxed_161_);
return v_res_162_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0(lean_object* v_x_168_, lean_object* v_y_169_){
_start:
{
uint8_t v___x_170_; 
v___x_170_ = lean_nat_dec_lt(v_x_168_, v_y_169_);
if (v___x_170_ == 0)
{
uint8_t v___x_171_; 
v___x_171_ = lean_nat_dec_eq(v_x_168_, v_y_169_);
if (v___x_171_ == 0)
{
uint8_t v___x_172_; 
v___x_172_ = 2;
return v___x_172_;
}
else
{
uint8_t v___x_173_; 
v___x_173_ = 1;
return v___x_173_;
}
}
else
{
uint8_t v___x_174_; 
v___x_174_ = 0;
return v___x_174_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0___boxed(lean_object* v_x_175_, lean_object* v_y_176_){
_start:
{
uint8_t v_res_177_; lean_object* v_r_178_; 
v_res_177_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0(v_x_175_, v_y_176_);
lean_dec(v_y_176_);
lean_dec(v_x_175_);
v_r_178_ = lean_box(v_res_177_);
return v_r_178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1(uint8_t v_b_u2082_179_, lean_object* v_x_180_){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_box(v_b_u2082_179_);
v___x_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1___boxed(lean_object* v_b_u2082_183_, lean_object* v_x_184_){
_start:
{
uint8_t v_b_u2082_boxed_185_; lean_object* v_res_186_; 
v_b_u2082_boxed_185_ = lean_unbox(v_b_u2082_183_);
v_res_186_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1(v_b_u2082_boxed_185_, v_x_184_);
lean_dec(v_x_184_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2(lean_object* v___f_187_, lean_object* v_t_188_, lean_object* v_a_189_, uint8_t v_b_u2082_190_){
_start:
{
lean_object* v___x_191_; lean_object* v___f_192_; lean_object* v___x_193_; 
v___x_191_ = lean_box(v_b_u2082_190_);
v___f_192_ = lean_alloc_closure((void*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1___boxed), 2, 1);
lean_closure_set(v___f_192_, 0, v___x_191_);
v___x_193_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v___f_187_, v_a_189_, v___f_192_, v_t_188_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2___boxed(lean_object* v___f_194_, lean_object* v_t_195_, lean_object* v_a_196_, lean_object* v_b_u2082_197_){
_start:
{
uint8_t v_b_u2082_boxed_198_; lean_object* v_res_199_; 
v_b_u2082_boxed_198_ = lean_unbox(v_b_u2082_197_);
v_res_199_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2(v___f_194_, v_t_195_, v_a_196_, v_b_u2082_boxed_198_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__5(lean_object* v___f_200_, lean_object* v___f_201_, lean_object* v_a_202_, lean_object* v_b_203_){
_start:
{
lean_object* v_changesBefore_204_; lean_object* v_changesAfter_205_; lean_object* v_changesBefore_206_; lean_object* v_changesAfter_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_216_; 
v_changesBefore_204_ = lean_ctor_get(v_a_202_, 0);
lean_inc(v_changesBefore_204_);
v_changesAfter_205_ = lean_ctor_get(v_a_202_, 1);
lean_inc(v_changesAfter_205_);
lean_dec_ref(v_a_202_);
v_changesBefore_206_ = lean_ctor_get(v_b_203_, 0);
v_changesAfter_207_ = lean_ctor_get(v_b_203_, 1);
v_isSharedCheck_216_ = !lean_is_exclusive(v_b_203_);
if (v_isSharedCheck_216_ == 0)
{
v___x_209_ = v_b_203_;
v_isShared_210_ = v_isSharedCheck_216_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_changesAfter_207_);
lean_inc(v_changesBefore_206_);
lean_dec(v_b_203_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_216_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_214_; 
v___x_211_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_200_, v_changesBefore_204_, v_changesBefore_206_);
v___x_212_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_201_, v_changesAfter_205_, v_changesAfter_207_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 1, v___x_212_);
lean_ctor_set(v___x_209_, 0, v___x_211_);
v___x_214_ = v___x_209_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_211_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v___x_212_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0(lean_object* v_x_226_){
_start:
{
lean_object* v_fst_227_; lean_object* v_snd_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_fst_227_ = lean_ctor_get(v_x_226_, 0);
v_snd_228_ = lean_ctor_get(v_x_226_, 1);
v___x_229_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__0));
v___x_230_ = l_Lean_SubExpr_Pos_toString(v_fst_227_);
v___x_231_ = lean_string_append(v___x_229_, v___x_230_);
lean_dec_ref(v___x_230_);
v___x_232_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__1));
v___x_233_ = lean_string_append(v___x_231_, v___x_232_);
v___x_234_ = lean_unbox(v_snd_228_);
v___x_235_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString(v___x_234_);
v___x_236_ = lean_string_append(v___x_233_, v___x_235_);
lean_dec_ref(v___x_235_);
v___x_237_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__2));
v___x_238_ = lean_string_append(v___x_236_, v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___boxed(lean_object* v_x_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0(v_x_239_);
lean_dec_ref(v_x_239_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1(lean_object* v_x1_241_, uint8_t v_x2_242_, lean_object* v_x3_243_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = lean_box(v_x2_242_);
v___x_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_245_, 0, v_x1_241_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
v___x_246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v_x3_243_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1___boxed(lean_object* v_x1_247_, lean_object* v_x2_248_, lean_object* v_x3_249_){
_start:
{
uint8_t v_x2_243__boxed_250_; lean_object* v_res_251_; 
v_x2_243__boxed_250_ = lean_unbox(v_x2_248_);
v_res_251_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1(v_x1_247_, v_x2_243__boxed_250_, v_x3_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2(lean_object* v___f_271_, lean_object* v___f_272_, lean_object* v_p_273_){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_274_ = lean_box(0);
v___x_275_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__9));
v___x_276_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_275_, v___f_271_, v___x_274_, v_p_273_);
v___x_277_ = l_List_mapTR_loop___redArg(v___f_272_, v___x_276_, v___x_274_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3(lean_object* v_f_280_, lean_object* v___f_281_, lean_object* v_x_282_){
_start:
{
lean_object* v_changesBefore_283_; lean_object* v_changesAfter_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v_changesBefore_283_ = lean_ctor_get(v_x_282_, 0);
lean_inc(v_changesBefore_283_);
v_changesAfter_284_ = lean_ctor_get(v_x_282_, 1);
lean_inc(v_changesAfter_284_);
lean_dec_ref(v_x_282_);
v___x_285_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__0));
lean_inc_ref(v_f_280_);
v___x_286_ = lean_apply_1(v_f_280_, v_changesBefore_283_);
lean_inc_ref(v___f_281_);
v___x_287_ = l_List_toString___redArg(v___f_281_, v___x_286_);
v___x_288_ = lean_string_append(v___x_285_, v___x_287_);
lean_dec_ref(v___x_287_);
v___x_289_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__1));
v___x_290_ = lean_string_append(v___x_288_, v___x_289_);
v___x_291_ = lean_apply_1(v_f_280_, v_changesAfter_284_);
v___x_292_ = l_List_toString___redArg(v___f_281_, v___x_291_);
v___x_293_ = lean_string_append(v___x_290_, v___x_292_);
lean_dec_ref(v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(lean_object* v_k_304_, lean_object* v_v_305_, lean_object* v_t_306_){
_start:
{
if (lean_obj_tag(v_t_306_) == 0)
{
lean_object* v_size_307_; lean_object* v_k_308_; lean_object* v_v_309_; lean_object* v_l_310_; lean_object* v_r_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_592_; 
v_size_307_ = lean_ctor_get(v_t_306_, 0);
v_k_308_ = lean_ctor_get(v_t_306_, 1);
v_v_309_ = lean_ctor_get(v_t_306_, 2);
v_l_310_ = lean_ctor_get(v_t_306_, 3);
v_r_311_ = lean_ctor_get(v_t_306_, 4);
v_isSharedCheck_592_ = !lean_is_exclusive(v_t_306_);
if (v_isSharedCheck_592_ == 0)
{
v___x_313_ = v_t_306_;
v_isShared_314_ = v_isSharedCheck_592_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_r_311_);
lean_inc(v_l_310_);
lean_inc(v_v_309_);
lean_inc(v_k_308_);
lean_inc(v_size_307_);
lean_dec(v_t_306_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_592_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
uint8_t v___x_315_; 
v___x_315_ = lean_nat_dec_lt(v_k_304_, v_k_308_);
if (v___x_315_ == 0)
{
uint8_t v___x_316_; 
v___x_316_ = lean_nat_dec_eq(v_k_304_, v_k_308_);
if (v___x_316_ == 0)
{
lean_object* v_impl_317_; lean_object* v___x_318_; 
lean_dec(v_size_307_);
v_impl_317_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_k_304_, v_v_305_, v_r_311_);
v___x_318_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_310_) == 0)
{
lean_object* v_size_319_; lean_object* v_size_320_; lean_object* v_k_321_; lean_object* v_v_322_; lean_object* v_l_323_; lean_object* v_r_324_; lean_object* v___x_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v_size_319_ = lean_ctor_get(v_l_310_, 0);
v_size_320_ = lean_ctor_get(v_impl_317_, 0);
lean_inc(v_size_320_);
v_k_321_ = lean_ctor_get(v_impl_317_, 1);
lean_inc(v_k_321_);
v_v_322_ = lean_ctor_get(v_impl_317_, 2);
lean_inc(v_v_322_);
v_l_323_ = lean_ctor_get(v_impl_317_, 3);
lean_inc(v_l_323_);
v_r_324_ = lean_ctor_get(v_impl_317_, 4);
lean_inc(v_r_324_);
v___x_325_ = lean_unsigned_to_nat(3u);
v___x_326_ = lean_nat_mul(v___x_325_, v_size_319_);
v___x_327_ = lean_nat_dec_lt(v___x_326_, v_size_320_);
lean_dec(v___x_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
lean_dec(v_r_324_);
lean_dec(v_l_323_);
lean_dec(v_v_322_);
lean_dec(v_k_321_);
v___x_328_ = lean_nat_add(v___x_318_, v_size_319_);
v___x_329_ = lean_nat_add(v___x_328_, v_size_320_);
lean_dec(v_size_320_);
lean_dec(v___x_328_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 4, v_impl_317_);
lean_ctor_set(v___x_313_, 0, v___x_329_);
v___x_331_ = v___x_313_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_329_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_k_308_);
lean_ctor_set(v_reuseFailAlloc_332_, 2, v_v_309_);
lean_ctor_set(v_reuseFailAlloc_332_, 3, v_l_310_);
lean_ctor_set(v_reuseFailAlloc_332_, 4, v_impl_317_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
else
{
lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_396_; 
v_isSharedCheck_396_ = !lean_is_exclusive(v_impl_317_);
if (v_isSharedCheck_396_ == 0)
{
lean_object* v_unused_397_; lean_object* v_unused_398_; lean_object* v_unused_399_; lean_object* v_unused_400_; lean_object* v_unused_401_; 
v_unused_397_ = lean_ctor_get(v_impl_317_, 4);
lean_dec(v_unused_397_);
v_unused_398_ = lean_ctor_get(v_impl_317_, 3);
lean_dec(v_unused_398_);
v_unused_399_ = lean_ctor_get(v_impl_317_, 2);
lean_dec(v_unused_399_);
v_unused_400_ = lean_ctor_get(v_impl_317_, 1);
lean_dec(v_unused_400_);
v_unused_401_ = lean_ctor_get(v_impl_317_, 0);
lean_dec(v_unused_401_);
v___x_334_ = v_impl_317_;
v_isShared_335_ = v_isSharedCheck_396_;
goto v_resetjp_333_;
}
else
{
lean_dec(v_impl_317_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_396_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v_size_336_; lean_object* v_k_337_; lean_object* v_v_338_; lean_object* v_l_339_; lean_object* v_r_340_; lean_object* v_size_341_; lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v_size_336_ = lean_ctor_get(v_l_323_, 0);
v_k_337_ = lean_ctor_get(v_l_323_, 1);
v_v_338_ = lean_ctor_get(v_l_323_, 2);
v_l_339_ = lean_ctor_get(v_l_323_, 3);
v_r_340_ = lean_ctor_get(v_l_323_, 4);
v_size_341_ = lean_ctor_get(v_r_324_, 0);
v___x_342_ = lean_unsigned_to_nat(2u);
v___x_343_ = lean_nat_mul(v___x_342_, v_size_341_);
v___x_344_ = lean_nat_dec_lt(v_size_336_, v___x_343_);
lean_dec(v___x_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_372_; 
lean_inc(v_r_340_);
lean_inc(v_l_339_);
lean_inc(v_v_338_);
lean_inc(v_k_337_);
v_isSharedCheck_372_ = !lean_is_exclusive(v_l_323_);
if (v_isSharedCheck_372_ == 0)
{
lean_object* v_unused_373_; lean_object* v_unused_374_; lean_object* v_unused_375_; lean_object* v_unused_376_; lean_object* v_unused_377_; 
v_unused_373_ = lean_ctor_get(v_l_323_, 4);
lean_dec(v_unused_373_);
v_unused_374_ = lean_ctor_get(v_l_323_, 3);
lean_dec(v_unused_374_);
v_unused_375_ = lean_ctor_get(v_l_323_, 2);
lean_dec(v_unused_375_);
v_unused_376_ = lean_ctor_get(v_l_323_, 1);
lean_dec(v_unused_376_);
v_unused_377_ = lean_ctor_get(v_l_323_, 0);
lean_dec(v_unused_377_);
v___x_346_ = v_l_323_;
v_isShared_347_ = v_isSharedCheck_372_;
goto v_resetjp_345_;
}
else
{
lean_dec(v_l_323_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_372_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___y_351_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_362_; 
v___x_348_ = lean_nat_add(v___x_318_, v_size_319_);
v___x_349_ = lean_nat_add(v___x_348_, v_size_320_);
lean_dec(v_size_320_);
if (lean_obj_tag(v_l_339_) == 0)
{
lean_object* v_size_370_; 
v_size_370_ = lean_ctor_get(v_l_339_, 0);
lean_inc(v_size_370_);
v___y_362_ = v_size_370_;
goto v___jp_361_;
}
else
{
lean_object* v___x_371_; 
v___x_371_ = lean_unsigned_to_nat(0u);
v___y_362_ = v___x_371_;
goto v___jp_361_;
}
v___jp_350_:
{
lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_354_ = lean_nat_add(v___y_351_, v___y_353_);
lean_dec(v___y_353_);
lean_dec(v___y_351_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 4, v_r_324_);
lean_ctor_set(v___x_346_, 3, v_r_340_);
lean_ctor_set(v___x_346_, 2, v_v_322_);
lean_ctor_set(v___x_346_, 1, v_k_321_);
lean_ctor_set(v___x_346_, 0, v___x_354_);
v___x_356_ = v___x_346_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_354_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_k_321_);
lean_ctor_set(v_reuseFailAlloc_360_, 2, v_v_322_);
lean_ctor_set(v_reuseFailAlloc_360_, 3, v_r_340_);
lean_ctor_set(v_reuseFailAlloc_360_, 4, v_r_324_);
v___x_356_ = v_reuseFailAlloc_360_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_object* v___x_358_; 
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 4, v___x_356_);
lean_ctor_set(v___x_334_, 3, v___y_352_);
lean_ctor_set(v___x_334_, 2, v_v_338_);
lean_ctor_set(v___x_334_, 1, v_k_337_);
lean_ctor_set(v___x_334_, 0, v___x_349_);
v___x_358_ = v___x_334_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_k_337_);
lean_ctor_set(v_reuseFailAlloc_359_, 2, v_v_338_);
lean_ctor_set(v_reuseFailAlloc_359_, 3, v___y_352_);
lean_ctor_set(v_reuseFailAlloc_359_, 4, v___x_356_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
v___jp_361_:
{
lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_363_ = lean_nat_add(v___x_348_, v___y_362_);
lean_dec(v___y_362_);
lean_dec(v___x_348_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 4, v_l_339_);
lean_ctor_set(v___x_313_, 0, v___x_363_);
v___x_365_ = v___x_313_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_k_308_);
lean_ctor_set(v_reuseFailAlloc_369_, 2, v_v_309_);
lean_ctor_set(v_reuseFailAlloc_369_, 3, v_l_310_);
lean_ctor_set(v_reuseFailAlloc_369_, 4, v_l_339_);
v___x_365_ = v_reuseFailAlloc_369_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_366_; 
v___x_366_ = lean_nat_add(v___x_318_, v_size_341_);
if (lean_obj_tag(v_r_340_) == 0)
{
lean_object* v_size_367_; 
v_size_367_ = lean_ctor_get(v_r_340_, 0);
lean_inc(v_size_367_);
v___y_351_ = v___x_366_;
v___y_352_ = v___x_365_;
v___y_353_ = v_size_367_;
goto v___jp_350_;
}
else
{
lean_object* v___x_368_; 
v___x_368_ = lean_unsigned_to_nat(0u);
v___y_351_ = v___x_366_;
v___y_352_ = v___x_365_;
v___y_353_ = v___x_368_;
goto v___jp_350_;
}
}
}
}
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_382_; 
lean_del_object(v___x_313_);
v___x_378_ = lean_nat_add(v___x_318_, v_size_319_);
v___x_379_ = lean_nat_add(v___x_378_, v_size_320_);
lean_dec(v_size_320_);
v___x_380_ = lean_nat_add(v___x_378_, v_size_336_);
lean_dec(v___x_378_);
lean_inc_ref(v_l_310_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 4, v_l_323_);
lean_ctor_set(v___x_334_, 3, v_l_310_);
lean_ctor_set(v___x_334_, 2, v_v_309_);
lean_ctor_set(v___x_334_, 1, v_k_308_);
lean_ctor_set(v___x_334_, 0, v___x_380_);
v___x_382_ = v___x_334_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_k_308_);
lean_ctor_set(v_reuseFailAlloc_395_, 2, v_v_309_);
lean_ctor_set(v_reuseFailAlloc_395_, 3, v_l_310_);
lean_ctor_set(v_reuseFailAlloc_395_, 4, v_l_323_);
v___x_382_ = v_reuseFailAlloc_395_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
v_isSharedCheck_389_ = !lean_is_exclusive(v_l_310_);
if (v_isSharedCheck_389_ == 0)
{
lean_object* v_unused_390_; lean_object* v_unused_391_; lean_object* v_unused_392_; lean_object* v_unused_393_; lean_object* v_unused_394_; 
v_unused_390_ = lean_ctor_get(v_l_310_, 4);
lean_dec(v_unused_390_);
v_unused_391_ = lean_ctor_get(v_l_310_, 3);
lean_dec(v_unused_391_);
v_unused_392_ = lean_ctor_get(v_l_310_, 2);
lean_dec(v_unused_392_);
v_unused_393_ = lean_ctor_get(v_l_310_, 1);
lean_dec(v_unused_393_);
v_unused_394_ = lean_ctor_get(v_l_310_, 0);
lean_dec(v_unused_394_);
v___x_384_ = v_l_310_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_dec(v_l_310_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 4, v_r_324_);
lean_ctor_set(v___x_384_, 3, v___x_382_);
lean_ctor_set(v___x_384_, 2, v_v_322_);
lean_ctor_set(v___x_384_, 1, v_k_321_);
lean_ctor_set(v___x_384_, 0, v___x_379_);
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_379_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_k_321_);
lean_ctor_set(v_reuseFailAlloc_388_, 2, v_v_322_);
lean_ctor_set(v_reuseFailAlloc_388_, 3, v___x_382_);
lean_ctor_set(v_reuseFailAlloc_388_, 4, v_r_324_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_402_; 
v_l_402_ = lean_ctor_get(v_impl_317_, 3);
lean_inc(v_l_402_);
if (lean_obj_tag(v_l_402_) == 0)
{
lean_object* v_r_403_; lean_object* v_k_404_; lean_object* v_v_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_428_; 
v_r_403_ = lean_ctor_get(v_impl_317_, 4);
v_k_404_ = lean_ctor_get(v_impl_317_, 1);
v_v_405_ = lean_ctor_get(v_impl_317_, 2);
v_isSharedCheck_428_ = !lean_is_exclusive(v_impl_317_);
if (v_isSharedCheck_428_ == 0)
{
lean_object* v_unused_429_; lean_object* v_unused_430_; 
v_unused_429_ = lean_ctor_get(v_impl_317_, 3);
lean_dec(v_unused_429_);
v_unused_430_ = lean_ctor_get(v_impl_317_, 0);
lean_dec(v_unused_430_);
v___x_407_ = v_impl_317_;
v_isShared_408_ = v_isSharedCheck_428_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_r_403_);
lean_inc(v_v_405_);
lean_inc(v_k_404_);
lean_dec(v_impl_317_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_428_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v_k_409_; lean_object* v_v_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_424_; 
v_k_409_ = lean_ctor_get(v_l_402_, 1);
v_v_410_ = lean_ctor_get(v_l_402_, 2);
v_isSharedCheck_424_ = !lean_is_exclusive(v_l_402_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; lean_object* v_unused_426_; lean_object* v_unused_427_; 
v_unused_425_ = lean_ctor_get(v_l_402_, 4);
lean_dec(v_unused_425_);
v_unused_426_ = lean_ctor_get(v_l_402_, 3);
lean_dec(v_unused_426_);
v_unused_427_ = lean_ctor_get(v_l_402_, 0);
lean_dec(v_unused_427_);
v___x_412_ = v_l_402_;
v_isShared_413_ = v_isSharedCheck_424_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_v_410_);
lean_inc(v_k_409_);
lean_dec(v_l_402_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_424_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_414_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_403_, 2);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 4, v_r_403_);
lean_ctor_set(v___x_412_, 3, v_r_403_);
lean_ctor_set(v___x_412_, 2, v_v_309_);
lean_ctor_set(v___x_412_, 1, v_k_308_);
lean_ctor_set(v___x_412_, 0, v___x_318_);
v___x_416_ = v___x_412_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_318_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_k_308_);
lean_ctor_set(v_reuseFailAlloc_423_, 2, v_v_309_);
lean_ctor_set(v_reuseFailAlloc_423_, 3, v_r_403_);
lean_ctor_set(v_reuseFailAlloc_423_, 4, v_r_403_);
v___x_416_ = v_reuseFailAlloc_423_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_418_; 
lean_inc(v_r_403_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 3, v_r_403_);
lean_ctor_set(v___x_407_, 0, v___x_318_);
v___x_418_ = v___x_407_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_318_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_k_404_);
lean_ctor_set(v_reuseFailAlloc_422_, 2, v_v_405_);
lean_ctor_set(v_reuseFailAlloc_422_, 3, v_r_403_);
lean_ctor_set(v_reuseFailAlloc_422_, 4, v_r_403_);
v___x_418_ = v_reuseFailAlloc_422_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_420_; 
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 4, v___x_418_);
lean_ctor_set(v___x_313_, 3, v___x_416_);
lean_ctor_set(v___x_313_, 2, v_v_410_);
lean_ctor_set(v___x_313_, 1, v_k_409_);
lean_ctor_set(v___x_313_, 0, v___x_414_);
v___x_420_ = v___x_313_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_k_409_);
lean_ctor_set(v_reuseFailAlloc_421_, 2, v_v_410_);
lean_ctor_set(v_reuseFailAlloc_421_, 3, v___x_416_);
lean_ctor_set(v_reuseFailAlloc_421_, 4, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
}
}
else
{
lean_object* v_r_431_; 
v_r_431_ = lean_ctor_get(v_impl_317_, 4);
lean_inc(v_r_431_);
if (lean_obj_tag(v_r_431_) == 0)
{
lean_object* v_k_432_; lean_object* v_v_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_444_; 
v_k_432_ = lean_ctor_get(v_impl_317_, 1);
v_v_433_ = lean_ctor_get(v_impl_317_, 2);
v_isSharedCheck_444_ = !lean_is_exclusive(v_impl_317_);
if (v_isSharedCheck_444_ == 0)
{
lean_object* v_unused_445_; lean_object* v_unused_446_; lean_object* v_unused_447_; 
v_unused_445_ = lean_ctor_get(v_impl_317_, 4);
lean_dec(v_unused_445_);
v_unused_446_ = lean_ctor_get(v_impl_317_, 3);
lean_dec(v_unused_446_);
v_unused_447_ = lean_ctor_get(v_impl_317_, 0);
lean_dec(v_unused_447_);
v___x_435_ = v_impl_317_;
v_isShared_436_ = v_isSharedCheck_444_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_v_433_);
lean_inc(v_k_432_);
lean_dec(v_impl_317_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_444_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_437_ = lean_unsigned_to_nat(3u);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 4, v_l_402_);
lean_ctor_set(v___x_435_, 2, v_v_309_);
lean_ctor_set(v___x_435_, 1, v_k_308_);
lean_ctor_set(v___x_435_, 0, v___x_318_);
v___x_439_ = v___x_435_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_318_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_k_308_);
lean_ctor_set(v_reuseFailAlloc_443_, 2, v_v_309_);
lean_ctor_set(v_reuseFailAlloc_443_, 3, v_l_402_);
lean_ctor_set(v_reuseFailAlloc_443_, 4, v_l_402_);
v___x_439_ = v_reuseFailAlloc_443_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
lean_object* v___x_441_; 
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 4, v_r_431_);
lean_ctor_set(v___x_313_, 3, v___x_439_);
lean_ctor_set(v___x_313_, 2, v_v_433_);
lean_ctor_set(v___x_313_, 1, v_k_432_);
lean_ctor_set(v___x_313_, 0, v___x_437_);
v___x_441_ = v___x_313_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_437_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_k_432_);
lean_ctor_set(v_reuseFailAlloc_442_, 2, v_v_433_);
lean_ctor_set(v_reuseFailAlloc_442_, 3, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_442_, 4, v_r_431_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
else
{
lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_448_ = lean_unsigned_to_nat(2u);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 4, v_impl_317_);
lean_ctor_set(v___x_313_, 3, v_r_431_);
lean_ctor_set(v___x_313_, 0, v___x_448_);
v___x_450_ = v___x_313_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_448_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_k_308_);
lean_ctor_set(v_reuseFailAlloc_451_, 2, v_v_309_);
lean_ctor_set(v_reuseFailAlloc_451_, 3, v_r_431_);
lean_ctor_set(v_reuseFailAlloc_451_, 4, v_impl_317_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
}
else
{
lean_object* v___x_453_; 
lean_dec(v_v_309_);
lean_dec(v_k_308_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 2, v_v_305_);
lean_ctor_set(v___x_313_, 1, v_k_304_);
v___x_453_ = v___x_313_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_size_307_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_k_304_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v_v_305_);
lean_ctor_set(v_reuseFailAlloc_454_, 3, v_l_310_);
lean_ctor_set(v_reuseFailAlloc_454_, 4, v_r_311_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
else
{
lean_object* v_impl_455_; lean_object* v___x_456_; 
lean_dec(v_size_307_);
v_impl_455_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_k_304_, v_v_305_, v_l_310_);
v___x_456_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_311_) == 0)
{
lean_object* v_size_457_; lean_object* v_size_458_; lean_object* v_k_459_; lean_object* v_v_460_; lean_object* v_l_461_; lean_object* v_r_462_; lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v_size_457_ = lean_ctor_get(v_r_311_, 0);
v_size_458_ = lean_ctor_get(v_impl_455_, 0);
lean_inc(v_size_458_);
v_k_459_ = lean_ctor_get(v_impl_455_, 1);
lean_inc(v_k_459_);
v_v_460_ = lean_ctor_get(v_impl_455_, 2);
lean_inc(v_v_460_);
v_l_461_ = lean_ctor_get(v_impl_455_, 3);
lean_inc(v_l_461_);
v_r_462_ = lean_ctor_get(v_impl_455_, 4);
lean_inc(v_r_462_);
v___x_463_ = lean_unsigned_to_nat(3u);
v___x_464_ = lean_nat_mul(v___x_463_, v_size_457_);
v___x_465_ = lean_nat_dec_lt(v___x_464_, v_size_458_);
lean_dec(v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
lean_dec(v_r_462_);
lean_dec(v_l_461_);
lean_dec(v_v_460_);
lean_dec(v_k_459_);
v___x_466_ = lean_nat_add(v___x_456_, v_size_458_);
lean_dec(v_size_458_);
v___x_467_ = lean_nat_add(v___x_466_, v_size_457_);
lean_dec(v___x_466_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 3, v_impl_455_);
lean_ctor_set(v___x_313_, 0, v___x_467_);
v___x_469_ = v___x_313_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v_k_308_);
lean_ctor_set(v_reuseFailAlloc_470_, 2, v_v_309_);
lean_ctor_set(v_reuseFailAlloc_470_, 3, v_impl_455_);
lean_ctor_set(v_reuseFailAlloc_470_, 4, v_r_311_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
else
{
lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_536_; 
v_isSharedCheck_536_ = !lean_is_exclusive(v_impl_455_);
if (v_isSharedCheck_536_ == 0)
{
lean_object* v_unused_537_; lean_object* v_unused_538_; lean_object* v_unused_539_; lean_object* v_unused_540_; lean_object* v_unused_541_; 
v_unused_537_ = lean_ctor_get(v_impl_455_, 4);
lean_dec(v_unused_537_);
v_unused_538_ = lean_ctor_get(v_impl_455_, 3);
lean_dec(v_unused_538_);
v_unused_539_ = lean_ctor_get(v_impl_455_, 2);
lean_dec(v_unused_539_);
v_unused_540_ = lean_ctor_get(v_impl_455_, 1);
lean_dec(v_unused_540_);
v_unused_541_ = lean_ctor_get(v_impl_455_, 0);
lean_dec(v_unused_541_);
v___x_472_ = v_impl_455_;
v_isShared_473_ = v_isSharedCheck_536_;
goto v_resetjp_471_;
}
else
{
lean_dec(v_impl_455_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_536_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v_size_474_; lean_object* v_size_475_; lean_object* v_k_476_; lean_object* v_v_477_; lean_object* v_l_478_; lean_object* v_r_479_; lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v_size_474_ = lean_ctor_get(v_l_461_, 0);
v_size_475_ = lean_ctor_get(v_r_462_, 0);
v_k_476_ = lean_ctor_get(v_r_462_, 1);
v_v_477_ = lean_ctor_get(v_r_462_, 2);
v_l_478_ = lean_ctor_get(v_r_462_, 3);
v_r_479_ = lean_ctor_get(v_r_462_, 4);
v___x_480_ = lean_unsigned_to_nat(2u);
v___x_481_ = lean_nat_mul(v___x_480_, v_size_474_);
v___x_482_ = lean_nat_dec_lt(v_size_475_, v___x_481_);
lean_dec(v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_511_; 
lean_inc(v_r_479_);
lean_inc(v_l_478_);
lean_inc(v_v_477_);
lean_inc(v_k_476_);
v_isSharedCheck_511_ = !lean_is_exclusive(v_r_462_);
if (v_isSharedCheck_511_ == 0)
{
lean_object* v_unused_512_; lean_object* v_unused_513_; lean_object* v_unused_514_; lean_object* v_unused_515_; lean_object* v_unused_516_; 
v_unused_512_ = lean_ctor_get(v_r_462_, 4);
lean_dec(v_unused_512_);
v_unused_513_ = lean_ctor_get(v_r_462_, 3);
lean_dec(v_unused_513_);
v_unused_514_ = lean_ctor_get(v_r_462_, 2);
lean_dec(v_unused_514_);
v_unused_515_ = lean_ctor_get(v_r_462_, 1);
lean_dec(v_unused_515_);
v_unused_516_ = lean_ctor_get(v_r_462_, 0);
lean_dec(v_unused_516_);
v___x_484_ = v_r_462_;
v_isShared_485_ = v_isSharedCheck_511_;
goto v_resetjp_483_;
}
else
{
lean_dec(v_r_462_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_511_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___x_499_; lean_object* v___y_501_; 
v___x_486_ = lean_nat_add(v___x_456_, v_size_458_);
lean_dec(v_size_458_);
v___x_487_ = lean_nat_add(v___x_486_, v_size_457_);
lean_dec(v___x_486_);
v___x_499_ = lean_nat_add(v___x_456_, v_size_474_);
if (lean_obj_tag(v_l_478_) == 0)
{
lean_object* v_size_509_; 
v_size_509_ = lean_ctor_get(v_l_478_, 0);
lean_inc(v_size_509_);
v___y_501_ = v_size_509_;
goto v___jp_500_;
}
else
{
lean_object* v___x_510_; 
v___x_510_ = lean_unsigned_to_nat(0u);
v___y_501_ = v___x_510_;
goto v___jp_500_;
}
v___jp_488_:
{
lean_object* v___x_492_; lean_object* v___x_494_; 
v___x_492_ = lean_nat_add(v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec(v___y_490_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 4, v_r_311_);
lean_ctor_set(v___x_484_, 3, v_r_479_);
lean_ctor_set(v___x_484_, 2, v_v_309_);
lean_ctor_set(v___x_484_, 1, v_k_308_);
lean_ctor_set(v___x_484_, 0, v___x_492_);
v___x_494_ = v___x_484_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_k_308_);
lean_ctor_set(v_reuseFailAlloc_498_, 2, v_v_309_);
lean_ctor_set(v_reuseFailAlloc_498_, 3, v_r_479_);
lean_ctor_set(v_reuseFailAlloc_498_, 4, v_r_311_);
v___x_494_ = v_reuseFailAlloc_498_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
lean_object* v___x_496_; 
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 4, v___x_494_);
lean_ctor_set(v___x_472_, 3, v___y_489_);
lean_ctor_set(v___x_472_, 2, v_v_477_);
lean_ctor_set(v___x_472_, 1, v_k_476_);
lean_ctor_set(v___x_472_, 0, v___x_487_);
v___x_496_ = v___x_472_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_487_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v_k_476_);
lean_ctor_set(v_reuseFailAlloc_497_, 2, v_v_477_);
lean_ctor_set(v_reuseFailAlloc_497_, 3, v___y_489_);
lean_ctor_set(v_reuseFailAlloc_497_, 4, v___x_494_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
v___jp_500_:
{
lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_502_ = lean_nat_add(v___x_499_, v___y_501_);
lean_dec(v___y_501_);
lean_dec(v___x_499_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 4, v_l_478_);
lean_ctor_set(v___x_313_, 3, v_l_461_);
lean_ctor_set(v___x_313_, 2, v_v_460_);
lean_ctor_set(v___x_313_, 1, v_k_459_);
lean_ctor_set(v___x_313_, 0, v___x_502_);
v___x_504_ = v___x_313_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v_k_459_);
lean_ctor_set(v_reuseFailAlloc_508_, 2, v_v_460_);
lean_ctor_set(v_reuseFailAlloc_508_, 3, v_l_461_);
lean_ctor_set(v_reuseFailAlloc_508_, 4, v_l_478_);
v___x_504_ = v_reuseFailAlloc_508_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_505_; 
v___x_505_ = lean_nat_add(v___x_456_, v_size_457_);
if (lean_obj_tag(v_r_479_) == 0)
{
lean_object* v_size_506_; 
v_size_506_ = lean_ctor_get(v_r_479_, 0);
lean_inc(v_size_506_);
v___y_489_ = v___x_504_;
v___y_490_ = v___x_505_;
v___y_491_ = v_size_506_;
goto v___jp_488_;
}
else
{
lean_object* v___x_507_; 
v___x_507_ = lean_unsigned_to_nat(0u);
v___y_489_ = v___x_504_;
v___y_490_ = v___x_505_;
v___y_491_ = v___x_507_;
goto v___jp_488_;
}
}
}
}
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
lean_del_object(v___x_313_);
v___x_517_ = lean_nat_add(v___x_456_, v_size_458_);
lean_dec(v_size_458_);
v___x_518_ = lean_nat_add(v___x_517_, v_size_457_);
lean_dec(v___x_517_);
v___x_519_ = lean_nat_add(v___x_456_, v_size_457_);
v___x_520_ = lean_nat_add(v___x_519_, v_size_475_);
lean_dec(v___x_519_);
lean_inc_ref(v_r_311_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 4, v_r_311_);
lean_ctor_set(v___x_472_, 3, v_r_462_);
lean_ctor_set(v___x_472_, 2, v_v_309_);
lean_ctor_set(v___x_472_, 1, v_k_308_);
lean_ctor_set(v___x_472_, 0, v___x_520_);
v___x_522_ = v___x_472_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_k_308_);
lean_ctor_set(v_reuseFailAlloc_535_, 2, v_v_309_);
lean_ctor_set(v_reuseFailAlloc_535_, 3, v_r_462_);
lean_ctor_set(v_reuseFailAlloc_535_, 4, v_r_311_);
v___x_522_ = v_reuseFailAlloc_535_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
v_isSharedCheck_529_ = !lean_is_exclusive(v_r_311_);
if (v_isSharedCheck_529_ == 0)
{
lean_object* v_unused_530_; lean_object* v_unused_531_; lean_object* v_unused_532_; lean_object* v_unused_533_; lean_object* v_unused_534_; 
v_unused_530_ = lean_ctor_get(v_r_311_, 4);
lean_dec(v_unused_530_);
v_unused_531_ = lean_ctor_get(v_r_311_, 3);
lean_dec(v_unused_531_);
v_unused_532_ = lean_ctor_get(v_r_311_, 2);
lean_dec(v_unused_532_);
v_unused_533_ = lean_ctor_get(v_r_311_, 1);
lean_dec(v_unused_533_);
v_unused_534_ = lean_ctor_get(v_r_311_, 0);
lean_dec(v_unused_534_);
v___x_524_ = v_r_311_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_dec(v_r_311_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 4, v___x_522_);
lean_ctor_set(v___x_524_, 3, v_l_461_);
lean_ctor_set(v___x_524_, 2, v_v_460_);
lean_ctor_set(v___x_524_, 1, v_k_459_);
lean_ctor_set(v___x_524_, 0, v___x_518_);
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_k_459_);
lean_ctor_set(v_reuseFailAlloc_528_, 2, v_v_460_);
lean_ctor_set(v_reuseFailAlloc_528_, 3, v_l_461_);
lean_ctor_set(v_reuseFailAlloc_528_, 4, v___x_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_542_; 
v_l_542_ = lean_ctor_get(v_impl_455_, 3);
lean_inc(v_l_542_);
if (lean_obj_tag(v_l_542_) == 0)
{
lean_object* v_r_543_; lean_object* v_k_544_; lean_object* v_v_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_556_; 
v_r_543_ = lean_ctor_get(v_impl_455_, 4);
v_k_544_ = lean_ctor_get(v_impl_455_, 1);
v_v_545_ = lean_ctor_get(v_impl_455_, 2);
v_isSharedCheck_556_ = !lean_is_exclusive(v_impl_455_);
if (v_isSharedCheck_556_ == 0)
{
lean_object* v_unused_557_; lean_object* v_unused_558_; 
v_unused_557_ = lean_ctor_get(v_impl_455_, 3);
lean_dec(v_unused_557_);
v_unused_558_ = lean_ctor_get(v_impl_455_, 0);
lean_dec(v_unused_558_);
v___x_547_ = v_impl_455_;
v_isShared_548_ = v_isSharedCheck_556_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_r_543_);
lean_inc(v_v_545_);
lean_inc(v_k_544_);
lean_dec(v_impl_455_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_556_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_549_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_543_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 3, v_r_543_);
lean_ctor_set(v___x_547_, 2, v_v_309_);
lean_ctor_set(v___x_547_, 1, v_k_308_);
lean_ctor_set(v___x_547_, 0, v___x_456_);
v___x_551_ = v___x_547_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_456_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_k_308_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v_v_309_);
lean_ctor_set(v_reuseFailAlloc_555_, 3, v_r_543_);
lean_ctor_set(v_reuseFailAlloc_555_, 4, v_r_543_);
v___x_551_ = v_reuseFailAlloc_555_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_553_; 
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 4, v___x_551_);
lean_ctor_set(v___x_313_, 3, v_l_542_);
lean_ctor_set(v___x_313_, 2, v_v_545_);
lean_ctor_set(v___x_313_, 1, v_k_544_);
lean_ctor_set(v___x_313_, 0, v___x_549_);
v___x_553_ = v___x_313_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_k_544_);
lean_ctor_set(v_reuseFailAlloc_554_, 2, v_v_545_);
lean_ctor_set(v_reuseFailAlloc_554_, 3, v_l_542_);
lean_ctor_set(v_reuseFailAlloc_554_, 4, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
else
{
lean_object* v_r_559_; 
v_r_559_ = lean_ctor_get(v_impl_455_, 4);
lean_inc(v_r_559_);
if (lean_obj_tag(v_r_559_) == 0)
{
lean_object* v_k_560_; lean_object* v_v_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_584_; 
v_k_560_ = lean_ctor_get(v_impl_455_, 1);
v_v_561_ = lean_ctor_get(v_impl_455_, 2);
v_isSharedCheck_584_ = !lean_is_exclusive(v_impl_455_);
if (v_isSharedCheck_584_ == 0)
{
lean_object* v_unused_585_; lean_object* v_unused_586_; lean_object* v_unused_587_; 
v_unused_585_ = lean_ctor_get(v_impl_455_, 4);
lean_dec(v_unused_585_);
v_unused_586_ = lean_ctor_get(v_impl_455_, 3);
lean_dec(v_unused_586_);
v_unused_587_ = lean_ctor_get(v_impl_455_, 0);
lean_dec(v_unused_587_);
v___x_563_ = v_impl_455_;
v_isShared_564_ = v_isSharedCheck_584_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_v_561_);
lean_inc(v_k_560_);
lean_dec(v_impl_455_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_584_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v_k_565_; lean_object* v_v_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_580_; 
v_k_565_ = lean_ctor_get(v_r_559_, 1);
v_v_566_ = lean_ctor_get(v_r_559_, 2);
v_isSharedCheck_580_ = !lean_is_exclusive(v_r_559_);
if (v_isSharedCheck_580_ == 0)
{
lean_object* v_unused_581_; lean_object* v_unused_582_; lean_object* v_unused_583_; 
v_unused_581_ = lean_ctor_get(v_r_559_, 4);
lean_dec(v_unused_581_);
v_unused_582_ = lean_ctor_get(v_r_559_, 3);
lean_dec(v_unused_582_);
v_unused_583_ = lean_ctor_get(v_r_559_, 0);
lean_dec(v_unused_583_);
v___x_568_ = v_r_559_;
v_isShared_569_ = v_isSharedCheck_580_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_v_566_);
lean_inc(v_k_565_);
lean_dec(v_r_559_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_580_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_570_ = lean_unsigned_to_nat(3u);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 4, v_l_542_);
lean_ctor_set(v___x_568_, 3, v_l_542_);
lean_ctor_set(v___x_568_, 2, v_v_561_);
lean_ctor_set(v___x_568_, 1, v_k_560_);
lean_ctor_set(v___x_568_, 0, v___x_456_);
v___x_572_ = v___x_568_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_456_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_k_560_);
lean_ctor_set(v_reuseFailAlloc_579_, 2, v_v_561_);
lean_ctor_set(v_reuseFailAlloc_579_, 3, v_l_542_);
lean_ctor_set(v_reuseFailAlloc_579_, 4, v_l_542_);
v___x_572_ = v_reuseFailAlloc_579_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v___x_574_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 4, v_l_542_);
lean_ctor_set(v___x_563_, 2, v_v_309_);
lean_ctor_set(v___x_563_, 1, v_k_308_);
lean_ctor_set(v___x_563_, 0, v___x_456_);
v___x_574_ = v___x_563_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_456_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_k_308_);
lean_ctor_set(v_reuseFailAlloc_578_, 2, v_v_309_);
lean_ctor_set(v_reuseFailAlloc_578_, 3, v_l_542_);
lean_ctor_set(v_reuseFailAlloc_578_, 4, v_l_542_);
v___x_574_ = v_reuseFailAlloc_578_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_576_; 
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 4, v___x_574_);
lean_ctor_set(v___x_313_, 3, v___x_572_);
lean_ctor_set(v___x_313_, 2, v_v_566_);
lean_ctor_set(v___x_313_, 1, v_k_565_);
lean_ctor_set(v___x_313_, 0, v___x_570_);
v___x_576_ = v___x_313_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_570_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v_k_565_);
lean_ctor_set(v_reuseFailAlloc_577_, 2, v_v_566_);
lean_ctor_set(v_reuseFailAlloc_577_, 3, v___x_572_);
lean_ctor_set(v_reuseFailAlloc_577_, 4, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
}
}
else
{
lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_588_ = lean_unsigned_to_nat(2u);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 4, v_r_559_);
lean_ctor_set(v___x_313_, 3, v_impl_455_);
lean_ctor_set(v___x_313_, 0, v___x_588_);
v___x_590_ = v___x_313_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_k_308_);
lean_ctor_set(v_reuseFailAlloc_591_, 2, v_v_309_);
lean_ctor_set(v_reuseFailAlloc_591_, 3, v_impl_455_);
lean_ctor_set(v_reuseFailAlloc_591_, 4, v_r_559_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = lean_unsigned_to_nat(1u);
v___x_594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
lean_ctor_set(v___x_594_, 1, v_k_304_);
lean_ctor_set(v___x_594_, 2, v_v_305_);
lean_ctor_set(v___x_594_, 3, v_t_306_);
lean_ctor_set(v___x_594_, 4, v_t_306_);
return v___x_594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange(lean_object* v_p_595_, uint8_t v_d_596_, lean_object* v_00_u03b4_597_){
_start:
{
lean_object* v_changesBefore_598_; lean_object* v_changesAfter_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_608_; 
v_changesBefore_598_ = lean_ctor_get(v_00_u03b4_597_, 0);
v_changesAfter_599_ = lean_ctor_get(v_00_u03b4_597_, 1);
v_isSharedCheck_608_ = !lean_is_exclusive(v_00_u03b4_597_);
if (v_isSharedCheck_608_ == 0)
{
v___x_601_ = v_00_u03b4_597_;
v_isShared_602_ = v_isSharedCheck_608_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_changesAfter_599_);
lean_inc(v_changesBefore_598_);
lean_dec(v_00_u03b4_597_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_608_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_603_ = lean_box(v_d_596_);
v___x_604_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_p_595_, v___x_603_, v_changesBefore_598_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v___x_604_);
v___x_606_ = v___x_601_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_604_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_changesAfter_599_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange___boxed(lean_object* v_p_609_, lean_object* v_d_610_, lean_object* v_00_u03b4_611_){
_start:
{
uint8_t v_d_boxed_612_; lean_object* v_res_613_; 
v_d_boxed_612_ = lean_unbox(v_d_610_);
v_res_613_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange(v_p_609_, v_d_boxed_612_, v_00_u03b4_611_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0(lean_object* v_00_u03b2_614_, lean_object* v_k_615_, lean_object* v_v_616_, lean_object* v_t_617_, lean_object* v_hl_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_k_615_, v_v_616_, v_t_617_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertAfterChange(lean_object* v_p_620_, uint8_t v_d_621_, lean_object* v_00_u03b4_622_){
_start:
{
lean_object* v_changesBefore_623_; lean_object* v_changesAfter_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_633_; 
v_changesBefore_623_ = lean_ctor_get(v_00_u03b4_622_, 0);
v_changesAfter_624_ = lean_ctor_get(v_00_u03b4_622_, 1);
v_isSharedCheck_633_ = !lean_is_exclusive(v_00_u03b4_622_);
if (v_isSharedCheck_633_ == 0)
{
v___x_626_ = v_00_u03b4_622_;
v_isShared_627_ = v_isSharedCheck_633_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_changesAfter_624_);
lean_inc(v_changesBefore_623_);
lean_dec(v_00_u03b4_622_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_633_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_628_ = lean_box(v_d_621_);
v___x_629_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_p_620_, v___x_628_, v_changesAfter_624_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 1, v___x_629_);
v___x_631_ = v___x_626_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_changesBefore_623_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v___x_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertAfterChange___boxed(lean_object* v_p_634_, lean_object* v_d_635_, lean_object* v_00_u03b4_636_){
_start:
{
uint8_t v_d_boxed_637_; lean_object* v_res_638_; 
v_d_boxed_637_ = lean_unbox(v_d_635_);
v_res_638_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertAfterChange(v_p_634_, v_d_boxed_637_, v_00_u03b4_636_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(lean_object* v_before_639_, lean_object* v_after_640_, uint8_t v_d_641_){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_642_ = lean_box(1);
v___x_643_ = lean_box(v_d_641_);
v___x_644_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_before_639_, v___x_643_, v___x_642_);
v___x_645_ = lean_box(v_d_641_);
v___x_646_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_after_640_, v___x_645_, v___x_642_);
v___x_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_644_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos___boxed(lean_object* v_before_648_, lean_object* v_after_649_, lean_object* v_d_650_){
_start:
{
uint8_t v_d_boxed_651_; lean_object* v_res_652_; 
v_d_boxed_651_ = lean_unbox(v_d_650_);
v_res_652_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v_before_648_, v_after_649_, v_d_boxed_651_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(lean_object* v_before_653_, lean_object* v_after_654_, uint8_t v_d_655_){
_start:
{
lean_object* v_pos_656_; lean_object* v_pos_657_; lean_object* v___x_658_; 
v_pos_656_ = lean_ctor_get(v_before_653_, 1);
lean_inc(v_pos_656_);
lean_dec_ref(v_before_653_);
v_pos_657_ = lean_ctor_get(v_after_654_, 1);
lean_inc(v_pos_657_);
lean_dec_ref(v_after_654_);
v___x_658_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v_pos_656_, v_pos_657_, v_d_655_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange___boxed(lean_object* v_before_659_, lean_object* v_after_660_, lean_object* v_d_661_){
_start:
{
uint8_t v_d_boxed_662_; lean_object* v_res_663_; 
v_d_boxed_662_ = lean_unbox(v_d_661_);
v_res_663_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_659_, v_after_660_, v_d_boxed_662_);
return v_res_663_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(lean_object* v_d_664_){
_start:
{
lean_object* v_changesAfter_665_; 
v_changesAfter_665_ = lean_ctor_get(v_d_664_, 1);
if (lean_obj_tag(v_changesAfter_665_) == 0)
{
uint8_t v___x_666_; 
v___x_666_ = 0;
return v___x_666_;
}
else
{
lean_object* v_changesBefore_667_; 
v_changesBefore_667_ = lean_ctor_get(v_d_664_, 0);
if (lean_obj_tag(v_changesBefore_667_) == 0)
{
uint8_t v___x_668_; 
v___x_668_ = 0;
return v___x_668_;
}
else
{
uint8_t v___x_669_; 
v___x_669_ = 1;
return v___x_669_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty___boxed(lean_object* v_d_670_){
_start:
{
uint8_t v_res_671_; lean_object* v_r_672_; 
v_res_671_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_d_670_);
lean_dec_ref(v_d_670_);
v_r_672_ = lean_box(v_res_671_);
return v_r_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0(lean_object* v_k_673_, lean_object* v_b_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v___x_680_; 
lean_inc(v___y_678_);
lean_inc_ref(v___y_677_);
lean_inc(v___y_676_);
lean_inc_ref(v___y_675_);
v___x_680_ = lean_apply_6(v_k_673_, v_b_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, lean_box(0));
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0___boxed(lean_object* v_k_681_, lean_object* v_b_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0(v_k_681_, v_b_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(lean_object* v_name_689_, uint8_t v_bi_690_, lean_object* v_type_691_, lean_object* v_k_692_, uint8_t v_kind_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v___f_699_; lean_object* v___x_700_; 
v___f_699_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_699_, 0, v_k_692_);
v___x_700_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_689_, v_bi_690_, v_type_691_, v___f_699_, v_kind_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_700_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_700_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
v_a_709_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_700_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_700_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___boxed(lean_object* v_name_717_, lean_object* v_bi_718_, lean_object* v_type_719_, lean_object* v_k_720_, lean_object* v_kind_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
uint8_t v_bi_boxed_727_; uint8_t v_kind_boxed_728_; lean_object* v_res_729_; 
v_bi_boxed_727_ = lean_unbox(v_bi_718_);
v_kind_boxed_728_ = lean_unbox(v_kind_721_);
v_res_729_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_name_717_, v_bi_boxed_727_, v_type_719_, v_k_720_, v_kind_boxed_728_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6(lean_object* v_00_u03b1_730_, lean_object* v_name_731_, uint8_t v_bi_732_, lean_object* v_type_733_, lean_object* v_k_734_, uint8_t v_kind_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_name_731_, v_bi_732_, v_type_733_, v_k_734_, v_kind_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___boxed(lean_object* v_00_u03b1_742_, lean_object* v_name_743_, lean_object* v_bi_744_, lean_object* v_type_745_, lean_object* v_k_746_, lean_object* v_kind_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
uint8_t v_bi_boxed_753_; uint8_t v_kind_boxed_754_; lean_object* v_res_755_; 
v_bi_boxed_753_ = lean_unbox(v_bi_744_);
v_kind_boxed_754_ = lean_unbox(v_kind_747_);
v_res_755_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6(v_00_u03b1_742_, v_name_743_, v_bi_boxed_753_, v_type_745_, v_k_746_, v_kind_boxed_754_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(lean_object* v_msgData_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v___x_762_; lean_object* v_env_763_; lean_object* v___x_764_; lean_object* v_mctx_765_; lean_object* v_lctx_766_; lean_object* v_options_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_762_ = lean_st_ref_get(v___y_760_);
v_env_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc_ref(v_env_763_);
lean_dec(v___x_762_);
v___x_764_ = lean_st_ref_get(v___y_758_);
v_mctx_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc_ref(v_mctx_765_);
lean_dec(v___x_764_);
v_lctx_766_ = lean_ctor_get(v___y_757_, 2);
v_options_767_ = lean_ctor_get(v___y_759_, 2);
lean_inc_ref(v_options_767_);
lean_inc_ref(v_lctx_766_);
v___x_768_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_768_, 0, v_env_763_);
lean_ctor_set(v___x_768_, 1, v_mctx_765_);
lean_ctor_set(v___x_768_, 2, v_lctx_766_);
lean_ctor_set(v___x_768_, 3, v_options_767_);
v___x_769_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
lean_ctor_set(v___x_769_, 1, v_msgData_756_);
v___x_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4___boxed(lean_object* v_msgData_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(v_msgData_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(lean_object* v_msg_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_ref_784_; lean_object* v___x_785_; lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_794_; 
v_ref_784_ = lean_ctor_get(v___y_781_, 5);
v___x_785_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(v_msg_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
v_a_786_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_794_ == 0)
{
v___x_788_ = v___x_785_;
v_isShared_789_ = v_isSharedCheck_794_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_794_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v___x_792_; 
lean_inc(v_ref_784_);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v_ref_784_);
lean_ctor_set(v___x_790_, 1, v_a_786_);
if (v_isShared_789_ == 0)
{
lean_ctor_set_tag(v___x_788_, 1);
lean_ctor_set(v___x_788_, 0, v___x_790_);
v___x_792_ = v___x_788_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg___boxed(lean_object* v_msg_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v_msg_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(lean_object* v_x_802_, lean_object* v_x_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
if (lean_obj_tag(v_x_802_) == 0)
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = l_List_reverse___redArg(v_x_803_);
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
return v___x_810_;
}
else
{
lean_object* v_head_811_; lean_object* v_tail_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_830_; 
v_head_811_ = lean_ctor_get(v_x_802_, 0);
v_tail_812_ = lean_ctor_get(v_x_802_, 1);
v_isSharedCheck_830_ = !lean_is_exclusive(v_x_802_);
if (v_isSharedCheck_830_ == 0)
{
v___x_814_ = v_x_802_;
v_isShared_815_ = v_isSharedCheck_830_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_tail_812_);
lean_inc(v_head_811_);
lean_dec(v_x_802_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_830_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_Meta_getFVarFromUserName(v_head_811_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_819_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
lean_dec_ref_known(v___x_816_, 1);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 1, v_x_803_);
lean_ctor_set(v___x_814_, 0, v_a_817_);
v___x_819_ = v___x_814_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_817_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_x_803_);
v___x_819_ = v_reuseFailAlloc_821_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
v_x_802_ = v_tail_812_;
v_x_803_ = v___x_819_;
goto _start;
}
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_del_object(v___x_814_);
lean_dec(v_tail_812_);
lean_dec(v_x_803_);
v_a_822_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_816_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_816_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2___boxed(lean_object* v_x_831_, lean_object* v_x_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(v_x_831_, v_x_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(lean_object* v_upperBound_839_, lean_object* v_before_840_, lean_object* v_a_841_, lean_object* v_b_842_){
_start:
{
uint8_t v___x_844_; 
v___x_844_ = lean_nat_dec_lt(v_a_841_, v_upperBound_839_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; 
lean_dec(v_a_841_);
lean_dec_ref(v_before_840_);
v___x_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_845_, 0, v_b_842_);
return v___x_845_;
}
else
{
lean_object* v_pos_846_; lean_object* v___x_847_; uint8_t v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v_pos_846_ = lean_ctor_get(v_before_840_, 1);
lean_inc(v_pos_846_);
lean_inc(v_a_841_);
v___x_847_ = l_Lean_SubExpr_Pos_pushNthBindingDomain(v_a_841_, v_pos_846_);
v___x_848_ = 1;
v___x_849_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange(v___x_847_, v___x_848_, v_b_842_);
v___x_850_ = lean_unsigned_to_nat(1u);
v___x_851_ = lean_nat_add(v_a_841_, v___x_850_);
lean_dec(v_a_841_);
v_a_841_ = v___x_851_;
v_b_842_ = v___x_849_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg___boxed(lean_object* v_upperBound_853_, lean_object* v_before_854_, lean_object* v_a_855_, lean_object* v_b_856_, lean_object* v___y_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v_upperBound_853_, v_before_854_, v_a_855_, v_b_856_);
lean_dec(v_upperBound_853_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0(lean_object* v_x_859_, lean_object* v_x_860_){
_start:
{
if (lean_obj_tag(v_x_859_) == 0)
{
lean_object* v___x_861_; 
v___x_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_861_, 0, v_x_860_);
return v___x_861_;
}
else
{
if (lean_obj_tag(v_x_860_) == 0)
{
lean_object* v___x_862_; 
v___x_862_ = lean_box(0);
return v___x_862_;
}
else
{
lean_object* v_head_863_; lean_object* v_tail_864_; lean_object* v_head_865_; lean_object* v_tail_866_; uint8_t v___x_867_; 
v_head_863_ = lean_ctor_get(v_x_859_, 0);
v_tail_864_ = lean_ctor_get(v_x_859_, 1);
v_head_865_ = lean_ctor_get(v_x_860_, 0);
lean_inc(v_head_865_);
v_tail_866_ = lean_ctor_get(v_x_860_, 1);
lean_inc(v_tail_866_);
lean_dec_ref_known(v_x_860_, 2);
v___x_867_ = lean_name_eq(v_head_863_, v_head_865_);
lean_dec(v_head_865_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; 
lean_dec(v_tail_866_);
v___x_868_ = lean_box(0);
return v___x_868_;
}
else
{
v_x_859_ = v_tail_864_;
v_x_860_ = v_tail_866_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0___boxed(lean_object* v_x_870_, lean_object* v_x_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0(v_x_870_, v_x_871_);
lean_dec(v_x_870_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0(lean_object* v_l_u2081_873_, lean_object* v_l_u2082_874_){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_875_ = l_List_reverse___redArg(v_l_u2081_873_);
v___x_876_ = l_List_reverse___redArg(v_l_u2082_874_);
v___x_877_ = l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0(v___x_875_, v___x_876_);
lean_dec(v___x_875_);
if (lean_obj_tag(v___x_877_) == 0)
{
return v___x_877_;
}
else
{
lean_object* v_val_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_886_; 
v_val_878_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_886_ == 0)
{
v___x_880_ = v___x_877_;
v_isShared_881_ = v_isSharedCheck_886_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_val_878_);
lean_dec(v___x_877_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_886_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_882_ = l_List_reverse___redArg(v_val_878_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v___x_882_);
v___x_884_ = v___x_880_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(uint8_t v_b_u2082_887_, lean_object* v_k_888_, lean_object* v_t_889_){
_start:
{
if (lean_obj_tag(v_t_889_) == 0)
{
lean_object* v_size_890_; lean_object* v_k_891_; lean_object* v_v_892_; lean_object* v_l_893_; lean_object* v_r_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_908_; 
v_size_890_ = lean_ctor_get(v_t_889_, 0);
v_k_891_ = lean_ctor_get(v_t_889_, 1);
v_v_892_ = lean_ctor_get(v_t_889_, 2);
v_l_893_ = lean_ctor_get(v_t_889_, 3);
v_r_894_ = lean_ctor_get(v_t_889_, 4);
v_isSharedCheck_908_ = !lean_is_exclusive(v_t_889_);
if (v_isSharedCheck_908_ == 0)
{
v___x_896_ = v_t_889_;
v_isShared_897_ = v_isSharedCheck_908_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_r_894_);
lean_inc(v_l_893_);
lean_inc(v_v_892_);
lean_inc(v_k_891_);
lean_inc(v_size_890_);
lean_dec(v_t_889_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_908_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
uint8_t v___x_898_; 
v___x_898_ = lean_nat_dec_lt(v_k_888_, v_k_891_);
if (v___x_898_ == 0)
{
uint8_t v___x_899_; 
v___x_899_ = lean_nat_dec_eq(v_k_888_, v_k_891_);
if (v___x_899_ == 0)
{
lean_object* v_impl_900_; lean_object* v___x_901_; 
lean_del_object(v___x_896_);
lean_dec(v_size_890_);
v_impl_900_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_887_, v_k_888_, v_r_894_);
v___x_901_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_891_, v_v_892_, v_l_893_, v_impl_900_);
return v___x_901_;
}
else
{
lean_object* v___x_902_; lean_object* v___x_904_; 
lean_dec(v_v_892_);
lean_dec(v_k_891_);
v___x_902_ = lean_box(v_b_u2082_887_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 2, v___x_902_);
lean_ctor_set(v___x_896_, 1, v_k_888_);
v___x_904_ = v___x_896_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_size_890_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_k_888_);
lean_ctor_set(v_reuseFailAlloc_905_, 2, v___x_902_);
lean_ctor_set(v_reuseFailAlloc_905_, 3, v_l_893_);
lean_ctor_set(v_reuseFailAlloc_905_, 4, v_r_894_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
else
{
lean_object* v_impl_906_; lean_object* v___x_907_; 
lean_del_object(v___x_896_);
lean_dec(v_size_890_);
v_impl_906_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_887_, v_k_888_, v_l_893_);
v___x_907_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_891_, v_v_892_, v_impl_906_, v_r_894_);
return v___x_907_;
}
}
}
else
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_909_ = lean_unsigned_to_nat(1u);
v___x_910_ = lean_box(v_b_u2082_887_);
v___x_911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set(v___x_911_, 1, v_k_888_);
lean_ctor_set(v___x_911_, 2, v___x_910_);
lean_ctor_set(v___x_911_, 3, v_t_889_);
lean_ctor_set(v___x_911_, 4, v_t_889_);
return v___x_911_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg___boxed(lean_object* v_b_u2082_912_, lean_object* v_k_913_, lean_object* v_t_914_){
_start:
{
uint8_t v_b_u2082_boxed_915_; lean_object* v_res_916_; 
v_b_u2082_boxed_915_ = lean_unbox(v_b_u2082_912_);
v_res_916_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_boxed_915_, v_k_913_, v_t_914_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(lean_object* v_init_917_, lean_object* v_x_918_){
_start:
{
if (lean_obj_tag(v_x_918_) == 0)
{
lean_object* v_k_919_; lean_object* v_v_920_; lean_object* v_l_921_; lean_object* v_r_922_; lean_object* v___x_923_; uint8_t v___x_924_; lean_object* v___x_925_; 
v_k_919_ = lean_ctor_get(v_x_918_, 1);
lean_inc(v_k_919_);
v_v_920_ = lean_ctor_get(v_x_918_, 2);
lean_inc(v_v_920_);
v_l_921_ = lean_ctor_get(v_x_918_, 3);
lean_inc(v_l_921_);
v_r_922_ = lean_ctor_get(v_x_918_, 4);
lean_inc(v_r_922_);
lean_dec_ref_known(v_x_918_, 5);
v___x_923_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_init_917_, v_l_921_);
v___x_924_ = lean_unbox(v_v_920_);
lean_dec(v_v_920_);
v___x_925_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v___x_924_, v_k_919_, v___x_923_);
v_init_917_ = v___x_925_;
v_x_918_ = v_r_922_;
goto _start;
}
else
{
return v_init_917_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(lean_object* v_as_927_, size_t v_i_928_, size_t v_stop_929_, lean_object* v_b_930_){
_start:
{
uint8_t v___x_931_; 
v___x_931_ = lean_usize_dec_eq(v_i_928_, v_stop_929_);
if (v___x_931_ == 0)
{
lean_object* v_changesBefore_932_; lean_object* v_changesAfter_933_; lean_object* v___x_934_; lean_object* v_changesBefore_935_; lean_object* v_changesAfter_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_948_; 
v_changesBefore_932_ = lean_ctor_get(v_b_930_, 0);
lean_inc(v_changesBefore_932_);
v_changesAfter_933_ = lean_ctor_get(v_b_930_, 1);
lean_inc(v_changesAfter_933_);
lean_dec_ref(v_b_930_);
v___x_934_ = lean_array_uget(v_as_927_, v_i_928_);
v_changesBefore_935_ = lean_ctor_get(v___x_934_, 0);
v_changesAfter_936_ = lean_ctor_get(v___x_934_, 1);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_948_ == 0)
{
v___x_938_ = v___x_934_;
v_isShared_939_ = v_isSharedCheck_948_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_changesAfter_936_);
lean_inc(v_changesBefore_935_);
lean_dec(v___x_934_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_948_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_940_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesBefore_932_, v_changesBefore_935_);
v___x_941_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesAfter_933_, v_changesAfter_936_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 1, v___x_941_);
lean_ctor_set(v___x_938_, 0, v___x_940_);
v___x_943_ = v___x_938_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v___x_941_);
v___x_943_ = v_reuseFailAlloc_947_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
size_t v___x_944_; size_t v___x_945_; 
v___x_944_ = ((size_t)1ULL);
v___x_945_ = lean_usize_add(v_i_928_, v___x_944_);
v_i_928_ = v___x_945_;
v_b_930_ = v___x_943_;
goto _start;
}
}
}
else
{
return v_b_930_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10___boxed(lean_object* v_as_949_, lean_object* v_i_950_, lean_object* v_stop_951_, lean_object* v_b_952_){
_start:
{
size_t v_i_boxed_953_; size_t v_stop_boxed_954_; lean_object* v_res_955_; 
v_i_boxed_953_ = lean_unbox_usize(v_i_950_);
lean_dec(v_i_950_);
v_stop_boxed_954_ = lean_unbox_usize(v_stop_951_);
lean_dec(v_stop_951_);
v_res_955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_as_949_, v_i_boxed_953_, v_stop_boxed_954_, v_b_952_);
lean_dec_ref(v_as_949_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(lean_object* v_x_956_, lean_object* v_x_957_, lean_object* v_x_958_){
_start:
{
if (lean_obj_tag(v_x_956_) == 5)
{
lean_object* v_fn_959_; lean_object* v_arg_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v_fn_959_ = lean_ctor_get(v_x_956_, 0);
lean_inc_ref(v_fn_959_);
v_arg_960_ = lean_ctor_get(v_x_956_, 1);
lean_inc_ref(v_arg_960_);
lean_dec_ref_known(v_x_956_, 2);
v___x_961_ = lean_array_set(v_x_957_, v_x_958_, v_arg_960_);
v___x_962_ = lean_unsigned_to_nat(1u);
v___x_963_ = lean_nat_sub(v_x_958_, v___x_962_);
lean_dec(v_x_958_);
v_x_956_ = v_fn_959_;
v_x_957_ = v___x_961_;
v_x_958_ = v___x_963_;
goto _start;
}
else
{
lean_object* v___x_965_; 
lean_dec(v_x_958_);
v___x_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_965_, 0, v_x_956_);
lean_ctor_set(v___x_965_, 1, v_x_957_);
return v___x_965_;
}
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0(void){
_start:
{
lean_object* v___x_966_; lean_object* v_dummy_967_; 
v___x_966_ = lean_box(0);
v_dummy_967_ = l_Lean_Expr_sort___override(v___x_966_);
return v_dummy_967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(lean_object* v_snd_968_, lean_object* v_before_969_, lean_object* v_after_970_, size_t v_sz_971_, size_t v_i_972_, lean_object* v_bs_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
uint8_t v___x_979_; 
v___x_979_ = lean_usize_dec_lt(v_i_972_, v_sz_971_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; 
v___x_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_980_, 0, v_bs_973_);
return v___x_980_;
}
else
{
lean_object* v_v_981_; lean_object* v_fst_982_; lean_object* v_snd_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_1013_; 
v_v_981_ = lean_array_uget(v_bs_973_, v_i_972_);
v_fst_982_ = lean_ctor_get(v_v_981_, 0);
v_snd_983_ = lean_ctor_get(v_v_981_, 1);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_v_981_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_985_ = v_v_981_;
v_isShared_986_ = v_isSharedCheck_1013_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_snd_983_);
lean_inc(v_fst_982_);
lean_dec(v_v_981_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_1013_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v_pos_987_; lean_object* v_pos_988_; lean_object* v___x_989_; lean_object* v_bs_x27_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_995_; 
v_pos_987_ = lean_ctor_get(v_before_969_, 1);
v_pos_988_ = lean_ctor_get(v_after_970_, 1);
v___x_989_ = lean_unsigned_to_nat(0u);
v_bs_x27_990_ = lean_array_uset(v_bs_973_, v_i_972_, v___x_989_);
v___x_991_ = lean_usize_to_nat(v_i_972_);
v___x_992_ = lean_array_get_size(v_snd_968_);
v___x_993_ = l_Lean_SubExpr_Pos_pushNaryArg(v___x_992_, v___x_991_, v_pos_987_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 1, v___x_993_);
v___x_995_ = v___x_985_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_fst_982_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v___x_993_);
v___x_995_ = v_reuseFailAlloc_1012_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_996_ = l_Lean_SubExpr_Pos_pushNaryArg(v___x_992_, v___x_991_, v_pos_988_);
lean_dec(v___x_991_);
v___x_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_997_, 0, v_snd_983_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_995_, v___x_997_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; size_t v___x_1000_; size_t v___x_1001_; lean_object* v___x_1002_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref_known(v___x_998_, 1);
v___x_1000_ = ((size_t)1ULL);
v___x_1001_ = lean_usize_add(v_i_972_, v___x_1000_);
v___x_1002_ = lean_array_uset(v_bs_x27_990_, v_i_972_, v_a_999_);
v_i_972_ = v___x_1001_;
v_bs_973_ = v___x_1002_;
goto _start;
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_dec_ref(v_bs_x27_990_);
v_a_1004_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_998_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_998_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
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
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__0));
v___x_1016_ = l_Lean_stringToMessageData(v___x_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0___boxed(lean_object* v_body_1017_, lean_object* v_pos_1018_, lean_object* v_body_1019_, lean_object* v_pos_1020_, lean_object* v_x_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0(v_body_1017_, v_pos_1018_, v_body_1019_, v_pos_1020_, v_x_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec_ref(v_x_1021_);
lean_dec(v_pos_1020_);
lean_dec_ref(v_body_1019_);
lean_dec(v_pos_1018_);
lean_dec_ref(v_body_1017_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(lean_object* v_before_1028_, lean_object* v_after_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v_a_1041_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; uint8_t v___y_1052_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v_a_1071_; lean_object* v_expr_1074_; lean_object* v_pos_1075_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; 
v_expr_1074_ = lean_ctor_get(v_before_1028_, 0);
v_pos_1075_ = lean_ctor_get(v_before_1028_, 1);
if (lean_obj_tag(v_expr_1074_) == 7)
{
lean_object* v_binderName_1112_; lean_object* v_binderType_1113_; lean_object* v_body_1114_; uint8_t v_binderInfo_1115_; lean_object* v_expr_1116_; lean_object* v_pos_1117_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; 
v_binderName_1112_ = lean_ctor_get(v_expr_1074_, 0);
v_binderType_1113_ = lean_ctor_get(v_expr_1074_, 1);
v_body_1114_ = lean_ctor_get(v_expr_1074_, 2);
v_binderInfo_1115_ = lean_ctor_get_uint8(v_expr_1074_, sizeof(void*)*3 + 8);
v_expr_1116_ = lean_ctor_get(v_after_1029_, 0);
v_pos_1117_ = lean_ctor_get(v_after_1029_, 1);
if (lean_obj_tag(v_expr_1116_) == 7)
{
lean_object* v_binderName_1143_; lean_object* v_binderType_1144_; lean_object* v_body_1145_; uint8_t v_binderInfo_1146_; lean_object* v___f_1147_; uint8_t v___y_1149_; uint8_t v___x_1199_; 
v_binderName_1143_ = lean_ctor_get(v_expr_1116_, 0);
v_binderType_1144_ = lean_ctor_get(v_expr_1116_, 1);
v_body_1145_ = lean_ctor_get(v_expr_1116_, 2);
v_binderInfo_1146_ = lean_ctor_get_uint8(v_expr_1116_, sizeof(void*)*3 + 8);
lean_inc(v_pos_1117_);
lean_inc_ref(v_body_1145_);
lean_inc(v_pos_1075_);
lean_inc_ref(v_body_1114_);
v___f_1147_ = lean_alloc_closure((void*)(l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1147_, 0, v_body_1114_);
lean_closure_set(v___f_1147_, 1, v_pos_1075_);
lean_closure_set(v___f_1147_, 2, v_body_1145_);
lean_closure_set(v___f_1147_, 3, v_pos_1117_);
v___x_1199_ = lean_name_eq(v_binderName_1112_, v_binderName_1143_);
if (v___x_1199_ == 0)
{
v___y_1149_ = v___x_1199_;
goto v___jp_1148_;
}
else
{
uint8_t v___x_1200_; 
v___x_1200_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1115_, v_binderInfo_1146_);
v___y_1149_ = v___x_1200_;
goto v___jp_1148_;
}
v___jp_1148_:
{
if (v___y_1149_ == 0)
{
lean_dec_ref(v___f_1147_);
v___y_1119_ = v_a_1030_;
v___y_1120_ = v_a_1031_;
v___y_1121_ = v_a_1032_;
v___y_1122_ = v_a_1033_;
goto v___jp_1118_;
}
else
{
lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1196_; 
lean_inc_ref(v_binderType_1144_);
lean_inc(v_pos_1117_);
lean_inc_ref(v_binderType_1113_);
lean_inc(v_binderName_1112_);
lean_inc(v_pos_1075_);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_before_1028_);
if (v_isSharedCheck_1196_ == 0)
{
lean_object* v_unused_1197_; lean_object* v_unused_1198_; 
v_unused_1197_ = lean_ctor_get(v_before_1028_, 1);
lean_dec(v_unused_1197_);
v_unused_1198_ = lean_ctor_get(v_before_1028_, 0);
lean_dec(v_unused_1198_);
v___x_1151_ = v_before_1028_;
v_isShared_1152_ = v_isSharedCheck_1196_;
goto v_resetjp_1150_;
}
else
{
lean_dec(v_before_1028_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1196_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1193_; 
v_isSharedCheck_1193_ = !lean_is_exclusive(v_after_1029_);
if (v_isSharedCheck_1193_ == 0)
{
lean_object* v_unused_1194_; lean_object* v_unused_1195_; 
v_unused_1194_ = lean_ctor_get(v_after_1029_, 1);
lean_dec(v_unused_1194_);
v_unused_1195_ = lean_ctor_get(v_after_1029_, 0);
lean_dec(v_unused_1195_);
v___x_1154_ = v_after_1029_;
v_isShared_1155_ = v_isSharedCheck_1193_;
goto v_resetjp_1153_;
}
else
{
lean_dec(v_after_1029_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1193_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; lean_object* v___x_1158_; 
v___x_1156_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1075_);
lean_inc_ref(v_binderType_1113_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 1, v___x_1156_);
lean_ctor_set(v___x_1154_, 0, v_binderType_1113_);
v___x_1158_ = v___x_1154_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_binderType_1113_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1159_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1117_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 1, v___x_1159_);
lean_ctor_set(v___x_1151_, 0, v_binderType_1144_);
v___x_1161_ = v___x_1151_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_binderType_1144_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1162_; 
v___x_1162_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1158_, v___x_1161_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1190_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1165_ = v___x_1162_;
v_isShared_1166_ = v_isSharedCheck_1190_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1162_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1190_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
uint8_t v___x_1167_; 
v___x_1167_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_a_1163_);
if (v___x_1167_ == 0)
{
lean_object* v_changesBefore_1168_; lean_object* v_changesAfter_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; lean_object* v___x_1173_; lean_object* v_changesBefore_1174_; lean_object* v_changesAfter_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1187_; 
lean_dec_ref(v___f_1147_);
lean_dec_ref(v_binderType_1113_);
lean_dec(v_binderName_1112_);
v_changesBefore_1168_ = lean_ctor_get(v_a_1163_, 0);
lean_inc(v_changesBefore_1168_);
v_changesAfter_1169_ = lean_ctor_get(v_a_1163_, 1);
lean_inc(v_changesAfter_1169_);
lean_dec(v_a_1163_);
v___x_1170_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1075_);
lean_dec(v_pos_1075_);
v___x_1171_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1117_);
lean_dec(v_pos_1117_);
v___x_1172_ = 0;
v___x_1173_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v___x_1170_, v___x_1171_, v___x_1172_);
v_changesBefore_1174_ = lean_ctor_get(v___x_1173_, 0);
v_changesAfter_1175_ = lean_ctor_get(v___x_1173_, 1);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1177_ = v___x_1173_;
v_isShared_1178_ = v_isSharedCheck_1187_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_changesAfter_1175_);
lean_inc(v_changesBefore_1174_);
lean_dec(v___x_1173_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1187_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1182_; 
v___x_1179_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesBefore_1168_, v_changesBefore_1174_);
v___x_1180_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesAfter_1169_, v_changesAfter_1175_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 1, v___x_1180_);
lean_ctor_set(v___x_1177_, 0, v___x_1179_);
v___x_1182_ = v___x_1177_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1179_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v___x_1180_);
v___x_1182_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1184_; 
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v___x_1182_);
v___x_1184_ = v___x_1165_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
else
{
uint8_t v___x_1188_; lean_object* v___x_1189_; 
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
lean_dec(v_pos_1117_);
lean_dec(v_pos_1075_);
v___x_1188_ = 0;
v___x_1189_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_binderName_1112_, v_binderInfo_1115_, v_binderType_1113_, v___f_1147_, v___x_1188_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_);
return v___x_1189_;
}
}
}
else
{
lean_dec_ref(v___f_1147_);
lean_dec(v_pos_1117_);
lean_dec_ref(v_binderType_1113_);
lean_dec(v_binderName_1112_);
lean_dec(v_pos_1075_);
return v___x_1162_;
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
v___y_1119_ = v_a_1030_;
v___y_1120_ = v_a_1031_;
v___y_1121_ = v_a_1032_;
v___y_1122_ = v_a_1033_;
goto v___jp_1118_;
}
v___jp_1118_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1123_ = l_Lean_Expr_getForallBinderNames(v_expr_1116_);
v___x_1124_ = l_Lean_Expr_getForallBinderNames(v_expr_1074_);
v___x_1125_ = l_List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0(v___x_1123_, v___x_1124_);
if (lean_obj_tag(v___x_1125_) == 1)
{
lean_object* v_val_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; 
v_val_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_val_1126_);
lean_dec_ref_known(v___x_1125_, 1);
v___x_1127_ = l_List_lengthTR___redArg(v_val_1126_);
v___x_1128_ = lean_unsigned_to_nat(0u);
v___x_1129_ = lean_nat_dec_eq(v___x_1127_, v___x_1128_);
lean_dec(v___x_1127_);
if (v___x_1129_ == 0)
{
v___y_1077_ = v_val_1126_;
v___y_1078_ = v___y_1119_;
v___y_1079_ = v___y_1120_;
v___y_1080_ = v___y_1121_;
v___y_1081_ = v___y_1122_;
goto v___jp_1076_;
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1, &l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1);
v___x_1131_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_1130_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_dec_ref_known(v___x_1131_, 1);
v___y_1077_ = v_val_1126_;
v___y_1078_ = v___y_1119_;
v___y_1079_ = v___y_1120_;
v___y_1080_ = v___y_1121_;
v___y_1081_ = v___y_1122_;
goto v___jp_1076_;
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_dec(v_val_1126_);
lean_dec_ref(v_after_1029_);
lean_dec_ref(v_before_1028_);
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1131_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1131_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
}
else
{
uint8_t v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_dec(v___x_1125_);
v___x_1140_ = 0;
v___x_1141_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1028_, v_after_1029_, v___x_1140_);
v___x_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
return v___x_1142_;
}
}
}
else
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
lean_dec_ref(v_after_1029_);
lean_dec_ref(v_before_1028_);
v___x_1201_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___x_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
return v___x_1202_;
}
v___jp_1035_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_unsigned_to_nat(0u);
v___x_1043_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v___y_1038_, v_before_1028_, v___x_1042_, v_a_1041_);
lean_dec(v___y_1038_);
return v___x_1043_;
}
v___jp_1044_:
{
if (v___y_1052_ == 0)
{
lean_object* v___x_1053_; 
lean_dec_ref(v___y_1049_);
v___x_1053_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1046_, v___y_1045_, v___y_1048_);
lean_dec_ref(v___y_1046_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v___x_1054_; 
lean_dec_ref_known(v___x_1053_, 1);
v___x_1054_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___y_1036_ = v___y_1045_;
v___y_1037_ = v___y_1048_;
v___y_1038_ = v___y_1047_;
v___y_1039_ = v___y_1050_;
v___y_1040_ = v___y_1051_;
v_a_1041_ = v___x_1054_;
goto v___jp_1035_;
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_dec(v___y_1047_);
lean_dec_ref(v_before_1028_);
v_a_1055_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1053_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1053_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
else
{
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec_ref(v_before_1028_);
return v___y_1049_;
}
}
v___jp_1063_:
{
uint8_t v___x_1072_; 
v___x_1072_ = l_Lean_Exception_isInterrupt(v_a_1071_);
if (v___x_1072_ == 0)
{
uint8_t v___x_1073_; 
v___x_1073_ = l_Lean_Exception_isRuntime(v_a_1071_);
v___y_1045_ = v___y_1064_;
v___y_1046_ = v___y_1065_;
v___y_1047_ = v___y_1067_;
v___y_1048_ = v___y_1066_;
v___y_1049_ = v___y_1070_;
v___y_1050_ = v___y_1068_;
v___y_1051_ = v___y_1069_;
v___y_1052_ = v___x_1073_;
goto v___jp_1044_;
}
else
{
lean_dec_ref(v_a_1071_);
v___y_1045_ = v___y_1064_;
v___y_1046_ = v___y_1065_;
v___y_1047_ = v___y_1067_;
v___y_1048_ = v___y_1066_;
v___y_1049_ = v___y_1070_;
v___y_1050_ = v___y_1068_;
v___y_1051_ = v___y_1069_;
v___y_1052_ = v___x_1072_;
goto v___jp_1044_;
}
}
v___jp_1076_:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Lean_Meta_saveState___redArg(v___y_1079_, v___y_1081_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_a_1083_);
lean_dec_ref_known(v___x_1082_, 1);
v___x_1084_ = l_List_lengthTR___redArg(v___y_1077_);
v___x_1085_ = lean_box(0);
v___x_1086_ = l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(v___y_1077_, v___x_1085_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v_body_u2080_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1086_, 1);
lean_inc_n(v___x_1084_, 2);
v_body_u2080_1088_ = l_Lean_Expr_getForallBodyMaxDepth(v___x_1084_, v_expr_1074_);
v___x_1089_ = lean_array_mk(v_a_1087_);
v___x_1090_ = lean_expr_instantiate_rev(v_body_u2080_1088_, v___x_1089_);
lean_dec_ref(v___x_1089_);
lean_dec_ref(v_body_u2080_1088_);
lean_inc(v_pos_1075_);
v___x_1091_ = l_Lean_SubExpr_Pos_pushNthBindingBody(v___x_1084_, v_pos_1075_);
v___x_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1090_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
v___x_1093_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1092_, v_after_1029_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; 
lean_dec(v_a_1083_);
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_a_1094_);
lean_dec_ref_known(v___x_1093_, 1);
v___y_1036_ = v___y_1079_;
v___y_1037_ = v___y_1081_;
v___y_1038_ = v___x_1084_;
v___y_1039_ = v___y_1078_;
v___y_1040_ = v___y_1080_;
v_a_1041_ = v_a_1094_;
goto v___jp_1035_;
}
else
{
lean_object* v_a_1095_; 
v_a_1095_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_a_1095_);
v___y_1064_ = v___y_1079_;
v___y_1065_ = v_a_1083_;
v___y_1066_ = v___y_1081_;
v___y_1067_ = v___x_1084_;
v___y_1068_ = v___y_1078_;
v___y_1069_ = v___y_1080_;
v___y_1070_ = v___x_1093_;
v_a_1071_ = v_a_1095_;
goto v___jp_1063_;
}
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec_ref(v_after_1029_);
v_a_1096_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1086_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1086_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
lean_inc(v_a_1096_);
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
v___y_1064_ = v___y_1079_;
v___y_1065_ = v_a_1083_;
v___y_1066_ = v___y_1081_;
v___y_1067_ = v___x_1084_;
v___y_1068_ = v___y_1078_;
v___y_1069_ = v___y_1080_;
v___y_1070_ = v___x_1101_;
v_a_1071_ = v_a_1096_;
goto v___jp_1063_;
}
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_dec(v___y_1077_);
lean_dec_ref(v_after_1029_);
lean_dec_ref(v_before_1028_);
v_a_1104_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1082_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1082_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(lean_object* v_before_1203_, lean_object* v_after_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_){
_start:
{
lean_object* v_expr_1226_; lean_object* v_pos_1227_; lean_object* v_expr_1228_; lean_object* v_pos_1229_; lean_object* v_e_u2081_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; uint8_t v___x_1238_; 
v_expr_1226_ = lean_ctor_get(v_before_1203_, 0);
v_pos_1227_ = lean_ctor_get(v_before_1203_, 1);
v_expr_1228_ = lean_ctor_get(v_after_1204_, 0);
v_pos_1229_ = lean_ctor_get(v_after_1204_, 1);
v___x_1238_ = lean_expr_eqv(v_expr_1226_, v_expr_1228_);
if (v___x_1238_ == 0)
{
switch(lean_obj_tag(v_expr_1226_))
{
case 10:
{
lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1247_; 
lean_inc_ref(v_expr_1226_);
lean_inc(v_pos_1227_);
v_isSharedCheck_1247_ = !lean_is_exclusive(v_before_1203_);
if (v_isSharedCheck_1247_ == 0)
{
lean_object* v_unused_1248_; lean_object* v_unused_1249_; 
v_unused_1248_ = lean_ctor_get(v_before_1203_, 1);
lean_dec(v_unused_1248_);
v_unused_1249_ = lean_ctor_get(v_before_1203_, 0);
lean_dec(v_unused_1249_);
v___x_1240_ = v_before_1203_;
v_isShared_1241_ = v_isSharedCheck_1247_;
goto v_resetjp_1239_;
}
else
{
lean_dec(v_before_1203_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1247_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v_expr_1242_; lean_object* v___x_1244_; 
v_expr_1242_ = lean_ctor_get(v_expr_1226_, 1);
lean_inc_ref(v_expr_1242_);
lean_dec_ref_known(v_expr_1226_, 2);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 0, v_expr_1242_);
v___x_1244_ = v___x_1240_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_expr_1242_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_pos_1227_);
v___x_1244_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
v_before_1203_ = v___x_1244_;
goto _start;
}
}
}
case 5:
{
switch(lean_obj_tag(v_expr_1228_))
{
case 10:
{
lean_object* v_expr_1250_; 
lean_inc_ref(v_expr_1228_);
lean_inc(v_pos_1229_);
lean_dec_ref(v_after_1204_);
v_expr_1250_ = lean_ctor_get(v_expr_1228_, 1);
lean_inc_ref(v_expr_1250_);
lean_dec_ref_known(v_expr_1228_, 2);
v_e_u2081_1231_ = v_expr_1250_;
v___y_1232_ = v_a_1205_;
v___y_1233_ = v_a_1206_;
v___y_1234_ = v_a_1207_;
v___y_1235_ = v_a_1208_;
goto v___jp_1230_;
}
case 5:
{
lean_object* v_dummy_1251_; lean_object* v_nargs_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v_fst_1257_; lean_object* v_snd_1258_; lean_object* v_nargs_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v_fst_1263_; lean_object* v_snd_1264_; uint8_t v___x_1265_; 
v_dummy_1251_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0, &l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0);
v_nargs_1252_ = l_Lean_Expr_getAppNumArgs(v_expr_1228_);
lean_inc(v_nargs_1252_);
v___x_1253_ = lean_mk_array(v_nargs_1252_, v_dummy_1251_);
v___x_1254_ = lean_unsigned_to_nat(1u);
v___x_1255_ = lean_nat_sub(v_nargs_1252_, v___x_1254_);
lean_dec(v_nargs_1252_);
lean_inc_ref(v_expr_1228_);
v___x_1256_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(v_expr_1228_, v___x_1253_, v___x_1255_);
v_fst_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_fst_1257_);
v_snd_1258_ = lean_ctor_get(v___x_1256_, 1);
lean_inc(v_snd_1258_);
lean_dec_ref(v___x_1256_);
v_nargs_1259_ = l_Lean_Expr_getAppNumArgs(v_expr_1226_);
lean_inc(v_nargs_1259_);
v___x_1260_ = lean_mk_array(v_nargs_1259_, v_dummy_1251_);
v___x_1261_ = lean_nat_sub(v_nargs_1259_, v___x_1254_);
lean_dec(v_nargs_1259_);
lean_inc_ref(v_expr_1226_);
v___x_1262_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(v_expr_1226_, v___x_1260_, v___x_1261_);
v_fst_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_fst_1263_);
v_snd_1264_ = lean_ctor_get(v___x_1262_, 1);
lean_inc(v_snd_1264_);
lean_dec_ref(v___x_1262_);
v___x_1265_ = lean_expr_eqv(v_fst_1257_, v_fst_1263_);
lean_dec(v_fst_1263_);
lean_dec(v_fst_1257_);
if (v___x_1265_ == 0)
{
lean_dec(v_snd_1264_);
lean_dec(v_snd_1258_);
goto v___jp_1218_;
}
else
{
if (v___x_1238_ == 0)
{
lean_object* v___x_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v___x_1266_ = lean_array_get_size(v_snd_1258_);
v___x_1267_ = lean_array_get_size(v_snd_1264_);
v___x_1268_ = lean_nat_dec_eq(v___x_1266_, v___x_1267_);
if (v___x_1268_ == 0)
{
lean_dec(v_snd_1264_);
lean_dec(v_snd_1258_);
goto v___jp_1218_;
}
else
{
lean_object* v_args_1269_; size_t v_sz_1270_; size_t v___x_1271_; lean_object* v___x_1272_; 
v_args_1269_ = l_Array_zip___redArg(v_snd_1258_, v_snd_1264_);
lean_dec(v_snd_1264_);
v_sz_1270_ = lean_array_size(v_args_1269_);
v___x_1271_ = ((size_t)0ULL);
v___x_1272_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_1258_, v_before_1203_, v_after_1204_, v_sz_1270_, v___x_1271_, v_args_1269_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_);
lean_dec_ref(v_after_1204_);
lean_dec_ref(v_before_1203_);
lean_dec(v_snd_1258_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1298_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1275_ = v___x_1272_;
v_isShared_1276_ = v_isSharedCheck_1298_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1272_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1298_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; 
v___x_1277_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___x_1278_ = lean_unsigned_to_nat(0u);
v___x_1279_ = lean_array_get_size(v_a_1273_);
v___x_1280_ = lean_nat_dec_lt(v___x_1278_, v___x_1279_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1282_; 
lean_dec(v_a_1273_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___x_1277_);
v___x_1282_ = v___x_1275_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
else
{
uint8_t v___x_1284_; 
v___x_1284_ = lean_nat_dec_le(v___x_1279_, v___x_1279_);
if (v___x_1284_ == 0)
{
if (v___x_1280_ == 0)
{
lean_object* v___x_1286_; 
lean_dec(v_a_1273_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___x_1277_);
v___x_1286_ = v___x_1275_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1277_);
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
size_t v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1288_ = lean_usize_of_nat(v___x_1279_);
v___x_1289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_a_1273_, v___x_1271_, v___x_1288_, v___x_1277_);
lean_dec(v_a_1273_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___x_1289_);
v___x_1291_ = v___x_1275_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
else
{
size_t v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1296_; 
v___x_1293_ = lean_usize_of_nat(v___x_1279_);
v___x_1294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_a_1273_, v___x_1271_, v___x_1293_, v___x_1277_);
lean_dec(v_a_1273_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___x_1294_);
v___x_1296_ = v___x_1275_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1294_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
v_a_1299_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1272_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1272_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
}
else
{
lean_dec(v_snd_1264_);
lean_dec(v_snd_1258_);
goto v___jp_1218_;
}
}
}
default: 
{
goto v___jp_1222_;
}
}
}
case 7:
{
if (lean_obj_tag(v_expr_1228_) == 10)
{
lean_object* v_expr_1307_; 
lean_inc_ref(v_expr_1228_);
lean_inc(v_pos_1229_);
lean_dec_ref(v_after_1204_);
v_expr_1307_ = lean_ctor_get(v_expr_1228_, 1);
lean_inc_ref(v_expr_1307_);
lean_dec_ref_known(v_expr_1228_, 2);
v_e_u2081_1231_ = v_expr_1307_;
v___y_1232_ = v_a_1205_;
v___y_1233_ = v_a_1206_;
v___y_1234_ = v_a_1207_;
v___y_1235_ = v_a_1208_;
goto v___jp_1230_;
}
else
{
lean_object* v___x_1308_; 
v___x_1308_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(v_before_1203_, v_after_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_);
return v___x_1308_;
}
}
case 6:
{
switch(lean_obj_tag(v_expr_1228_))
{
case 10:
{
lean_object* v_expr_1309_; 
lean_inc_ref(v_expr_1228_);
lean_inc(v_pos_1229_);
lean_dec_ref(v_after_1204_);
v_expr_1309_ = lean_ctor_get(v_expr_1228_, 1);
lean_inc_ref(v_expr_1309_);
lean_dec_ref_known(v_expr_1228_, 2);
v_e_u2081_1231_ = v_expr_1309_;
v___y_1232_ = v_a_1205_;
v___y_1233_ = v_a_1206_;
v___y_1234_ = v_a_1207_;
v___y_1235_ = v_a_1208_;
goto v___jp_1230_;
}
case 6:
{
lean_object* v_binderName_1310_; lean_object* v_binderType_1311_; lean_object* v_body_1312_; uint8_t v_binderInfo_1313_; lean_object* v_binderName_1314_; lean_object* v_binderType_1315_; lean_object* v_body_1316_; uint8_t v_binderInfo_1317_; uint8_t v___x_1318_; 
v_binderName_1310_ = lean_ctor_get(v_expr_1226_, 0);
v_binderType_1311_ = lean_ctor_get(v_expr_1226_, 1);
v_body_1312_ = lean_ctor_get(v_expr_1226_, 2);
v_binderInfo_1313_ = lean_ctor_get_uint8(v_expr_1226_, sizeof(void*)*3 + 8);
v_binderName_1314_ = lean_ctor_get(v_expr_1228_, 0);
v_binderType_1315_ = lean_ctor_get(v_expr_1228_, 1);
v_body_1316_ = lean_ctor_get(v_expr_1228_, 2);
v_binderInfo_1317_ = lean_ctor_get_uint8(v_expr_1228_, sizeof(void*)*3 + 8);
v___x_1318_ = lean_name_eq(v_binderName_1310_, v_binderName_1314_);
if (v___x_1318_ == 0)
{
goto v___jp_1214_;
}
else
{
if (v___x_1238_ == 0)
{
uint8_t v___x_1319_; 
v___x_1319_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1313_, v_binderInfo_1317_);
if (v___x_1319_ == 0)
{
goto v___jp_1214_;
}
else
{
lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1369_; 
lean_inc_ref(v_body_1316_);
lean_inc_ref(v_binderType_1315_);
lean_inc_ref(v_body_1312_);
lean_inc_ref(v_binderType_1311_);
lean_inc(v_pos_1229_);
lean_inc(v_pos_1227_);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_before_1203_);
if (v_isSharedCheck_1369_ == 0)
{
lean_object* v_unused_1370_; lean_object* v_unused_1371_; 
v_unused_1370_ = lean_ctor_get(v_before_1203_, 1);
lean_dec(v_unused_1370_);
v_unused_1371_ = lean_ctor_get(v_before_1203_, 0);
lean_dec(v_unused_1371_);
v___x_1321_ = v_before_1203_;
v_isShared_1322_ = v_isSharedCheck_1369_;
goto v_resetjp_1320_;
}
else
{
lean_dec(v_before_1203_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1369_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1366_; 
v_isSharedCheck_1366_ = !lean_is_exclusive(v_after_1204_);
if (v_isSharedCheck_1366_ == 0)
{
lean_object* v_unused_1367_; lean_object* v_unused_1368_; 
v_unused_1367_ = lean_ctor_get(v_after_1204_, 1);
lean_dec(v_unused_1367_);
v_unused_1368_ = lean_ctor_get(v_after_1204_, 0);
lean_dec(v_unused_1368_);
v___x_1324_ = v_after_1204_;
v_isShared_1325_ = v_isSharedCheck_1366_;
goto v_resetjp_1323_;
}
else
{
lean_dec(v_after_1204_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1366_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1326_; lean_object* v___x_1328_; 
v___x_1326_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1227_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 1, v___x_1326_);
lean_ctor_set(v___x_1324_, 0, v_binderType_1311_);
v___x_1328_ = v___x_1324_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_binderType_1311_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v___x_1326_);
v___x_1328_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___x_1329_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1229_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 1, v___x_1329_);
lean_ctor_set(v___x_1321_, 0, v_binderType_1315_);
v___x_1331_ = v___x_1321_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_binderType_1315_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v___x_1329_);
v___x_1331_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
lean_object* v___x_1332_; 
v___x_1332_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1328_, v___x_1331_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1363_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1335_ = v___x_1332_;
v_isShared_1336_ = v_isSharedCheck_1363_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1332_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1363_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
uint8_t v___x_1337_; 
v___x_1337_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_a_1333_);
if (v___x_1337_ == 0)
{
lean_object* v_changesBefore_1338_; lean_object* v_changesAfter_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; lean_object* v___x_1343_; lean_object* v_changesBefore_1344_; lean_object* v_changesAfter_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1357_; 
lean_dec_ref(v_body_1316_);
lean_dec_ref(v_body_1312_);
v_changesBefore_1338_ = lean_ctor_get(v_a_1333_, 0);
lean_inc(v_changesBefore_1338_);
v_changesAfter_1339_ = lean_ctor_get(v_a_1333_, 1);
lean_inc(v_changesAfter_1339_);
lean_dec(v_a_1333_);
v___x_1340_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1227_);
lean_dec(v_pos_1227_);
v___x_1341_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1229_);
lean_dec(v_pos_1229_);
v___x_1342_ = 0;
v___x_1343_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v___x_1340_, v___x_1341_, v___x_1342_);
v_changesBefore_1344_ = lean_ctor_get(v___x_1343_, 0);
v_changesAfter_1345_ = lean_ctor_get(v___x_1343_, 1);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1347_ = v___x_1343_;
v_isShared_1348_ = v_isSharedCheck_1357_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_changesAfter_1345_);
lean_inc(v_changesBefore_1344_);
lean_dec(v___x_1343_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1357_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1352_; 
v___x_1349_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesBefore_1338_, v_changesBefore_1344_);
v___x_1350_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesAfter_1339_, v_changesAfter_1345_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 1, v___x_1350_);
lean_ctor_set(v___x_1347_, 0, v___x_1349_);
v___x_1352_ = v___x_1347_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1354_; 
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v___x_1352_);
v___x_1354_ = v___x_1335_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
else
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
lean_del_object(v___x_1335_);
lean_dec(v_a_1333_);
v___x_1358_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1227_);
lean_dec(v_pos_1227_);
v___x_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1359_, 0, v_body_1312_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
v___x_1360_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1229_);
lean_dec(v_pos_1229_);
v___x_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1361_, 0, v_body_1316_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
v_before_1203_ = v___x_1359_;
v_after_1204_ = v___x_1361_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_body_1316_);
lean_dec_ref(v_body_1312_);
lean_dec(v_pos_1229_);
lean_dec(v_pos_1227_);
return v___x_1332_;
}
}
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
default: 
{
goto v___jp_1222_;
}
}
}
case 11:
{
switch(lean_obj_tag(v_expr_1228_))
{
case 10:
{
lean_object* v_expr_1372_; 
lean_inc_ref(v_expr_1228_);
lean_inc(v_pos_1229_);
lean_dec_ref(v_after_1204_);
v_expr_1372_ = lean_ctor_get(v_expr_1228_, 1);
lean_inc_ref(v_expr_1372_);
lean_dec_ref_known(v_expr_1228_, 2);
v_e_u2081_1231_ = v_expr_1372_;
v___y_1232_ = v_a_1205_;
v___y_1233_ = v_a_1206_;
v___y_1234_ = v_a_1207_;
v___y_1235_ = v_a_1208_;
goto v___jp_1230_;
}
case 11:
{
lean_object* v_typeName_1373_; lean_object* v_idx_1374_; lean_object* v_struct_1375_; lean_object* v_typeName_1376_; lean_object* v_idx_1377_; lean_object* v_struct_1378_; uint8_t v___x_1379_; 
v_typeName_1373_ = lean_ctor_get(v_expr_1226_, 0);
v_idx_1374_ = lean_ctor_get(v_expr_1226_, 1);
v_struct_1375_ = lean_ctor_get(v_expr_1226_, 2);
v_typeName_1376_ = lean_ctor_get(v_expr_1228_, 0);
v_idx_1377_ = lean_ctor_get(v_expr_1228_, 1);
v_struct_1378_ = lean_ctor_get(v_expr_1228_, 2);
v___x_1379_ = lean_name_eq(v_typeName_1373_, v_typeName_1376_);
if (v___x_1379_ == 0)
{
goto v___jp_1210_;
}
else
{
if (v___x_1238_ == 0)
{
uint8_t v___x_1380_; 
v___x_1380_ = lean_nat_dec_eq(v_idx_1374_, v_idx_1377_);
if (v___x_1380_ == 0)
{
goto v___jp_1210_;
}
else
{
lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1399_; 
lean_inc_ref(v_struct_1378_);
lean_inc_ref(v_struct_1375_);
lean_inc(v_pos_1229_);
lean_inc(v_pos_1227_);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_before_1203_);
if (v_isSharedCheck_1399_ == 0)
{
lean_object* v_unused_1400_; lean_object* v_unused_1401_; 
v_unused_1400_ = lean_ctor_get(v_before_1203_, 1);
lean_dec(v_unused_1400_);
v_unused_1401_ = lean_ctor_get(v_before_1203_, 0);
lean_dec(v_unused_1401_);
v___x_1382_ = v_before_1203_;
v_isShared_1383_ = v_isSharedCheck_1399_;
goto v_resetjp_1381_;
}
else
{
lean_dec(v_before_1203_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1399_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1396_; 
v_isSharedCheck_1396_ = !lean_is_exclusive(v_after_1204_);
if (v_isSharedCheck_1396_ == 0)
{
lean_object* v_unused_1397_; lean_object* v_unused_1398_; 
v_unused_1397_ = lean_ctor_get(v_after_1204_, 1);
lean_dec(v_unused_1397_);
v_unused_1398_ = lean_ctor_get(v_after_1204_, 0);
lean_dec(v_unused_1398_);
v___x_1385_ = v_after_1204_;
v_isShared_1386_ = v_isSharedCheck_1396_;
goto v_resetjp_1384_;
}
else
{
lean_dec(v_after_1204_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1396_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1387_ = l_Lean_SubExpr_Pos_pushProj(v_pos_1227_);
lean_dec(v_pos_1227_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 1, v___x_1387_);
lean_ctor_set(v___x_1385_, 0, v_struct_1375_);
v___x_1389_ = v___x_1385_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_struct_1375_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1390_; lean_object* v___x_1392_; 
v___x_1390_ = l_Lean_SubExpr_Pos_pushProj(v_pos_1229_);
lean_dec(v_pos_1229_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 1, v___x_1390_);
lean_ctor_set(v___x_1382_, 0, v_struct_1378_);
v___x_1392_ = v___x_1382_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_struct_1378_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
v_before_1203_ = v___x_1389_;
v_after_1204_ = v___x_1392_;
goto _start;
}
}
}
}
}
}
else
{
goto v___jp_1210_;
}
}
}
default: 
{
goto v___jp_1222_;
}
}
}
default: 
{
if (lean_obj_tag(v_expr_1228_) == 10)
{
lean_object* v_expr_1402_; 
lean_inc_ref(v_expr_1228_);
lean_inc(v_pos_1229_);
lean_dec_ref(v_after_1204_);
v_expr_1402_ = lean_ctor_get(v_expr_1228_, 1);
lean_inc_ref(v_expr_1402_);
lean_dec_ref_known(v_expr_1228_, 2);
v_e_u2081_1231_ = v_expr_1402_;
v___y_1232_ = v_a_1205_;
v___y_1233_ = v_a_1206_;
v___y_1234_ = v_a_1207_;
v___y_1235_ = v_a_1208_;
goto v___jp_1230_;
}
else
{
goto v___jp_1222_;
}
}
}
}
else
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
lean_dec_ref(v_after_1204_);
lean_dec_ref(v_before_1203_);
v___x_1403_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___x_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1403_);
return v___x_1404_;
}
v___jp_1210_:
{
uint8_t v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1211_ = 0;
v___x_1212_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1203_, v_after_1204_, v___x_1211_);
v___x_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
return v___x_1213_;
}
v___jp_1214_:
{
uint8_t v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1215_ = 0;
v___x_1216_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1203_, v_after_1204_, v___x_1215_);
v___x_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
return v___x_1217_;
}
v___jp_1218_:
{
uint8_t v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1219_ = 0;
v___x_1220_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1203_, v_after_1204_, v___x_1219_);
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
return v___x_1221_;
}
v___jp_1222_:
{
uint8_t v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1223_ = 0;
v___x_1224_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1203_, v_after_1204_, v___x_1223_);
v___x_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
return v___x_1225_;
}
v___jp_1230_:
{
lean_object* v___x_1236_; 
v___x_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1236_, 0, v_e_u2081_1231_);
lean_ctor_set(v___x_1236_, 1, v_pos_1229_);
v_after_1204_ = v___x_1236_;
v_a_1205_ = v___y_1232_;
v_a_1206_ = v___y_1233_;
v_a_1207_ = v___y_1234_;
v_a_1208_ = v___y_1235_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0(lean_object* v_body_1405_, lean_object* v_pos_1406_, lean_object* v_body_1407_, lean_object* v_pos_1408_, lean_object* v_x_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1415_ = lean_expr_instantiate1(v_body_1405_, v_x_1409_);
v___x_1416_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1406_);
v___x_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1415_);
lean_ctor_set(v___x_1417_, 1, v___x_1416_);
v___x_1418_ = lean_expr_instantiate1(v_body_1407_, v_x_1409_);
v___x_1419_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1408_);
v___x_1420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1418_);
lean_ctor_set(v___x_1420_, 1, v___x_1419_);
v___x_1421_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1417_, v___x_1420_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg___boxed(lean_object* v_snd_1422_, lean_object* v_before_1423_, lean_object* v_after_1424_, lean_object* v_sz_1425_, lean_object* v_i_1426_, lean_object* v_bs_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
size_t v_sz_boxed_1433_; size_t v_i_boxed_1434_; lean_object* v_res_1435_; 
v_sz_boxed_1433_ = lean_unbox_usize(v_sz_1425_);
lean_dec(v_sz_1425_);
v_i_boxed_1434_ = lean_unbox_usize(v_i_1426_);
lean_dec(v_i_1426_);
v_res_1435_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_1422_, v_before_1423_, v_after_1424_, v_sz_boxed_1433_, v_i_boxed_1434_, v_bs_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec_ref(v_after_1424_);
lean_dec_ref(v_before_1423_);
lean_dec_ref(v_snd_1422_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___boxed(lean_object* v_before_1436_, lean_object* v_after_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(v_before_1436_, v_after_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec(v_a_1439_);
lean_dec_ref(v_a_1438_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___boxed(lean_object* v_before_1444_, lean_object* v_after_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v_before_1444_, v_after_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1(lean_object* v_upperBound_1452_, lean_object* v_before_1453_, lean_object* v_inst_1454_, lean_object* v_R_1455_, lean_object* v_a_1456_, lean_object* v_b_1457_, lean_object* v_c_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v_upperBound_1452_, v_before_1453_, v_a_1456_, v_b_1457_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___boxed(lean_object* v_upperBound_1465_, lean_object* v_before_1466_, lean_object* v_inst_1467_, lean_object* v_R_1468_, lean_object* v_a_1469_, lean_object* v_b_1470_, lean_object* v_c_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1(v_upperBound_1465_, v_before_1466_, v_inst_1467_, v_R_1468_, v_a_1469_, v_b_1470_, v_c_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v_upperBound_1465_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3(lean_object* v_00_u03b1_1478_, lean_object* v_msg_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v_msg_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___boxed(lean_object* v_00_u03b1_1486_, lean_object* v_msg_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3(v_00_u03b1_1486_, v_msg_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4(uint8_t v_b_u2082_1494_, lean_object* v_k_1495_, lean_object* v_t_1496_, lean_object* v_hl_1497_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_1494_, v_k_1495_, v_t_1496_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___boxed(lean_object* v_b_u2082_1499_, lean_object* v_k_1500_, lean_object* v_t_1501_, lean_object* v_hl_1502_){
_start:
{
uint8_t v_b_u2082_boxed_1503_; lean_object* v_res_1504_; 
v_b_u2082_boxed_1503_ = lean_unbox(v_b_u2082_1499_);
v_res_1504_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4(v_b_u2082_boxed_1503_, v_k_1500_, v_t_1501_, v_hl_1502_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5(lean_object* v_init_1505_, lean_object* v_t_1506_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_init_1505_, v_t_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9(lean_object* v_snd_1508_, lean_object* v_before_1509_, lean_object* v_after_1510_, lean_object* v_as_1511_, size_t v_sz_1512_, size_t v_i_1513_, lean_object* v_bs_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_1508_, v_before_1509_, v_after_1510_, v_sz_1512_, v_i_1513_, v_bs_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___boxed(lean_object* v_snd_1521_, lean_object* v_before_1522_, lean_object* v_after_1523_, lean_object* v_as_1524_, lean_object* v_sz_1525_, lean_object* v_i_1526_, lean_object* v_bs_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
size_t v_sz_boxed_1533_; size_t v_i_boxed_1534_; lean_object* v_res_1535_; 
v_sz_boxed_1533_ = lean_unbox_usize(v_sz_1525_);
lean_dec(v_sz_1525_);
v_i_boxed_1534_ = lean_unbox_usize(v_i_1526_);
lean_dec(v_i_1526_);
v_res_1535_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9(v_snd_1521_, v_before_1522_, v_after_1523_, v_as_1524_, v_sz_boxed_1533_, v_i_boxed_1534_, v_bs_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec_ref(v_as_1524_);
lean_dec_ref(v_after_1523_);
lean_dec_ref(v_before_1522_);
lean_dec_ref(v_snd_1521_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(lean_object* v_e_u2080_1536_, lean_object* v_e_u2081_1537_, uint8_t v_useAfter_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v___x_1544_; lean_object* v_s_u2080_1545_; lean_object* v_s_u2081_1546_; 
v___x_1544_ = l_Lean_SubExpr_Pos_root;
v_s_u2080_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_u2080_1545_, 0, v_e_u2080_1536_);
lean_ctor_set(v_s_u2080_1545_, 1, v___x_1544_);
v_s_u2081_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_u2081_1546_, 0, v_e_u2081_1537_);
lean_ctor_set(v_s_u2081_1546_, 1, v___x_1544_);
if (v_useAfter_1538_ == 0)
{
lean_object* v___x_1547_; 
v___x_1547_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v_s_u2081_1546_, v_s_u2080_1545_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_);
return v___x_1547_;
}
else
{
lean_object* v___x_1548_; 
v___x_1548_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v_s_u2080_1545_, v_s_u2081_1546_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_);
return v___x_1548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff___boxed(lean_object* v_e_u2080_1549_, lean_object* v_e_u2081_1550_, lean_object* v_useAfter_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_){
_start:
{
uint8_t v_useAfter_boxed_1557_; lean_object* v_res_1558_; 
v_useAfter_boxed_1557_ = lean_unbox(v_useAfter_1551_);
v_res_1558_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(v_e_u2080_1549_, v_e_u2081_1550_, v_useAfter_boxed_1557_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
lean_dec(v_a_1555_);
lean_dec_ref(v_a_1554_);
lean_dec(v_a_1553_);
lean_dec_ref(v_a_1552_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0(uint8_t v_useAfter_1559_, lean_object* v_info_1560_, uint8_t v_d_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
uint8_t v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1567_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag(v_useAfter_1559_, v_d_1561_);
v___x_1568_ = l_Lean_Widget_SubexprInfo_withDiffTag(v___x_1567_, v_info_1560_);
v___x_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0___boxed(lean_object* v_useAfter_1570_, lean_object* v_info_1571_, lean_object* v_d_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
uint8_t v_useAfter_boxed_1578_; uint8_t v_d_boxed_1579_; lean_object* v_res_1580_; 
v_useAfter_boxed_1578_ = lean_unbox(v_useAfter_1570_);
v_d_boxed_1579_ = lean_unbox(v_d_1572_);
v_res_1580_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0(v_useAfter_boxed_1578_, v_info_1571_, v_d_boxed_1579_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(lean_object* v_f_1581_, lean_object* v_x_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
switch(lean_obj_tag(v_x_1582_))
{
case 0:
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1596_; 
lean_dec_ref(v_f_1581_);
v_a_1588_ = lean_ctor_get(v_x_1582_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_x_1582_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1590_ = v_x_1582_;
v_isShared_1591_ = v_isSharedCheck_1596_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v_x_1582_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1596_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
lean_object* v___x_1594_; 
v___x_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
return v___x_1594_;
}
}
}
case 1:
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1623_; 
v_a_1597_ = lean_ctor_get(v_x_1582_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v_x_1582_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1599_ = v_x_1582_;
v_isShared_1600_ = v_isSharedCheck_1623_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v_x_1582_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1623_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
size_t v_sz_1601_; size_t v___x_1602_; lean_object* v___x_1603_; 
v_sz_1601_ = lean_array_size(v_a_1597_);
v___x_1602_ = ((size_t)0ULL);
v___x_1603_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_1581_, v_sz_1601_, v___x_1602_, v_a_1597_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1614_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1606_ = v___x_1603_;
v_isShared_1607_ = v_isSharedCheck_1614_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1603_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1614_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 0, v_a_1604_);
v___x_1609_ = v___x_1599_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1611_; 
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v___x_1609_);
v___x_1611_ = v___x_1606_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1609_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_del_object(v___x_1599_);
v_a_1615_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1603_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1603_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
}
default: 
{
lean_object* v_a_1624_; lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1651_; 
v_a_1624_ = lean_ctor_get(v_x_1582_, 0);
v_a_1625_ = lean_ctor_get(v_x_1582_, 1);
v_isSharedCheck_1651_ = !lean_is_exclusive(v_x_1582_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1627_ = v_x_1582_;
v_isShared_1628_ = v_isSharedCheck_1651_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_inc(v_a_1624_);
lean_dec(v_x_1582_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1651_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; 
lean_inc_ref(v_f_1581_);
lean_inc(v___y_1586_);
lean_inc_ref(v___y_1585_);
lean_inc(v___y_1584_);
lean_inc_ref(v___y_1583_);
v___x_1629_ = lean_apply_6(v_f_1581_, v_a_1624_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, lean_box(0));
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1631_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1630_);
lean_dec_ref_known(v___x_1629_, 1);
v___x_1631_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1581_, v_a_1625_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1642_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1634_ = v___x_1631_;
v_isShared_1635_ = v_isSharedCheck_1642_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1631_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1642_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 1, v_a_1632_);
lean_ctor_set(v___x_1627_, 0, v_a_1630_);
v___x_1637_ = v___x_1627_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1630_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
lean_object* v___x_1639_; 
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v___x_1637_);
v___x_1639_ = v___x_1634_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1637_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
else
{
lean_dec(v_a_1630_);
lean_del_object(v___x_1627_);
return v___x_1631_;
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
lean_del_object(v___x_1627_);
lean_dec_ref(v_a_1625_);
lean_dec_ref(v_f_1581_);
v_a_1643_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1629_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1629_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(lean_object* v_f_1652_, size_t v_sz_1653_, size_t v_i_1654_, lean_object* v_bs_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
uint8_t v___x_1661_; 
v___x_1661_ = lean_usize_dec_lt(v_i_1654_, v_sz_1653_);
if (v___x_1661_ == 0)
{
lean_object* v___x_1662_; 
lean_dec_ref(v_f_1652_);
v___x_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1662_, 0, v_bs_1655_);
return v___x_1662_;
}
else
{
lean_object* v_v_1663_; lean_object* v___x_1664_; 
v_v_1663_ = lean_array_uget_borrowed(v_bs_1655_, v_i_1654_);
lean_inc(v_v_1663_);
lean_inc_ref(v_f_1652_);
v___x_1664_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1652_, v_v_1663_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; lean_object* v___x_1666_; lean_object* v_bs_x27_1667_; size_t v___x_1668_; size_t v___x_1669_; lean_object* v___x_1670_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_a_1665_);
lean_dec_ref_known(v___x_1664_, 1);
v___x_1666_ = lean_unsigned_to_nat(0u);
v_bs_x27_1667_ = lean_array_uset(v_bs_1655_, v_i_1654_, v___x_1666_);
v___x_1668_ = ((size_t)1ULL);
v___x_1669_ = lean_usize_add(v_i_1654_, v___x_1668_);
v___x_1670_ = lean_array_uset(v_bs_x27_1667_, v_i_1654_, v_a_1665_);
v_i_1654_ = v___x_1669_;
v_bs_1655_ = v___x_1670_;
goto _start;
}
else
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
lean_dec_ref(v_bs_1655_);
lean_dec_ref(v_f_1652_);
v_a_1672_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1664_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1664_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_1680_, lean_object* v_sz_1681_, lean_object* v_i_1682_, lean_object* v_bs_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
size_t v_sz_boxed_1689_; size_t v_i_boxed_1690_; lean_object* v_res_1691_; 
v_sz_boxed_1689_ = lean_unbox_usize(v_sz_1681_);
lean_dec(v_sz_1681_);
v_i_boxed_1690_ = lean_unbox_usize(v_i_1682_);
lean_dec(v_i_1682_);
v_res_1691_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_1680_, v_sz_boxed_1689_, v_i_boxed_1690_, v_bs_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg___boxed(lean_object* v_f_1692_, lean_object* v_x_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1692_, v_x_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(lean_object* v_t_1700_, lean_object* v_k_1701_){
_start:
{
if (lean_obj_tag(v_t_1700_) == 0)
{
lean_object* v_k_1702_; lean_object* v_v_1703_; lean_object* v_l_1704_; lean_object* v_r_1705_; uint8_t v___x_1706_; 
v_k_1702_ = lean_ctor_get(v_t_1700_, 1);
v_v_1703_ = lean_ctor_get(v_t_1700_, 2);
v_l_1704_ = lean_ctor_get(v_t_1700_, 3);
v_r_1705_ = lean_ctor_get(v_t_1700_, 4);
v___x_1706_ = lean_nat_dec_lt(v_k_1701_, v_k_1702_);
if (v___x_1706_ == 0)
{
uint8_t v___x_1707_; 
v___x_1707_ = lean_nat_dec_eq(v_k_1701_, v_k_1702_);
if (v___x_1707_ == 0)
{
v_t_1700_ = v_r_1705_;
goto _start;
}
else
{
lean_object* v___x_1709_; 
lean_inc(v_v_1703_);
v___x_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1709_, 0, v_v_1703_);
return v___x_1709_;
}
}
else
{
v_t_1700_ = v_l_1704_;
goto _start;
}
}
else
{
lean_object* v___x_1711_; 
v___x_1711_ = lean_box(0);
return v___x_1711_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg___boxed(lean_object* v_t_1712_, lean_object* v_k_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_t_1712_, v_k_1713_);
lean_dec(v_k_1713_);
lean_dec(v_t_1712_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0(lean_object* v_pm_1715_, lean_object* v_merger_1716_, lean_object* v_info_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v_subexprPos_1723_; lean_object* v___x_1724_; 
v_subexprPos_1723_ = lean_ctor_get(v_info_1717_, 1);
v___x_1724_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_pm_1715_, v_subexprPos_1723_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v___x_1725_; 
lean_dec_ref(v_merger_1716_);
v___x_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1725_, 0, v_info_1717_);
return v___x_1725_;
}
else
{
lean_object* v_val_1726_; lean_object* v___x_1727_; 
v_val_1726_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_val_1726_);
lean_dec_ref_known(v___x_1724_, 1);
lean_inc(v___y_1721_);
lean_inc_ref(v___y_1720_);
lean_inc(v___y_1719_);
lean_inc_ref(v___y_1718_);
v___x_1727_ = lean_apply_7(v_merger_1716_, v_info_1717_, v_val_1726_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, lean_box(0));
return v___x_1727_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0___boxed(lean_object* v_pm_1728_, lean_object* v_merger_1729_, lean_object* v_info_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0(v_pm_1728_, v_merger_1729_, v_info_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v_pm_1728_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(lean_object* v_merger_1737_, lean_object* v_pm_1738_, lean_object* v_tt_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
if (lean_obj_tag(v_pm_1738_) == 0)
{
lean_object* v___f_1745_; lean_object* v___x_1746_; 
v___f_1745_ = lean_alloc_closure((void*)(l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1745_, 0, v_pm_1738_);
lean_closure_set(v___f_1745_, 1, v_merger_1737_);
v___x_1746_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v___f_1745_, v_tt_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
return v___x_1746_;
}
else
{
lean_object* v___x_1747_; 
lean_dec_ref(v_merger_1737_);
v___x_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1747_, 0, v_tt_1739_);
return v___x_1747_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___boxed(lean_object* v_merger_1748_, lean_object* v_pm_1749_, lean_object* v_tt_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v_merger_1748_, v_pm_1749_, v_tt_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(uint8_t v_useAfter_1757_, lean_object* v_diff_1758_, lean_object* v_info_u2081_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_){
_start:
{
lean_object* v___x_1765_; lean_object* v___f_1766_; 
v___x_1765_ = lean_box(v_useAfter_1757_);
v___f_1766_ = lean_alloc_closure((void*)(l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1766_, 0, v___x_1765_);
if (v_useAfter_1757_ == 0)
{
lean_object* v_changesBefore_1767_; lean_object* v___x_1768_; 
v_changesBefore_1767_ = lean_ctor_get(v_diff_1758_, 0);
lean_inc(v_changesBefore_1767_);
lean_dec_ref(v_diff_1758_);
v___x_1768_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v___f_1766_, v_changesBefore_1767_, v_info_u2081_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_);
return v___x_1768_;
}
else
{
lean_object* v_changesAfter_1769_; lean_object* v___x_1770_; 
v_changesAfter_1769_ = lean_ctor_get(v_diff_1758_, 1);
lean_inc(v_changesAfter_1769_);
lean_dec_ref(v_diff_1758_);
v___x_1770_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v___f_1766_, v_changesAfter_1769_, v_info_u2081_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_);
return v___x_1770_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___boxed(lean_object* v_useAfter_1771_, lean_object* v_diff_1772_, lean_object* v_info_u2081_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_){
_start:
{
uint8_t v_useAfter_boxed_1779_; lean_object* v_res_1780_; 
v_useAfter_boxed_1779_ = lean_unbox(v_useAfter_1771_);
v_res_1780_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(v_useAfter_boxed_1779_, v_diff_1772_, v_info_u2081_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_);
lean_dec(v_a_1777_);
lean_dec_ref(v_a_1776_);
lean_dec(v_a_1775_);
lean_dec_ref(v_a_1774_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0(lean_object* v_00_u03b1_1781_, lean_object* v_merger_1782_, lean_object* v_pm_1783_, lean_object* v_tt_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v_merger_1782_, v_pm_1783_, v_tt_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___boxed(lean_object* v_00_u03b1_1791_, lean_object* v_merger_1792_, lean_object* v_pm_1793_, lean_object* v_tt_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0(v_00_u03b1_1791_, v_merger_1792_, v_pm_1793_, v_tt_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0(lean_object* v_00_u03b4_1801_, lean_object* v_t_1802_, lean_object* v_k_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_t_1802_, v_k_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___boxed(lean_object* v_00_u03b4_1805_, lean_object* v_t_1806_, lean_object* v_k_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0(v_00_u03b4_1805_, v_t_1806_, v_k_1807_);
lean_dec(v_k_1807_);
lean_dec(v_t_1806_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1(lean_object* v_00_u03b1_1809_, lean_object* v_00_u03b2_1810_, lean_object* v_f_1811_, lean_object* v_x_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1811_, v_x_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1819_, lean_object* v_00_u03b2_1820_, lean_object* v_f_1821_, lean_object* v_x_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1(v_00_u03b1_1819_, v_00_u03b2_1820_, v_f_1821_, v_x_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1829_, lean_object* v_00_u03b2_1830_, lean_object* v_f_1831_, size_t v_sz_1832_, size_t v_i_1833_, lean_object* v_bs_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_1831_, v_sz_1832_, v_i_1833_, v_bs_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1841_, lean_object* v_00_u03b2_1842_, lean_object* v_f_1843_, lean_object* v_sz_1844_, lean_object* v_i_1845_, lean_object* v_bs_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
size_t v_sz_boxed_1852_; size_t v_i_boxed_1853_; lean_object* v_res_1854_; 
v_sz_boxed_1852_ = lean_unbox_usize(v_sz_1844_);
lean_dec(v_sz_1844_);
v_i_boxed_1853_ = lean_unbox_usize(v_i_1845_);
lean_dec(v_i_1845_);
v_res_1854_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2(v_00_u03b1_1841_, v_00_u03b2_1842_, v_f_1843_, v_sz_boxed_1852_, v_i_boxed_1853_, v_bs_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(lean_object* v_e_1855_, lean_object* v___y_1856_){
_start:
{
uint8_t v___x_1858_; 
v___x_1858_ = l_Lean_Expr_hasMVar(v_e_1855_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1859_; 
v___x_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1859_, 0, v_e_1855_);
return v___x_1859_;
}
else
{
lean_object* v___x_1860_; lean_object* v_mctx_1861_; lean_object* v___x_1862_; lean_object* v_fst_1863_; lean_object* v_snd_1864_; lean_object* v___x_1865_; lean_object* v_cache_1866_; lean_object* v_zetaDeltaFVarIds_1867_; lean_object* v_postponed_1868_; lean_object* v_diag_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1878_; 
v___x_1860_ = lean_st_ref_get(v___y_1856_);
v_mctx_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc_ref(v_mctx_1861_);
lean_dec(v___x_1860_);
v___x_1862_ = l_Lean_instantiateMVarsCore(v_mctx_1861_, v_e_1855_);
v_fst_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_fst_1863_);
v_snd_1864_ = lean_ctor_get(v___x_1862_, 1);
lean_inc(v_snd_1864_);
lean_dec_ref(v___x_1862_);
v___x_1865_ = lean_st_ref_take(v___y_1856_);
v_cache_1866_ = lean_ctor_get(v___x_1865_, 1);
v_zetaDeltaFVarIds_1867_ = lean_ctor_get(v___x_1865_, 2);
v_postponed_1868_ = lean_ctor_get(v___x_1865_, 3);
v_diag_1869_ = lean_ctor_get(v___x_1865_, 4);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1878_ == 0)
{
lean_object* v_unused_1879_; 
v_unused_1879_ = lean_ctor_get(v___x_1865_, 0);
lean_dec(v_unused_1879_);
v___x_1871_ = v___x_1865_;
v_isShared_1872_ = v_isSharedCheck_1878_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_diag_1869_);
lean_inc(v_postponed_1868_);
lean_inc(v_zetaDeltaFVarIds_1867_);
lean_inc(v_cache_1866_);
lean_dec(v___x_1865_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1878_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v_snd_1864_);
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_snd_1864_);
lean_ctor_set(v_reuseFailAlloc_1877_, 1, v_cache_1866_);
lean_ctor_set(v_reuseFailAlloc_1877_, 2, v_zetaDeltaFVarIds_1867_);
lean_ctor_set(v_reuseFailAlloc_1877_, 3, v_postponed_1868_);
lean_ctor_set(v_reuseFailAlloc_1877_, 4, v_diag_1869_);
v___x_1874_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1875_ = lean_st_ref_set(v___y_1856_, v___x_1874_);
v___x_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1876_, 0, v_fst_1863_);
return v___x_1876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg___boxed(lean_object* v_e_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_e_1880_, v___y_1881_);
lean_dec(v___y_1881_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0(lean_object* v_e_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_e_1884_, v___y_1886_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___boxed(lean_object* v_e_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0(v_e_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
return v_res_1897_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1(void){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__0));
v___x_1900_ = l_Lean_stringToMessageData(v___x_1899_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(uint8_t v_useAfter_1901_, lean_object* v_t_u2080_1902_, lean_object* v_h_u2081_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v_names_1909_; lean_object* v_fvarIds_1910_; lean_object* v_type_1911_; lean_object* v_val_x3f_1912_; lean_object* v_isInstance_x3f_1913_; lean_object* v_isType_x3f_1914_; lean_object* v_isInserted_x3f_1915_; lean_object* v_isRemoved_x3f_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1971_; 
v_names_1909_ = lean_ctor_get(v_h_u2081_1903_, 0);
v_fvarIds_1910_ = lean_ctor_get(v_h_u2081_1903_, 1);
v_type_1911_ = lean_ctor_get(v_h_u2081_1903_, 2);
v_val_x3f_1912_ = lean_ctor_get(v_h_u2081_1903_, 3);
v_isInstance_x3f_1913_ = lean_ctor_get(v_h_u2081_1903_, 4);
v_isType_x3f_1914_ = lean_ctor_get(v_h_u2081_1903_, 5);
v_isInserted_x3f_1915_ = lean_ctor_get(v_h_u2081_1903_, 6);
v_isRemoved_x3f_1916_ = lean_ctor_get(v_h_u2081_1903_, 7);
v_isSharedCheck_1971_ = !lean_is_exclusive(v_h_u2081_1903_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1918_ = v_h_u2081_1903_;
v_isShared_1919_ = v_isSharedCheck_1971_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_isRemoved_x3f_1916_);
lean_inc(v_isInserted_x3f_1915_);
lean_inc(v_isType_x3f_1914_);
lean_inc(v_isInstance_x3f_1913_);
lean_inc(v_val_x3f_1912_);
lean_inc(v_type_1911_);
lean_inc(v_fvarIds_1910_);
lean_inc(v_names_1909_);
lean_dec(v_h_u2081_1903_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1971_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___y_1921_; lean_object* v___x_1961_; lean_object* v___x_1962_; uint8_t v___x_1963_; 
v___x_1961_ = lean_unsigned_to_nat(0u);
v___x_1962_ = lean_array_get_size(v_fvarIds_1910_);
v___x_1963_ = lean_nat_dec_lt(v___x_1961_, v___x_1962_);
if (v___x_1963_ == 0)
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
lean_del_object(v___x_1918_);
lean_dec(v_isRemoved_x3f_1916_);
lean_dec(v_isInserted_x3f_1915_);
lean_dec(v_isType_x3f_1914_);
lean_dec(v_isInstance_x3f_1913_);
lean_dec(v_val_x3f_1912_);
lean_dec_ref(v_type_1911_);
lean_dec_ref(v_fvarIds_1910_);
lean_dec_ref(v_names_1909_);
lean_dec_ref(v_t_u2080_1902_);
v___x_1964_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1);
v___x_1965_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_1964_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
return v___x_1965_;
}
else
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1966_ = lean_array_fget_borrowed(v_fvarIds_1910_, v___x_1961_);
lean_inc(v___x_1966_);
v___x_1967_ = l_Lean_Expr_fvar___override(v___x_1966_);
lean_inc(v_a_1907_);
lean_inc_ref(v_a_1906_);
lean_inc(v_a_1905_);
lean_inc_ref(v_a_1904_);
v___x_1968_ = lean_infer_type(v___x_1967_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1970_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref_known(v___x_1968_, 1);
v___x_1970_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_a_1969_, v_a_1905_);
v___y_1921_ = v___x_1970_;
goto v___jp_1920_;
}
else
{
v___y_1921_ = v___x_1968_;
goto v___jp_1920_;
}
}
v___jp_1920_:
{
if (lean_obj_tag(v___y_1921_) == 0)
{
lean_object* v_a_1922_; lean_object* v___x_1923_; 
v_a_1922_ = lean_ctor_get(v___y_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref_known(v___y_1921_, 1);
v___x_1923_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(v_t_u2080_1902_, v_a_1922_, v_useAfter_1901_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1925_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___x_1923_, 1);
v___x_1925_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(v_useAfter_1901_, v_a_1924_, v_type_1911_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1936_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1928_ = v___x_1925_;
v_isShared_1929_ = v_isSharedCheck_1936_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1925_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1936_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 2, v_a_1926_);
v___x_1931_ = v___x_1918_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_names_1909_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_fvarIds_1910_);
lean_ctor_set(v_reuseFailAlloc_1935_, 2, v_a_1926_);
lean_ctor_set(v_reuseFailAlloc_1935_, 3, v_val_x3f_1912_);
lean_ctor_set(v_reuseFailAlloc_1935_, 4, v_isInstance_x3f_1913_);
lean_ctor_set(v_reuseFailAlloc_1935_, 5, v_isType_x3f_1914_);
lean_ctor_set(v_reuseFailAlloc_1935_, 6, v_isInserted_x3f_1915_);
lean_ctor_set(v_reuseFailAlloc_1935_, 7, v_isRemoved_x3f_1916_);
v___x_1931_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
lean_object* v___x_1933_; 
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 0, v___x_1931_);
v___x_1933_ = v___x_1928_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1931_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
lean_del_object(v___x_1918_);
lean_dec(v_isRemoved_x3f_1916_);
lean_dec(v_isInserted_x3f_1915_);
lean_dec(v_isType_x3f_1914_);
lean_dec(v_isInstance_x3f_1913_);
lean_dec(v_val_x3f_1912_);
lean_dec_ref(v_fvarIds_1910_);
lean_dec_ref(v_names_1909_);
v_a_1937_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1925_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1925_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_del_object(v___x_1918_);
lean_dec(v_isRemoved_x3f_1916_);
lean_dec(v_isInserted_x3f_1915_);
lean_dec(v_isType_x3f_1914_);
lean_dec(v_isInstance_x3f_1913_);
lean_dec(v_val_x3f_1912_);
lean_dec_ref(v_type_1911_);
lean_dec_ref(v_fvarIds_1910_);
lean_dec_ref(v_names_1909_);
v_a_1945_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1923_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1923_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_del_object(v___x_1918_);
lean_dec(v_isRemoved_x3f_1916_);
lean_dec(v_isInserted_x3f_1915_);
lean_dec(v_isType_x3f_1914_);
lean_dec(v_isInstance_x3f_1913_);
lean_dec(v_val_x3f_1912_);
lean_dec_ref(v_type_1911_);
lean_dec_ref(v_fvarIds_1910_);
lean_dec_ref(v_names_1909_);
lean_dec_ref(v_t_u2080_1902_);
v_a_1953_ = lean_ctor_get(v___y_1921_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___y_1921_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___y_1921_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___y_1921_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___boxed(lean_object* v_useAfter_1972_, lean_object* v_t_u2080_1973_, lean_object* v_h_u2081_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_){
_start:
{
uint8_t v_useAfter_boxed_1980_; lean_object* v_res_1981_; 
v_useAfter_boxed_1980_ = lean_unbox(v_useAfter_1972_);
v_res_1981_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(v_useAfter_boxed_1980_, v_t_u2080_1973_, v_h_u2081_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
lean_dec(v_a_1978_);
lean_dec_ref(v_a_1977_);
lean_dec(v_a_1976_);
lean_dec_ref(v_a_1975_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(lean_object* v_ctx_u2080_1985_, uint8_t v_useAfter_1986_, lean_object* v_h_u2081_1987_, lean_object* v___x_1988_, lean_object* v___x_1989_, lean_object* v_as_1990_, size_t v_sz_1991_, size_t v_i_1992_, lean_object* v_b_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
uint8_t v___x_1999_; 
v___x_1999_ = lean_usize_dec_lt(v_i_1992_, v_sz_1991_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; 
lean_dec_ref(v___x_1989_);
lean_dec_ref(v___x_1988_);
lean_dec_ref(v_h_u2081_1987_);
v___x_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2000_, 0, v_b_1993_);
return v___x_2000_;
}
else
{
lean_object* v_a_2001_; lean_object* v_fst_2002_; lean_object* v_snd_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2099_; 
lean_dec_ref(v_b_1993_);
v_a_2001_ = lean_array_uget(v_as_1990_, v_i_1992_);
v_fst_2002_ = lean_ctor_get(v_a_2001_, 0);
v_snd_2003_ = lean_ctor_get(v_a_2001_, 1);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_a_2001_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2005_ = v_a_2001_;
v_isShared_2006_ = v_isSharedCheck_2099_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_snd_2003_);
lean_inc(v_fst_2002_);
lean_dec(v_a_2001_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2099_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2007_; uint8_t v___x_2008_; 
v___x_2007_ = lean_box(0);
v___x_2008_ = l_Lean_LocalContext_contains(v_ctx_u2080_1985_, v_snd_2003_);
lean_dec(v_snd_2003_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2009_ = lean_box(0);
v___x_2010_ = l_Lean_Name_str___override(v___x_2009_, v_fst_2002_);
v___x_2011_ = l_Lean_LocalContext_findFromUserName_x3f(v_ctx_u2080_1985_, v___x_2010_);
lean_dec(v___x_2010_);
if (lean_obj_tag(v___x_2011_) == 1)
{
lean_object* v_val_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2050_; 
lean_dec_ref(v___x_1989_);
lean_dec_ref(v___x_1988_);
v_val_2012_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2014_ = v___x_2011_;
v_isShared_2015_ = v_isSharedCheck_2050_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_val_2012_);
lean_dec(v___x_2011_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2050_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2016_ = l_Lean_LocalDecl_type(v_val_2012_);
lean_dec(v_val_2012_);
v___x_2017_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v___x_2016_, v___y_1995_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v___x_2019_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_a_2018_);
lean_dec_ref_known(v___x_2017_, 1);
v___x_2019_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(v_useAfter_1986_, v_a_2018_, v_h_u2081_1987_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2033_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2022_ = v___x_2019_;
v_isShared_2023_ = v_isSharedCheck_2033_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2019_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2033_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v_a_2020_);
v___x_2025_ = v___x_2014_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
lean_object* v___x_2027_; 
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 1, v___x_2007_);
lean_ctor_set(v___x_2005_, 0, v___x_2025_);
v___x_2027_ = v___x_2005_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2025_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v___x_2007_);
v___x_2027_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
lean_object* v___x_2029_; 
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 0, v___x_2027_);
v___x_2029_ = v___x_2022_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
lean_del_object(v___x_2014_);
lean_del_object(v___x_2005_);
v_a_2034_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_2019_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2019_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_del_object(v___x_2014_);
lean_del_object(v___x_2005_);
lean_dec_ref(v_h_u2081_1987_);
v_a_2042_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2017_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2017_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
}
else
{
lean_dec(v___x_2011_);
if (v_useAfter_1986_ == 0)
{
lean_object* v_type_2051_; lean_object* v_val_x3f_2052_; lean_object* v_isInstance_x3f_2053_; lean_object* v_isType_x3f_2054_; lean_object* v_isInserted_x3f_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2069_; 
v_type_2051_ = lean_ctor_get(v_h_u2081_1987_, 2);
v_val_x3f_2052_ = lean_ctor_get(v_h_u2081_1987_, 3);
v_isInstance_x3f_2053_ = lean_ctor_get(v_h_u2081_1987_, 4);
v_isType_x3f_2054_ = lean_ctor_get(v_h_u2081_1987_, 5);
v_isInserted_x3f_2055_ = lean_ctor_get(v_h_u2081_1987_, 6);
v_isSharedCheck_2069_ = !lean_is_exclusive(v_h_u2081_1987_);
if (v_isSharedCheck_2069_ == 0)
{
lean_object* v_unused_2070_; lean_object* v_unused_2071_; lean_object* v_unused_2072_; 
v_unused_2070_ = lean_ctor_get(v_h_u2081_1987_, 7);
lean_dec(v_unused_2070_);
v_unused_2071_ = lean_ctor_get(v_h_u2081_1987_, 1);
lean_dec(v_unused_2071_);
v_unused_2072_ = lean_ctor_get(v_h_u2081_1987_, 0);
lean_dec(v_unused_2072_);
v___x_2057_ = v_h_u2081_1987_;
v_isShared_2058_ = v_isSharedCheck_2069_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_isInserted_x3f_2055_);
lean_inc(v_isType_x3f_2054_);
lean_inc(v_isInstance_x3f_2053_);
lean_inc(v_val_x3f_2052_);
lean_inc(v_type_2051_);
lean_dec(v_h_u2081_1987_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2069_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2062_; 
v___x_2059_ = lean_box(v___x_1999_);
v___x_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2059_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 7, v___x_2060_);
lean_ctor_set(v___x_2057_, 1, v___x_1989_);
lean_ctor_set(v___x_2057_, 0, v___x_1988_);
v___x_2062_ = v___x_2057_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v___x_1989_);
lean_ctor_set(v_reuseFailAlloc_2068_, 2, v_type_2051_);
lean_ctor_set(v_reuseFailAlloc_2068_, 3, v_val_x3f_2052_);
lean_ctor_set(v_reuseFailAlloc_2068_, 4, v_isInstance_x3f_2053_);
lean_ctor_set(v_reuseFailAlloc_2068_, 5, v_isType_x3f_2054_);
lean_ctor_set(v_reuseFailAlloc_2068_, 6, v_isInserted_x3f_2055_);
lean_ctor_set(v_reuseFailAlloc_2068_, 7, v___x_2060_);
v___x_2062_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
lean_object* v___x_2063_; lean_object* v___x_2065_; 
v___x_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 1, v___x_2007_);
lean_ctor_set(v___x_2005_, 0, v___x_2063_);
v___x_2065_ = v___x_2005_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2063_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v___x_2007_);
v___x_2065_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
lean_object* v___x_2066_; 
v___x_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
return v___x_2066_;
}
}
}
}
else
{
lean_object* v_type_2073_; lean_object* v_val_x3f_2074_; lean_object* v_isInstance_x3f_2075_; lean_object* v_isType_x3f_2076_; lean_object* v_isRemoved_x3f_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2091_; 
v_type_2073_ = lean_ctor_get(v_h_u2081_1987_, 2);
v_val_x3f_2074_ = lean_ctor_get(v_h_u2081_1987_, 3);
v_isInstance_x3f_2075_ = lean_ctor_get(v_h_u2081_1987_, 4);
v_isType_x3f_2076_ = lean_ctor_get(v_h_u2081_1987_, 5);
v_isRemoved_x3f_2077_ = lean_ctor_get(v_h_u2081_1987_, 7);
v_isSharedCheck_2091_ = !lean_is_exclusive(v_h_u2081_1987_);
if (v_isSharedCheck_2091_ == 0)
{
lean_object* v_unused_2092_; lean_object* v_unused_2093_; lean_object* v_unused_2094_; 
v_unused_2092_ = lean_ctor_get(v_h_u2081_1987_, 6);
lean_dec(v_unused_2092_);
v_unused_2093_ = lean_ctor_get(v_h_u2081_1987_, 1);
lean_dec(v_unused_2093_);
v_unused_2094_ = lean_ctor_get(v_h_u2081_1987_, 0);
lean_dec(v_unused_2094_);
v___x_2079_ = v_h_u2081_1987_;
v_isShared_2080_ = v_isSharedCheck_2091_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_isRemoved_x3f_2077_);
lean_inc(v_isType_x3f_2076_);
lean_inc(v_isInstance_x3f_2075_);
lean_inc(v_val_x3f_2074_);
lean_inc(v_type_2073_);
lean_dec(v_h_u2081_1987_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2091_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2084_; 
v___x_2081_ = lean_box(v___x_1999_);
v___x_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 6, v___x_2082_);
lean_ctor_set(v___x_2079_, 1, v___x_1989_);
lean_ctor_set(v___x_2079_, 0, v___x_1988_);
v___x_2084_ = v___x_2079_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v___x_1989_);
lean_ctor_set(v_reuseFailAlloc_2090_, 2, v_type_2073_);
lean_ctor_set(v_reuseFailAlloc_2090_, 3, v_val_x3f_2074_);
lean_ctor_set(v_reuseFailAlloc_2090_, 4, v_isInstance_x3f_2075_);
lean_ctor_set(v_reuseFailAlloc_2090_, 5, v_isType_x3f_2076_);
lean_ctor_set(v_reuseFailAlloc_2090_, 6, v___x_2082_);
lean_ctor_set(v_reuseFailAlloc_2090_, 7, v_isRemoved_x3f_2077_);
v___x_2084_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
lean_object* v___x_2085_; lean_object* v___x_2087_; 
v___x_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 1, v___x_2007_);
lean_ctor_set(v___x_2005_, 0, v___x_2085_);
v___x_2087_ = v___x_2005_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2085_);
lean_ctor_set(v_reuseFailAlloc_2089_, 1, v___x_2007_);
v___x_2087_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
lean_object* v___x_2088_; 
v___x_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
return v___x_2088_;
}
}
}
}
}
}
else
{
lean_object* v___x_2095_; size_t v___x_2096_; size_t v___x_2097_; 
lean_del_object(v___x_2005_);
lean_dec(v_fst_2002_);
v___x_2095_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___closed__0));
v___x_2096_ = ((size_t)1ULL);
v___x_2097_ = lean_usize_add(v_i_1992_, v___x_2096_);
v_i_1992_ = v___x_2097_;
v_b_1993_ = v___x_2095_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___boxed(lean_object* v_ctx_u2080_2100_, lean_object* v_useAfter_2101_, lean_object* v_h_u2081_2102_, lean_object* v___x_2103_, lean_object* v___x_2104_, lean_object* v_as_2105_, lean_object* v_sz_2106_, lean_object* v_i_2107_, lean_object* v_b_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
uint8_t v_useAfter_boxed_2114_; size_t v_sz_boxed_2115_; size_t v_i_boxed_2116_; lean_object* v_res_2117_; 
v_useAfter_boxed_2114_ = lean_unbox(v_useAfter_2101_);
v_sz_boxed_2115_ = lean_unbox_usize(v_sz_2106_);
lean_dec(v_sz_2106_);
v_i_boxed_2116_ = lean_unbox_usize(v_i_2107_);
lean_dec(v_i_2107_);
v_res_2117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(v_ctx_u2080_2100_, v_useAfter_boxed_2114_, v_h_u2081_2102_, v___x_2103_, v___x_2104_, v_as_2105_, v_sz_boxed_2115_, v_i_boxed_2116_, v_b_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec_ref(v_as_2105_);
lean_dec_ref(v_ctx_u2080_2100_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(uint8_t v_useAfter_2118_, lean_object* v_ctx_u2080_2119_, lean_object* v_h_u2081_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_){
_start:
{
lean_object* v_names_2126_; lean_object* v_fvarIds_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; size_t v_sz_2130_; size_t v___x_2131_; lean_object* v___x_2132_; 
v_names_2126_ = lean_ctor_get(v_h_u2081_2120_, 0);
v_fvarIds_2127_ = lean_ctor_get(v_h_u2081_2120_, 1);
v___x_2128_ = l_Array_zip___redArg(v_names_2126_, v_fvarIds_2127_);
v___x_2129_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___closed__0));
v_sz_2130_ = lean_array_size(v___x_2128_);
v___x_2131_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_2127_);
lean_inc_ref(v_names_2126_);
lean_inc_ref(v_h_u2081_2120_);
v___x_2132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(v_ctx_u2080_2119_, v_useAfter_2118_, v_h_u2081_2120_, v_names_2126_, v_fvarIds_2127_, v___x_2128_, v_sz_2130_, v___x_2131_, v___x_2129_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
lean_dec_ref(v___x_2128_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2145_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2135_ = v___x_2132_;
v_isShared_2136_ = v_isSharedCheck_2145_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2132_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2145_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v_fst_2137_; 
v_fst_2137_ = lean_ctor_get(v_a_2133_, 0);
lean_inc(v_fst_2137_);
lean_dec(v_a_2133_);
if (lean_obj_tag(v_fst_2137_) == 0)
{
lean_object* v___x_2139_; 
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v_h_u2081_2120_);
v___x_2139_ = v___x_2135_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_h_u2081_2120_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
else
{
lean_object* v_val_2141_; lean_object* v___x_2143_; 
lean_dec_ref(v_h_u2081_2120_);
v_val_2141_ = lean_ctor_get(v_fst_2137_, 0);
lean_inc(v_val_2141_);
lean_dec_ref_known(v_fst_2137_, 1);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v_val_2141_);
v___x_2143_ = v___x_2135_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_val_2141_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec_ref(v_h_u2081_2120_);
v_a_2146_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2132_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2132_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle___boxed(lean_object* v_useAfter_2154_, lean_object* v_ctx_u2080_2155_, lean_object* v_h_u2081_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_){
_start:
{
uint8_t v_useAfter_boxed_2162_; lean_object* v_res_2163_; 
v_useAfter_boxed_2162_ = lean_unbox(v_useAfter_2154_);
v_res_2163_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(v_useAfter_boxed_2162_, v_ctx_u2080_2155_, v_h_u2081_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
lean_dec(v_a_2160_);
lean_dec_ref(v_a_2159_);
lean_dec(v_a_2158_);
lean_dec_ref(v_a_2157_);
lean_dec_ref(v_ctx_u2080_2155_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(uint8_t v_useAfter_2164_, lean_object* v_lctx_u2080_2165_, size_t v_sz_2166_, size_t v_i_2167_, lean_object* v_bs_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
uint8_t v___x_2174_; 
v___x_2174_ = lean_usize_dec_lt(v_i_2167_, v_sz_2166_);
if (v___x_2174_ == 0)
{
lean_object* v___x_2175_; 
v___x_2175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2175_, 0, v_bs_2168_);
return v___x_2175_;
}
else
{
lean_object* v_v_2176_; lean_object* v___x_2177_; 
v_v_2176_ = lean_array_uget_borrowed(v_bs_2168_, v_i_2167_);
lean_inc(v_v_2176_);
v___x_2177_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(v_useAfter_2164_, v_lctx_u2080_2165_, v_v_2176_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2179_; lean_object* v_bs_x27_2180_; size_t v___x_2181_; size_t v___x_2182_; lean_object* v___x_2183_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2177_, 1);
v___x_2179_ = lean_unsigned_to_nat(0u);
v_bs_x27_2180_ = lean_array_uset(v_bs_2168_, v_i_2167_, v___x_2179_);
v___x_2181_ = ((size_t)1ULL);
v___x_2182_ = lean_usize_add(v_i_2167_, v___x_2181_);
v___x_2183_ = lean_array_uset(v_bs_x27_2180_, v_i_2167_, v_a_2178_);
v_i_2167_ = v___x_2182_;
v_bs_2168_ = v___x_2183_;
goto _start;
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_dec_ref(v_bs_2168_);
v_a_2185_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2177_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2177_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0___boxed(lean_object* v_useAfter_2193_, lean_object* v_lctx_u2080_2194_, lean_object* v_sz_2195_, lean_object* v_i_2196_, lean_object* v_bs_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
uint8_t v_useAfter_boxed_2203_; size_t v_sz_boxed_2204_; size_t v_i_boxed_2205_; lean_object* v_res_2206_; 
v_useAfter_boxed_2203_ = lean_unbox(v_useAfter_2193_);
v_sz_boxed_2204_ = lean_unbox_usize(v_sz_2195_);
lean_dec(v_sz_2195_);
v_i_boxed_2205_ = lean_unbox_usize(v_i_2196_);
lean_dec(v_i_2196_);
v_res_2206_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(v_useAfter_boxed_2203_, v_lctx_u2080_2194_, v_sz_boxed_2204_, v_i_boxed_2205_, v_bs_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec_ref(v_lctx_u2080_2194_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(uint8_t v_useAfter_2207_, lean_object* v_lctx_u2080_2208_, lean_object* v_hs_u2081_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_){
_start:
{
size_t v_sz_2215_; size_t v___x_2216_; lean_object* v___x_2217_; 
v_sz_2215_ = lean_array_size(v_hs_u2081_2209_);
v___x_2216_ = ((size_t)0ULL);
v___x_2217_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(v_useAfter_2207_, v_lctx_u2080_2208_, v_sz_2215_, v___x_2216_, v_hs_u2081_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses___boxed(lean_object* v_useAfter_2218_, lean_object* v_lctx_u2080_2219_, lean_object* v_hs_u2081_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_){
_start:
{
uint8_t v_useAfter_boxed_2226_; lean_object* v_res_2227_; 
v_useAfter_boxed_2226_ = lean_unbox(v_useAfter_2218_);
v_res_2227_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(v_useAfter_boxed_2226_, v_lctx_u2080_2219_, v_hs_u2081_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_);
lean_dec(v_a_2224_);
lean_dec_ref(v_a_2223_);
lean_dec(v_a_2222_);
lean_dec_ref(v_a_2221_);
lean_dec_ref(v_lctx_u2080_2219_);
return v_res_2227_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2(void){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2232_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__1));
v___x_2233_ = l_Lean_stringToMessageData(v___x_2232_);
return v___x_2233_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4(void){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2235_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__3));
v___x_2236_ = l_Lean_stringToMessageData(v___x_2235_);
return v___x_2236_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6(void){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__5));
v___x_2239_ = l_Lean_stringToMessageData(v___x_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(uint8_t v_useAfter_2240_, lean_object* v_g_u2080_2241_, lean_object* v_i_u2081_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_){
_start:
{
lean_object* v___x_2248_; lean_object* v_mctx_2249_; lean_object* v___x_2250_; 
v___x_2248_ = lean_st_ref_get(v_a_2244_);
v_mctx_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc_ref(v_mctx_2249_);
lean_dec(v___x_2248_);
v___x_2250_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2249_, v_g_u2080_2241_);
lean_dec_ref(v_mctx_2249_);
if (lean_obj_tag(v___x_2250_) == 1)
{
lean_object* v_val_2251_; lean_object* v_options_2252_; lean_object* v_lctx_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v_toInteractiveGoalCore_2257_; lean_object* v_fst_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2355_; 
v_val_2251_ = lean_ctor_get(v___x_2250_, 0);
lean_inc(v_val_2251_);
lean_dec_ref_known(v___x_2250_, 1);
v_options_2252_ = lean_ctor_get(v_a_2245_, 2);
v_lctx_2253_ = lean_ctor_get(v_val_2251_, 1);
lean_inc_ref(v_lctx_2253_);
lean_dec(v_val_2251_);
v___x_2254_ = lean_box(1);
lean_inc_ref(v_options_2252_);
v___x_2255_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2255_, 0, v_options_2252_);
lean_ctor_set(v___x_2255_, 1, v___x_2254_);
lean_ctor_set(v___x_2255_, 2, v___x_2254_);
v___x_2256_ = l_Lean_LocalContext_sanitizeNames(v_lctx_2253_, v___x_2255_);
v_toInteractiveGoalCore_2257_ = lean_ctor_get(v_i_u2081_2242_, 0);
lean_inc_ref(v_toInteractiveGoalCore_2257_);
v_fst_2258_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2355_ == 0)
{
lean_object* v_unused_2356_; 
v_unused_2356_ = lean_ctor_get(v___x_2256_, 1);
lean_dec(v_unused_2356_);
v___x_2260_ = v___x_2256_;
v_isShared_2261_ = v_isSharedCheck_2355_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_fst_2258_);
lean_dec(v___x_2256_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2355_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v_userName_x3f_2262_; lean_object* v_goalPrefix_2263_; lean_object* v_mvarId_2264_; lean_object* v_isRemoved_x3f_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2352_; 
v_userName_x3f_2262_ = lean_ctor_get(v_i_u2081_2242_, 1);
v_goalPrefix_2263_ = lean_ctor_get(v_i_u2081_2242_, 2);
v_mvarId_2264_ = lean_ctor_get(v_i_u2081_2242_, 3);
v_isRemoved_x3f_2265_ = lean_ctor_get(v_i_u2081_2242_, 5);
v_isSharedCheck_2352_ = !lean_is_exclusive(v_i_u2081_2242_);
if (v_isSharedCheck_2352_ == 0)
{
lean_object* v_unused_2353_; lean_object* v_unused_2354_; 
v_unused_2353_ = lean_ctor_get(v_i_u2081_2242_, 4);
lean_dec(v_unused_2353_);
v_unused_2354_ = lean_ctor_get(v_i_u2081_2242_, 0);
lean_dec(v_unused_2354_);
v___x_2267_ = v_i_u2081_2242_;
v_isShared_2268_ = v_isSharedCheck_2352_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_isRemoved_x3f_2265_);
lean_inc(v_mvarId_2264_);
lean_inc(v_goalPrefix_2263_);
lean_inc(v_userName_x3f_2262_);
lean_dec(v_i_u2081_2242_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2352_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v_hyps_2269_; lean_object* v_type_2270_; lean_object* v_ctx_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2351_; 
v_hyps_2269_ = lean_ctor_get(v_toInteractiveGoalCore_2257_, 0);
v_type_2270_ = lean_ctor_get(v_toInteractiveGoalCore_2257_, 1);
v_ctx_2271_ = lean_ctor_get(v_toInteractiveGoalCore_2257_, 2);
v_isSharedCheck_2351_ = !lean_is_exclusive(v_toInteractiveGoalCore_2257_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2273_ = v_toInteractiveGoalCore_2257_;
v_isShared_2274_ = v_isSharedCheck_2351_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_ctx_2271_);
lean_inc(v_type_2270_);
lean_inc(v_hyps_2269_);
lean_dec(v_toInteractiveGoalCore_2257_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2351_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2275_; 
v___x_2275_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(v_useAfter_2240_, v_fst_2258_, v_hyps_2269_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_);
lean_dec(v_fst_2258_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_a_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2276_);
lean_dec_ref_known(v___x_2275_, 1);
v___x_2277_ = l_Lean_Expr_mvar___override(v_g_u2080_2241_);
lean_inc(v_a_2246_);
lean_inc_ref(v_a_2245_);
lean_inc(v_a_2244_);
lean_inc_ref(v_a_2243_);
v___x_2278_ = lean_infer_type(v___x_2277_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2280_; lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2334_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_a_2279_);
lean_dec_ref_known(v___x_2278_, 1);
v___x_2280_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_a_2279_, v_a_2244_);
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2283_ = v___x_2280_;
v_isShared_2284_ = v_isSharedCheck_2334_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2280_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2334_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2285_; lean_object* v_mctx_2286_; lean_object* v___x_2287_; 
v___x_2285_ = lean_st_ref_get(v_a_2244_);
v_mctx_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc_ref(v_mctx_2286_);
lean_dec(v___x_2285_);
v___x_2287_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2286_, v_mvarId_2264_);
lean_dec_ref(v_mctx_2286_);
if (lean_obj_tag(v___x_2287_) == 1)
{
lean_object* v_val_2288_; lean_object* v_type_2289_; lean_object* v___x_2290_; lean_object* v_a_2291_; lean_object* v___x_2292_; 
lean_del_object(v___x_2283_);
lean_del_object(v___x_2260_);
v_val_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_val_2288_);
lean_dec_ref_known(v___x_2287_, 1);
v_type_2289_ = lean_ctor_get(v_val_2288_, 2);
lean_inc_ref(v_type_2289_);
lean_dec(v_val_2288_);
v___x_2290_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_type_2289_, v_a_2244_);
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_a_2291_);
lean_dec_ref(v___x_2290_);
v___x_2292_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(v_a_2281_, v_a_2291_, v_useAfter_2240_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v___x_2294_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2293_);
lean_dec_ref_known(v___x_2292_, 1);
v___x_2294_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(v_useAfter_2240_, v_a_2293_, v_type_2270_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2309_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2297_ = v___x_2294_;
v_isShared_2298_ = v_isSharedCheck_2309_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2294_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2309_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 1, v_a_2295_);
lean_ctor_set(v___x_2273_, 0, v_a_2276_);
v___x_2300_ = v___x_2273_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2276_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_a_2295_);
lean_ctor_set(v_reuseFailAlloc_2308_, 2, v_ctx_2271_);
v___x_2300_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
lean_object* v___x_2301_; lean_object* v___x_2303_; 
v___x_2301_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__0));
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v___x_2301_);
lean_ctor_set(v___x_2267_, 0, v___x_2300_);
v___x_2303_ = v___x_2267_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2300_);
lean_ctor_set(v_reuseFailAlloc_2307_, 1, v_userName_x3f_2262_);
lean_ctor_set(v_reuseFailAlloc_2307_, 2, v_goalPrefix_2263_);
lean_ctor_set(v_reuseFailAlloc_2307_, 3, v_mvarId_2264_);
lean_ctor_set(v_reuseFailAlloc_2307_, 4, v___x_2301_);
lean_ctor_set(v_reuseFailAlloc_2307_, 5, v_isRemoved_x3f_2265_);
v___x_2303_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
lean_object* v___x_2305_; 
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 0, v___x_2303_);
v___x_2305_ = v___x_2297_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2303_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_dec(v_a_2276_);
lean_del_object(v___x_2273_);
lean_dec_ref(v_ctx_2271_);
lean_del_object(v___x_2267_);
lean_dec(v_isRemoved_x3f_2265_);
lean_dec(v_mvarId_2264_);
lean_dec_ref(v_goalPrefix_2263_);
lean_dec(v_userName_x3f_2262_);
v_a_2310_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2294_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2294_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_dec(v_a_2276_);
lean_del_object(v___x_2273_);
lean_dec_ref(v_ctx_2271_);
lean_dec_ref(v_type_2270_);
lean_del_object(v___x_2267_);
lean_dec(v_isRemoved_x3f_2265_);
lean_dec(v_mvarId_2264_);
lean_dec_ref(v_goalPrefix_2263_);
lean_dec(v_userName_x3f_2262_);
v_a_2318_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2292_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2292_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
else
{
lean_object* v___x_2326_; lean_object* v___x_2328_; 
lean_dec(v___x_2287_);
lean_dec(v_a_2281_);
lean_dec(v_a_2276_);
lean_del_object(v___x_2273_);
lean_dec_ref(v_ctx_2271_);
lean_dec_ref(v_type_2270_);
lean_del_object(v___x_2267_);
lean_dec(v_isRemoved_x3f_2265_);
lean_dec_ref(v_goalPrefix_2263_);
lean_dec(v_userName_x3f_2262_);
v___x_2326_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2);
if (v_isShared_2284_ == 0)
{
lean_ctor_set_tag(v___x_2283_, 1);
lean_ctor_set(v___x_2283_, 0, v_mvarId_2264_);
v___x_2328_ = v___x_2283_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_mvarId_2264_);
v___x_2328_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
lean_object* v___x_2330_; 
if (v_isShared_2261_ == 0)
{
lean_ctor_set_tag(v___x_2260_, 7);
lean_ctor_set(v___x_2260_, 1, v___x_2328_);
lean_ctor_set(v___x_2260_, 0, v___x_2326_);
v___x_2330_ = v___x_2260_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2326_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v___x_2328_);
v___x_2330_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
lean_object* v___x_2331_; 
v___x_2331_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_2330_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_);
return v___x_2331_;
}
}
}
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec(v_a_2276_);
lean_del_object(v___x_2273_);
lean_dec_ref(v_ctx_2271_);
lean_dec_ref(v_type_2270_);
lean_del_object(v___x_2267_);
lean_dec(v_isRemoved_x3f_2265_);
lean_dec(v_mvarId_2264_);
lean_dec_ref(v_goalPrefix_2263_);
lean_dec(v_userName_x3f_2262_);
lean_del_object(v___x_2260_);
v_a_2335_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2278_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2278_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_del_object(v___x_2273_);
lean_dec_ref(v_ctx_2271_);
lean_dec_ref(v_type_2270_);
lean_del_object(v___x_2267_);
lean_dec(v_isRemoved_x3f_2265_);
lean_dec(v_mvarId_2264_);
lean_dec_ref(v_goalPrefix_2263_);
lean_dec(v_userName_x3f_2262_);
lean_del_object(v___x_2260_);
lean_dec(v_g_u2080_2241_);
v_a_2343_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2275_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2275_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
lean_dec(v___x_2250_);
lean_dec_ref(v_i_u2081_2242_);
v___x_2357_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4);
v___x_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2358_, 0, v_g_u2080_2241_);
v___x_2359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2357_);
lean_ctor_set(v___x_2359_, 1, v___x_2358_);
v___x_2360_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6);
v___x_2361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2359_);
lean_ctor_set(v___x_2361_, 1, v___x_2360_);
v___x_2362_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_2361_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_);
return v___x_2362_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___boxed(lean_object* v_useAfter_2363_, lean_object* v_g_u2080_2364_, lean_object* v_i_u2081_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_){
_start:
{
uint8_t v_useAfter_boxed_2371_; lean_object* v_res_2372_; 
v_useAfter_boxed_2371_ = lean_unbox(v_useAfter_2363_);
v_res_2372_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(v_useAfter_boxed_2371_, v_g_u2080_2364_, v_i_u2081_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
lean_dec(v_a_2369_);
lean_dec_ref(v_a_2368_);
lean_dec(v_a_2367_);
lean_dec_ref(v_a_2366_);
return v_res_2372_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(lean_object* v_opts_2373_, lean_object* v_opt_2374_){
_start:
{
lean_object* v_name_2375_; lean_object* v_defValue_2376_; lean_object* v_map_2377_; lean_object* v___x_2378_; 
v_name_2375_ = lean_ctor_get(v_opt_2374_, 0);
v_defValue_2376_ = lean_ctor_get(v_opt_2374_, 1);
v_map_2377_ = lean_ctor_get(v_opts_2373_, 0);
v___x_2378_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2377_, v_name_2375_);
if (lean_obj_tag(v___x_2378_) == 0)
{
uint8_t v___x_2379_; 
v___x_2379_ = lean_unbox(v_defValue_2376_);
return v___x_2379_;
}
else
{
lean_object* v_val_2380_; 
v_val_2380_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_val_2380_);
lean_dec_ref_known(v___x_2378_, 1);
if (lean_obj_tag(v_val_2380_) == 1)
{
uint8_t v_v_2381_; 
v_v_2381_ = lean_ctor_get_uint8(v_val_2380_, 0);
lean_dec_ref_known(v_val_2380_, 0);
return v_v_2381_;
}
else
{
uint8_t v___x_2382_; 
lean_dec(v_val_2380_);
v___x_2382_ = lean_unbox(v_defValue_2376_);
return v___x_2382_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0___boxed(lean_object* v_opts_2383_, lean_object* v_opt_2384_){
_start:
{
uint8_t v_res_2385_; lean_object* v_r_2386_; 
v_res_2385_ = l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(v_opts_2383_, v_opt_2384_);
lean_dec_ref(v_opt_2384_);
lean_dec_ref(v_opts_2383_);
v_r_2386_ = lean_box(v_res_2385_);
return v_r_2386_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(lean_object* v_x_2387_, lean_object* v_x_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
if (lean_obj_tag(v_x_2388_) == 0)
{
lean_object* v___x_2394_; 
v___x_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2394_, 0, v_x_2387_);
return v___x_2394_;
}
else
{
lean_object* v_head_2395_; lean_object* v_tail_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v_head_2395_ = lean_ctor_get(v_x_2388_, 0);
lean_inc_n(v_head_2395_, 2);
v_tail_2396_ = lean_ctor_get(v_x_2388_, 1);
lean_inc(v_tail_2396_);
lean_dec_ref_known(v_x_2388_, 2);
v___x_2397_ = l_Lean_Expr_mvar___override(v_head_2395_);
v___x_2398_ = l_Lean_Meta_getMVars(v___x_2397_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_a_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_a_2399_);
lean_dec_ref_known(v___x_2398_, 1);
v___x_2400_ = l_Lean_MVarIdSet_ofArray(v_a_2399_);
lean_dec(v_a_2399_);
v___x_2401_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_head_2395_, v___x_2400_, v_x_2387_);
v_x_2387_ = v___x_2401_;
v_x_2388_ = v_tail_2396_;
goto _start;
}
else
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2410_; 
lean_dec(v_tail_2396_);
lean_dec(v_head_2395_);
lean_dec(v_x_2387_);
v_a_2403_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2405_ = v___x_2398_;
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2398_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2408_; 
if (v_isShared_2406_ == 0)
{
v___x_2408_ = v___x_2405_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_a_2403_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1___boxed(lean_object* v_x_2411_, lean_object* v_x_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(v_x_2411_, v_x_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(lean_object* v_lctx_2419_, lean_object* v_localInsts_2420_, lean_object* v_x_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v___x_2427_; 
v___x_2427_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2419_, v_localInsts_2420_, v_x_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
v_a_2428_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2427_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2427_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
v_a_2436_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2427_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2427_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg___boxed(lean_object* v_lctx_2444_, lean_object* v_localInsts_2445_, lean_object* v_x_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(v_lctx_2444_, v_localInsts_2445_, v_x_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
return v_res_2452_;
}
}
static lean_object* _init_l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = ((lean_object*)(l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__0));
v___x_2455_ = l_Lean_stringToMessageData(v___x_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(lean_object* v_goal_2456_, lean_object* v_action_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v___x_2463_; lean_object* v_mctx_2464_; lean_object* v___x_2465_; 
v___x_2463_ = lean_st_ref_get(v___y_2459_);
v_mctx_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc_ref(v_mctx_2464_);
lean_dec(v___x_2463_);
v___x_2465_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2464_, v_goal_2456_);
lean_dec_ref(v_mctx_2464_);
if (lean_obj_tag(v___x_2465_) == 1)
{
lean_object* v_val_2466_; lean_object* v_options_2467_; lean_object* v_lctx_2468_; lean_object* v_localInstances_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v_fst_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
lean_dec(v_goal_2456_);
v_val_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc(v_val_2466_);
lean_dec_ref_known(v___x_2465_, 1);
v_options_2467_ = lean_ctor_get(v___y_2460_, 2);
v_lctx_2468_ = lean_ctor_get(v_val_2466_, 1);
v_localInstances_2469_ = lean_ctor_get(v_val_2466_, 4);
lean_inc_ref(v_localInstances_2469_);
v___x_2470_ = lean_box(1);
lean_inc_ref(v_options_2467_);
v___x_2471_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2471_, 0, v_options_2467_);
lean_ctor_set(v___x_2471_, 1, v___x_2470_);
lean_ctor_set(v___x_2471_, 2, v___x_2470_);
lean_inc_ref(v_lctx_2468_);
v___x_2472_ = l_Lean_LocalContext_sanitizeNames(v_lctx_2468_, v___x_2471_);
v_fst_2473_ = lean_ctor_get(v___x_2472_, 0);
lean_inc_n(v_fst_2473_, 2);
lean_dec_ref(v___x_2472_);
v___x_2474_ = lean_apply_2(v_action_2457_, v_fst_2473_, v_val_2466_);
v___x_2475_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(v_fst_2473_, v_localInstances_2469_, v___x_2474_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
return v___x_2475_;
}
else
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
lean_dec(v___x_2465_);
lean_dec_ref(v_action_2457_);
v___x_2476_ = lean_obj_once(&l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1, &l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1_once, _init_l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1);
v___x_2477_ = l_Lean_MessageData_ofName(v_goal_2456_);
v___x_2478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2476_);
lean_ctor_set(v___x_2478_, 1, v___x_2477_);
v___x_2479_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_2478_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
return v___x_2479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___boxed(lean_object* v_goal_2480_, lean_object* v_action_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(v_goal_2480_, v_action_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
return v_res_2487_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4(lean_object* v___x_2488_, lean_object* v_x_2489_){
_start:
{
if (lean_obj_tag(v_x_2489_) == 0)
{
uint8_t v___x_2490_; 
v___x_2490_ = 0;
return v___x_2490_;
}
else
{
lean_object* v_head_2491_; lean_object* v_tail_2492_; uint8_t v___x_2493_; 
v_head_2491_ = lean_ctor_get(v_x_2489_, 0);
v_tail_2492_ = lean_ctor_get(v_x_2489_, 1);
v___x_2493_ = l_Lean_instBEqMVarId_beq(v_head_2491_, v___x_2488_);
if (v___x_2493_ == 0)
{
v_x_2489_ = v_tail_2492_;
goto _start;
}
else
{
return v___x_2493_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4___boxed(lean_object* v___x_2495_, lean_object* v_x_2496_){
_start:
{
uint8_t v_res_2497_; lean_object* v_r_2498_; 
v_res_2497_ = l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4(v___x_2495_, v_x_2496_);
lean_dec(v_x_2496_);
lean_dec(v___x_2495_);
v_r_2498_ = lean_box(v_res_2497_);
return v_r_2498_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(lean_object* v_t_2499_, lean_object* v_k_2500_){
_start:
{
if (lean_obj_tag(v_t_2499_) == 0)
{
lean_object* v_k_2501_; lean_object* v_v_2502_; lean_object* v_l_2503_; lean_object* v_r_2504_; uint8_t v___x_2505_; 
v_k_2501_ = lean_ctor_get(v_t_2499_, 1);
v_v_2502_ = lean_ctor_get(v_t_2499_, 2);
v_l_2503_ = lean_ctor_get(v_t_2499_, 3);
v_r_2504_ = lean_ctor_get(v_t_2499_, 4);
v___x_2505_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2500_, v_k_2501_);
switch(v___x_2505_)
{
case 0:
{
v_t_2499_ = v_l_2503_;
goto _start;
}
case 1:
{
lean_object* v___x_2507_; 
lean_inc(v_v_2502_);
v___x_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2507_, 0, v_v_2502_);
return v___x_2507_;
}
default: 
{
v_t_2499_ = v_r_2504_;
goto _start;
}
}
}
else
{
lean_object* v___x_2509_; 
v___x_2509_ = lean_box(0);
return v___x_2509_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg___boxed(lean_object* v_t_2510_, lean_object* v_k_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(v_t_2510_, v_k_2511_);
lean_dec(v_k_2511_);
lean_dec(v_t_2510_);
return v_res_2512_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(lean_object* v_k_2513_, lean_object* v_t_2514_){
_start:
{
if (lean_obj_tag(v_t_2514_) == 0)
{
lean_object* v_k_2515_; lean_object* v_l_2516_; lean_object* v_r_2517_; uint8_t v___x_2518_; 
v_k_2515_ = lean_ctor_get(v_t_2514_, 1);
v_l_2516_ = lean_ctor_get(v_t_2514_, 3);
v_r_2517_ = lean_ctor_get(v_t_2514_, 4);
v___x_2518_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2513_, v_k_2515_);
switch(v___x_2518_)
{
case 0:
{
v_t_2514_ = v_l_2516_;
goto _start;
}
case 1:
{
uint8_t v___x_2520_; 
v___x_2520_ = 1;
return v___x_2520_;
}
default: 
{
v_t_2514_ = v_r_2517_;
goto _start;
}
}
}
else
{
uint8_t v___x_2522_; 
v___x_2522_ = 0;
return v___x_2522_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg___boxed(lean_object* v_k_2523_, lean_object* v_t_2524_){
_start:
{
uint8_t v_res_2525_; lean_object* v_r_2526_; 
v_res_2525_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_k_2523_, v_t_2524_);
lean_dec(v_t_2524_);
lean_dec(v_k_2523_);
v_r_2526_ = lean_box(v_res_2525_);
return v_r_2526_;
}
}
LEAN_EXPORT uint8_t l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(lean_object* v_a_2527_, uint8_t v___x_2528_, lean_object* v_before_2529_, lean_object* v_after_2530_){
_start:
{
lean_object* v___x_2531_; 
v___x_2531_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(v_a_2527_, v_before_2529_);
if (lean_obj_tag(v___x_2531_) == 0)
{
return v___x_2528_;
}
else
{
lean_object* v_val_2532_; uint8_t v___x_2533_; 
v_val_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_val_2532_);
lean_dec_ref_known(v___x_2531_, 1);
v___x_2533_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_after_2530_, v_val_2532_);
lean_dec(v_val_2532_);
return v___x_2533_;
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0___boxed(lean_object* v_a_2534_, lean_object* v___x_2535_, lean_object* v_before_2536_, lean_object* v_after_2537_){
_start:
{
uint8_t v___x_3864__boxed_2538_; uint8_t v_res_2539_; lean_object* v_r_2540_; 
v___x_3864__boxed_2538_ = lean_unbox(v___x_2535_);
v_res_2539_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(v_a_2534_, v___x_3864__boxed_2538_, v_before_2536_, v_after_2537_);
lean_dec(v_after_2537_);
lean_dec(v_before_2536_);
lean_dec(v_a_2534_);
v_r_2540_ = lean_box(v_res_2539_);
return v_r_2540_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5(uint8_t v___y_2541_, lean_object* v_a_2542_, lean_object* v___x_2543_, lean_object* v_x_2544_){
_start:
{
if (lean_obj_tag(v_x_2544_) == 0)
{
lean_object* v___x_2545_; 
v___x_2545_ = lean_box(0);
return v___x_2545_;
}
else
{
lean_object* v_head_2546_; lean_object* v_tail_2547_; uint8_t v___y_2549_; uint8_t v___x_2552_; 
v_head_2546_ = lean_ctor_get(v_x_2544_, 0);
v_tail_2547_ = lean_ctor_get(v_x_2544_, 1);
v___x_2552_ = 0;
if (v___y_2541_ == 0)
{
uint8_t v___x_2553_; 
v___x_2553_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(v_a_2542_, v___x_2552_, v___x_2543_, v_head_2546_);
v___y_2549_ = v___x_2553_;
goto v___jp_2548_;
}
else
{
uint8_t v___x_2554_; 
v___x_2554_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(v_a_2542_, v___x_2552_, v_head_2546_, v___x_2543_);
v___y_2549_ = v___x_2554_;
goto v___jp_2548_;
}
v___jp_2548_:
{
if (v___y_2549_ == 0)
{
v_x_2544_ = v_tail_2547_;
goto _start;
}
else
{
lean_object* v___x_2551_; 
lean_inc(v_head_2546_);
v___x_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2551_, 0, v_head_2546_);
return v___x_2551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___boxed(lean_object* v___y_2555_, lean_object* v_a_2556_, lean_object* v___x_2557_, lean_object* v_x_2558_){
_start:
{
uint8_t v___y_3875__boxed_2559_; lean_object* v_res_2560_; 
v___y_3875__boxed_2559_ = lean_unbox(v___y_2555_);
v_res_2560_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5(v___y_3875__boxed_2559_, v_a_2556_, v___x_2557_, v_x_2558_);
lean_dec(v_x_2558_);
lean_dec(v___x_2557_);
lean_dec(v_a_2556_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0(lean_object* v_mvarId_2561_, lean_object* v___y_2562_, uint8_t v___y_2563_, lean_object* v_a_2564_, uint8_t v_useAfter_2565_, lean_object* v_v_2566_, uint8_t v___x_2567_, lean_object* v_toInteractiveGoalCore_2568_, lean_object* v_userName_x3f_2569_, lean_object* v_goalPrefix_2570_, lean_object* v_isInserted_x3f_2571_, lean_object* v_isRemoved_x3f_2572_, lean_object* v___lctx_u2081_2573_, lean_object* v___md_u2081_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
uint8_t v___x_2580_; 
v___x_2580_ = l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4(v_mvarId_2561_, v___y_2562_);
if (v___x_2580_ == 0)
{
lean_object* v___x_2581_; 
v___x_2581_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5(v___y_2563_, v_a_2564_, v_mvarId_2561_, v___y_2562_);
if (lean_obj_tag(v___x_2581_) == 1)
{
lean_object* v_val_2582_; lean_object* v___x_2583_; 
lean_dec(v_isRemoved_x3f_2572_);
lean_dec(v_isInserted_x3f_2571_);
lean_dec_ref(v_goalPrefix_2570_);
lean_dec(v_userName_x3f_2569_);
lean_dec_ref(v_toInteractiveGoalCore_2568_);
lean_dec(v_mvarId_2561_);
v_val_2582_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_val_2582_);
lean_dec_ref_known(v___x_2581_, 1);
v___x_2583_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(v_useAfter_2565_, v_val_2582_, v_v_2566_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
return v___x_2583_;
}
else
{
lean_dec(v___x_2581_);
lean_dec(v_v_2566_);
if (v___y_2563_ == 0)
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
lean_dec(v_isRemoved_x3f_2572_);
v___x_2584_ = lean_box(v___x_2567_);
v___x_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2584_);
v___x_2586_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2586_, 0, v_toInteractiveGoalCore_2568_);
lean_ctor_set(v___x_2586_, 1, v_userName_x3f_2569_);
lean_ctor_set(v___x_2586_, 2, v_goalPrefix_2570_);
lean_ctor_set(v___x_2586_, 3, v_mvarId_2561_);
lean_ctor_set(v___x_2586_, 4, v_isInserted_x3f_2571_);
lean_ctor_set(v___x_2586_, 5, v___x_2585_);
v___x_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2586_);
return v___x_2587_;
}
else
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
lean_dec(v_isInserted_x3f_2571_);
v___x_2588_ = lean_box(v___x_2567_);
v___x_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2588_);
v___x_2590_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2590_, 0, v_toInteractiveGoalCore_2568_);
lean_ctor_set(v___x_2590_, 1, v_userName_x3f_2569_);
lean_ctor_set(v___x_2590_, 2, v_goalPrefix_2570_);
lean_ctor_set(v___x_2590_, 3, v_mvarId_2561_);
lean_ctor_set(v___x_2590_, 4, v___x_2589_);
lean_ctor_set(v___x_2590_, 5, v_isRemoved_x3f_2572_);
v___x_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2590_);
return v___x_2591_;
}
}
}
else
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
lean_dec(v_isInserted_x3f_2571_);
lean_dec(v_v_2566_);
v___x_2592_ = lean_box(0);
v___x_2593_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2593_, 0, v_toInteractiveGoalCore_2568_);
lean_ctor_set(v___x_2593_, 1, v_userName_x3f_2569_);
lean_ctor_set(v___x_2593_, 2, v_goalPrefix_2570_);
lean_ctor_set(v___x_2593_, 3, v_mvarId_2561_);
lean_ctor_set(v___x_2593_, 4, v___x_2592_);
lean_ctor_set(v___x_2593_, 5, v_isRemoved_x3f_2572_);
v___x_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
return v___x_2594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0___boxed(lean_object** _args){
lean_object* v_mvarId_2595_ = _args[0];
lean_object* v___y_2596_ = _args[1];
lean_object* v___y_2597_ = _args[2];
lean_object* v_a_2598_ = _args[3];
lean_object* v_useAfter_2599_ = _args[4];
lean_object* v_v_2600_ = _args[5];
lean_object* v___x_2601_ = _args[6];
lean_object* v_toInteractiveGoalCore_2602_ = _args[7];
lean_object* v_userName_x3f_2603_ = _args[8];
lean_object* v_goalPrefix_2604_ = _args[9];
lean_object* v_isInserted_x3f_2605_ = _args[10];
lean_object* v_isRemoved_x3f_2606_ = _args[11];
lean_object* v___lctx_u2081_2607_ = _args[12];
lean_object* v___md_u2081_2608_ = _args[13];
lean_object* v___y_2609_ = _args[14];
lean_object* v___y_2610_ = _args[15];
lean_object* v___y_2611_ = _args[16];
lean_object* v___y_2612_ = _args[17];
lean_object* v___y_2613_ = _args[18];
_start:
{
uint8_t v___y_3908__boxed_2614_; uint8_t v_useAfter_boxed_2615_; uint8_t v___x_3910__boxed_2616_; lean_object* v_res_2617_; 
v___y_3908__boxed_2614_ = lean_unbox(v___y_2597_);
v_useAfter_boxed_2615_ = lean_unbox(v_useAfter_2599_);
v___x_3910__boxed_2616_ = lean_unbox(v___x_2601_);
v_res_2617_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0(v_mvarId_2595_, v___y_2596_, v___y_3908__boxed_2614_, v_a_2598_, v_useAfter_boxed_2615_, v_v_2600_, v___x_3910__boxed_2616_, v_toInteractiveGoalCore_2602_, v_userName_x3f_2603_, v_goalPrefix_2604_, v_isInserted_x3f_2605_, v_isRemoved_x3f_2606_, v___lctx_u2081_2607_, v___md_u2081_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec_ref(v___md_u2081_2608_);
lean_dec_ref(v___lctx_u2081_2607_);
lean_dec(v_a_2598_);
lean_dec(v___y_2596_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8(lean_object* v___y_2618_, uint8_t v___y_2619_, lean_object* v_a_2620_, uint8_t v_useAfter_2621_, uint8_t v___x_2622_, size_t v_sz_2623_, size_t v_i_2624_, lean_object* v_bs_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
uint8_t v___x_2631_; 
v___x_2631_ = lean_usize_dec_lt(v_i_2624_, v_sz_2623_);
if (v___x_2631_ == 0)
{
lean_object* v___x_2632_; 
lean_dec(v_a_2620_);
lean_dec(v___y_2618_);
v___x_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2632_, 0, v_bs_2625_);
return v___x_2632_;
}
else
{
lean_object* v_v_2633_; lean_object* v_toInteractiveGoalCore_2634_; lean_object* v_userName_x3f_2635_; lean_object* v_goalPrefix_2636_; lean_object* v_mvarId_2637_; lean_object* v_isInserted_x3f_2638_; lean_object* v_isRemoved_x3f_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___f_2643_; lean_object* v___x_2644_; 
v_v_2633_ = lean_array_uget_borrowed(v_bs_2625_, v_i_2624_);
v_toInteractiveGoalCore_2634_ = lean_ctor_get(v_v_2633_, 0);
v_userName_x3f_2635_ = lean_ctor_get(v_v_2633_, 1);
v_goalPrefix_2636_ = lean_ctor_get(v_v_2633_, 2);
v_mvarId_2637_ = lean_ctor_get(v_v_2633_, 3);
v_isInserted_x3f_2638_ = lean_ctor_get(v_v_2633_, 4);
v_isRemoved_x3f_2639_ = lean_ctor_get(v_v_2633_, 5);
v___x_2640_ = lean_box(v___y_2619_);
v___x_2641_ = lean_box(v_useAfter_2621_);
v___x_2642_ = lean_box(v___x_2622_);
lean_inc(v_isRemoved_x3f_2639_);
lean_inc(v_isInserted_x3f_2638_);
lean_inc_ref(v_goalPrefix_2636_);
lean_inc(v_userName_x3f_2635_);
lean_inc_ref(v_toInteractiveGoalCore_2634_);
lean_inc(v_v_2633_);
lean_inc(v_a_2620_);
lean_inc(v___y_2618_);
lean_inc_n(v_mvarId_2637_, 2);
v___f_2643_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0___boxed), 19, 12);
lean_closure_set(v___f_2643_, 0, v_mvarId_2637_);
lean_closure_set(v___f_2643_, 1, v___y_2618_);
lean_closure_set(v___f_2643_, 2, v___x_2640_);
lean_closure_set(v___f_2643_, 3, v_a_2620_);
lean_closure_set(v___f_2643_, 4, v___x_2641_);
lean_closure_set(v___f_2643_, 5, v_v_2633_);
lean_closure_set(v___f_2643_, 6, v___x_2642_);
lean_closure_set(v___f_2643_, 7, v_toInteractiveGoalCore_2634_);
lean_closure_set(v___f_2643_, 8, v_userName_x3f_2635_);
lean_closure_set(v___f_2643_, 9, v_goalPrefix_2636_);
lean_closure_set(v___f_2643_, 10, v_isInserted_x3f_2638_);
lean_closure_set(v___f_2643_, 11, v_isRemoved_x3f_2639_);
v___x_2644_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(v_mvarId_2637_, v___f_2643_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v_a_2645_; lean_object* v___x_2646_; lean_object* v_bs_x27_2647_; size_t v___x_2648_; size_t v___x_2649_; lean_object* v___x_2650_; 
v_a_2645_ = lean_ctor_get(v___x_2644_, 0);
lean_inc(v_a_2645_);
lean_dec_ref_known(v___x_2644_, 1);
v___x_2646_ = lean_unsigned_to_nat(0u);
v_bs_x27_2647_ = lean_array_uset(v_bs_2625_, v_i_2624_, v___x_2646_);
v___x_2648_ = ((size_t)1ULL);
v___x_2649_ = lean_usize_add(v_i_2624_, v___x_2648_);
v___x_2650_ = lean_array_uset(v_bs_x27_2647_, v_i_2624_, v_a_2645_);
v_i_2624_ = v___x_2649_;
v_bs_2625_ = v___x_2650_;
goto _start;
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
lean_dec_ref(v_bs_2625_);
lean_dec(v_a_2620_);
lean_dec(v___y_2618_);
v_a_2652_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2644_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2644_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8___boxed(lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v_a_2662_, lean_object* v_useAfter_2663_, lean_object* v___x_2664_, lean_object* v_sz_2665_, lean_object* v_i_2666_, lean_object* v_bs_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
uint8_t v___y_3965__boxed_2673_; uint8_t v_useAfter_boxed_2674_; uint8_t v___x_3967__boxed_2675_; size_t v_sz_boxed_2676_; size_t v_i_boxed_2677_; lean_object* v_res_2678_; 
v___y_3965__boxed_2673_ = lean_unbox(v___y_2661_);
v_useAfter_boxed_2674_ = lean_unbox(v_useAfter_2663_);
v___x_3967__boxed_2675_ = lean_unbox(v___x_2664_);
v_sz_boxed_2676_ = lean_unbox_usize(v_sz_2665_);
lean_dec(v_sz_2665_);
v_i_boxed_2677_ = lean_unbox_usize(v_i_2666_);
lean_dec(v_i_2666_);
v_res_2678_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8(v___y_2660_, v___y_3965__boxed_2673_, v_a_2662_, v_useAfter_boxed_2674_, v___x_3967__boxed_2675_, v_sz_boxed_2676_, v_i_boxed_2677_, v_bs_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7(uint8_t v___y_2679_, lean_object* v_a_2680_, lean_object* v___y_2681_, uint8_t v_useAfter_2682_, uint8_t v___x_2683_, size_t v_sz_2684_, size_t v_i_2685_, lean_object* v_bs_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
uint8_t v___x_2692_; 
v___x_2692_ = lean_usize_dec_lt(v_i_2685_, v_sz_2684_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2693_; 
lean_dec(v___y_2681_);
lean_dec(v_a_2680_);
v___x_2693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2693_, 0, v_bs_2686_);
return v___x_2693_;
}
else
{
lean_object* v_v_2694_; lean_object* v_toInteractiveGoalCore_2695_; lean_object* v_userName_x3f_2696_; lean_object* v_goalPrefix_2697_; lean_object* v_mvarId_2698_; lean_object* v_isInserted_x3f_2699_; lean_object* v_isRemoved_x3f_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___f_2704_; lean_object* v___x_2705_; 
v_v_2694_ = lean_array_uget_borrowed(v_bs_2686_, v_i_2685_);
v_toInteractiveGoalCore_2695_ = lean_ctor_get(v_v_2694_, 0);
v_userName_x3f_2696_ = lean_ctor_get(v_v_2694_, 1);
v_goalPrefix_2697_ = lean_ctor_get(v_v_2694_, 2);
v_mvarId_2698_ = lean_ctor_get(v_v_2694_, 3);
v_isInserted_x3f_2699_ = lean_ctor_get(v_v_2694_, 4);
v_isRemoved_x3f_2700_ = lean_ctor_get(v_v_2694_, 5);
v___x_2701_ = lean_box(v___y_2679_);
v___x_2702_ = lean_box(v_useAfter_2682_);
v___x_2703_ = lean_box(v___x_2683_);
lean_inc(v_isRemoved_x3f_2700_);
lean_inc(v_isInserted_x3f_2699_);
lean_inc_ref(v_goalPrefix_2697_);
lean_inc(v_userName_x3f_2696_);
lean_inc_ref(v_toInteractiveGoalCore_2695_);
lean_inc(v_v_2694_);
lean_inc(v_a_2680_);
lean_inc(v___y_2681_);
lean_inc_n(v_mvarId_2698_, 2);
v___f_2704_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0___boxed), 19, 12);
lean_closure_set(v___f_2704_, 0, v_mvarId_2698_);
lean_closure_set(v___f_2704_, 1, v___y_2681_);
lean_closure_set(v___f_2704_, 2, v___x_2701_);
lean_closure_set(v___f_2704_, 3, v_a_2680_);
lean_closure_set(v___f_2704_, 4, v___x_2702_);
lean_closure_set(v___f_2704_, 5, v_v_2694_);
lean_closure_set(v___f_2704_, 6, v___x_2703_);
lean_closure_set(v___f_2704_, 7, v_toInteractiveGoalCore_2695_);
lean_closure_set(v___f_2704_, 8, v_userName_x3f_2696_);
lean_closure_set(v___f_2704_, 9, v_goalPrefix_2697_);
lean_closure_set(v___f_2704_, 10, v_isInserted_x3f_2699_);
lean_closure_set(v___f_2704_, 11, v_isRemoved_x3f_2700_);
v___x_2705_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(v_mvarId_2698_, v___f_2704_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_a_2706_; lean_object* v___x_2707_; lean_object* v_bs_x27_2708_; size_t v___x_2709_; size_t v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2705_, 1);
v___x_2707_ = lean_unsigned_to_nat(0u);
v_bs_x27_2708_ = lean_array_uset(v_bs_2686_, v_i_2685_, v___x_2707_);
v___x_2709_ = ((size_t)1ULL);
v___x_2710_ = lean_usize_add(v_i_2685_, v___x_2709_);
v___x_2711_ = lean_array_uset(v_bs_x27_2708_, v_i_2685_, v_a_2706_);
v___x_2712_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8(v___y_2681_, v___y_2679_, v_a_2680_, v_useAfter_2682_, v___x_2683_, v_sz_2684_, v___x_2710_, v___x_2711_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
return v___x_2712_;
}
else
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
lean_dec_ref(v_bs_2686_);
lean_dec(v___y_2681_);
lean_dec(v_a_2680_);
v_a_2713_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v___x_2705_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2705_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___boxed(lean_object* v___y_2721_, lean_object* v_a_2722_, lean_object* v___y_2723_, lean_object* v_useAfter_2724_, lean_object* v___x_2725_, lean_object* v_sz_2726_, lean_object* v_i_2727_, lean_object* v_bs_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
uint8_t v___y_4033__boxed_2734_; uint8_t v_useAfter_boxed_2735_; uint8_t v___x_4036__boxed_2736_; size_t v_sz_boxed_2737_; size_t v_i_boxed_2738_; lean_object* v_res_2739_; 
v___y_4033__boxed_2734_ = lean_unbox(v___y_2721_);
v_useAfter_boxed_2735_ = lean_unbox(v_useAfter_2724_);
v___x_4036__boxed_2736_ = lean_unbox(v___x_2725_);
v_sz_boxed_2737_ = lean_unbox_usize(v_sz_2726_);
lean_dec(v_sz_2726_);
v_i_boxed_2738_ = lean_unbox_usize(v_i_2727_);
lean_dec(v_i_2727_);
v_res_2739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7(v___y_4033__boxed_2734_, v_a_2722_, v___y_2723_, v_useAfter_boxed_2735_, v___x_4036__boxed_2736_, v_sz_boxed_2737_, v_i_boxed_2738_, v_bs_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_diffInteractiveGoals(uint8_t v_useAfter_2740_, lean_object* v_info_2741_, lean_object* v_igs_u2081_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_){
_start:
{
lean_object* v_options_2748_; lean_object* v___x_2749_; uint8_t v___x_2750_; lean_object* v___y_2752_; 
v_options_2748_ = lean_ctor_get(v_a_2745_, 2);
v___x_2749_ = l___private_Lean_Widget_Diff_0__Lean_Widget_showTacticDiff;
v___x_2750_ = l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(v_options_2748_, v___x_2749_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2784_; 
lean_dec_ref(v_info_2741_);
v___x_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2784_, 0, v_igs_u2081_2742_);
return v___x_2784_;
}
else
{
if (v_useAfter_2740_ == 0)
{
lean_object* v_goalsAfter_2785_; 
v_goalsAfter_2785_ = lean_ctor_get(v_info_2741_, 4);
lean_inc(v_goalsAfter_2785_);
v___y_2752_ = v_goalsAfter_2785_;
goto v___jp_2751_;
}
else
{
lean_object* v_goalsBefore_2786_; 
v_goalsBefore_2786_ = lean_ctor_get(v_info_2741_, 2);
lean_inc(v_goalsBefore_2786_);
v___y_2752_ = v_goalsBefore_2786_;
goto v___jp_2751_;
}
}
v___jp_2751_:
{
lean_object* v_goalsBefore_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v_goalsBefore_2753_ = lean_ctor_get(v_info_2741_, 2);
lean_inc(v_goalsBefore_2753_);
lean_dec_ref(v_info_2741_);
v___x_2754_ = lean_box(1);
v___x_2755_ = l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(v___x_2754_, v_goalsBefore_2753_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; size_t v_sz_2757_; size_t v___x_2758_; lean_object* v___x_2759_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc(v_a_2756_);
lean_dec_ref_known(v___x_2755_, 1);
v_sz_2757_ = lean_array_size(v_igs_u2081_2742_);
v___x_2758_ = ((size_t)0ULL);
v___x_2759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7(v_useAfter_2740_, v_a_2756_, v___y_2752_, v_useAfter_2740_, v___x_2750_, v_sz_2757_, v___x_2758_, v_igs_u2081_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2759_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2759_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
v_a_2768_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2759_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2759_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
else
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2783_; 
lean_dec(v___y_2752_);
lean_dec_ref(v_igs_u2081_2742_);
v_a_2776_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2778_ = v___x_2755_;
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2755_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
if (v_isShared_2779_ == 0)
{
v___x_2781_ = v___x_2778_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2776_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_diffInteractiveGoals___boxed(lean_object* v_useAfter_2787_, lean_object* v_info_2788_, lean_object* v_igs_u2081_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_){
_start:
{
uint8_t v_useAfter_boxed_2795_; lean_object* v_res_2796_; 
v_useAfter_boxed_2795_ = lean_unbox(v_useAfter_2787_);
v_res_2796_ = l_Lean_Widget_diffInteractiveGoals(v_useAfter_boxed_2795_, v_info_2788_, v_igs_u2081_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
lean_dec(v_a_2793_);
lean_dec_ref(v_a_2792_);
lean_dec(v_a_2791_);
lean_dec_ref(v_a_2790_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2(lean_object* v_00_u03b4_2797_, lean_object* v_t_2798_, lean_object* v_k_2799_){
_start:
{
lean_object* v___x_2800_; 
v___x_2800_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(v_t_2798_, v_k_2799_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___boxed(lean_object* v_00_u03b4_2801_, lean_object* v_t_2802_, lean_object* v_k_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2(v_00_u03b4_2801_, v_t_2802_, v_k_2803_);
lean_dec(v_k_2803_);
lean_dec(v_t_2802_);
return v_res_2804_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3(lean_object* v_00_u03b2_2805_, lean_object* v_k_2806_, lean_object* v_t_2807_){
_start:
{
uint8_t v___x_2808_; 
v___x_2808_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_k_2806_, v_t_2807_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___boxed(lean_object* v_00_u03b2_2809_, lean_object* v_k_2810_, lean_object* v_t_2811_){
_start:
{
uint8_t v_res_2812_; lean_object* v_r_2813_; 
v_res_2812_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3(v_00_u03b2_2809_, v_k_2810_, v_t_2811_);
lean_dec(v_t_2811_);
lean_dec(v_k_2810_);
v_r_2813_ = lean_box(v_res_2812_);
return v_r_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6(lean_object* v_00_u03b1_2814_, lean_object* v_lctx_2815_, lean_object* v_localInsts_2816_, lean_object* v_x_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v___x_2823_; 
v___x_2823_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(v_lctx_2815_, v_localInsts_2816_, v_x_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___boxed(lean_object* v_00_u03b1_2824_, lean_object* v_lctx_2825_, lean_object* v_localInsts_2826_, lean_object* v_x_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6(v_00_u03b1_2824_, v_lctx_2825_, v_localInsts_2826_, v_x_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6(lean_object* v_00_u03b1_2834_, lean_object* v_goal_2835_, lean_object* v_action_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
lean_object* v___x_2842_; 
v___x_2842_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(v_goal_2835_, v_action_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___boxed(lean_object* v_00_u03b1_2843_, lean_object* v_goal_2844_, lean_object* v_action_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6(v_00_u03b1_2843_, v_goal_2844_, v_action_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
return v_res_2851_;
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
