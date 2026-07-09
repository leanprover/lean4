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
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toCtorIdx(uint8_t v_x_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx(v_x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toCtorIdx___boxed(lean_object* v_x_87_){
_start:
{
uint8_t v_x_4__boxed_88_; lean_object* v_res_89_; 
v_x_4__boxed_88_ = lean_unbox(v_x_87_);
v_res_89_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toCtorIdx(v_x_4__boxed_88_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___redArg(lean_object* v_k_90_){
_start:
{
lean_inc(v_k_90_);
return v_k_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___redArg___boxed(lean_object* v_k_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___redArg(v_k_91_);
lean_dec(v_k_91_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim(lean_object* v_motive_93_, lean_object* v_ctorIdx_94_, uint8_t v_t_95_, lean_object* v_h_96_, lean_object* v_k_97_){
_start:
{
lean_inc(v_k_97_);
return v_k_97_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___boxed(lean_object* v_motive_98_, lean_object* v_ctorIdx_99_, lean_object* v_t_100_, lean_object* v_h_101_, lean_object* v_k_102_){
_start:
{
uint8_t v_t_boxed_103_; lean_object* v_res_104_; 
v_t_boxed_103_ = lean_unbox(v_t_100_);
v_res_104_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim(v_motive_98_, v_ctorIdx_99_, v_t_boxed_103_, v_h_101_, v_k_102_);
lean_dec(v_k_102_);
lean_dec(v_ctorIdx_99_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___redArg(lean_object* v_change_105_){
_start:
{
lean_inc(v_change_105_);
return v_change_105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___redArg___boxed(lean_object* v_change_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___redArg(v_change_106_);
lean_dec(v_change_106_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim(lean_object* v_motive_108_, uint8_t v_t_109_, lean_object* v_h_110_, lean_object* v_change_111_){
_start:
{
lean_inc(v_change_111_);
return v_change_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___boxed(lean_object* v_motive_112_, lean_object* v_t_113_, lean_object* v_h_114_, lean_object* v_change_115_){
_start:
{
uint8_t v_t_boxed_116_; lean_object* v_res_117_; 
v_t_boxed_116_ = lean_unbox(v_t_113_);
v_res_117_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim(v_motive_112_, v_t_boxed_116_, v_h_114_, v_change_115_);
lean_dec(v_change_115_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___redArg(lean_object* v_delete_118_){
_start:
{
lean_inc(v_delete_118_);
return v_delete_118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___redArg___boxed(lean_object* v_delete_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___redArg(v_delete_119_);
lean_dec(v_delete_119_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim(lean_object* v_motive_121_, uint8_t v_t_122_, lean_object* v_h_123_, lean_object* v_delete_124_){
_start:
{
lean_inc(v_delete_124_);
return v_delete_124_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim(lean_object* v_motive_134_, uint8_t v_t_135_, lean_object* v_h_136_, lean_object* v_insert_137_){
_start:
{
lean_inc(v_insert_137_);
return v_insert_137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___boxed(lean_object* v_motive_138_, lean_object* v_t_139_, lean_object* v_h_140_, lean_object* v_insert_141_){
_start:
{
uint8_t v_t_boxed_142_; lean_object* v_res_143_; 
v_t_boxed_142_ = lean_unbox(v_t_139_);
v_res_143_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim(v_motive_138_, v_t_boxed_142_, v_h_140_, v_insert_141_);
lean_dec(v_insert_141_);
return v_res_143_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag(uint8_t v_x_144_, uint8_t v_x_145_){
_start:
{
if (v_x_144_ == 0)
{
switch(v_x_145_)
{
case 0:
{
uint8_t v___x_146_; 
v___x_146_ = 1;
return v___x_146_;
}
case 1:
{
uint8_t v___x_147_; 
v___x_147_ = 3;
return v___x_147_;
}
default: 
{
uint8_t v___x_148_; 
v___x_148_ = 5;
return v___x_148_;
}
}
}
else
{
switch(v_x_145_)
{
case 0:
{
uint8_t v___x_149_; 
v___x_149_ = 0;
return v___x_149_;
}
case 1:
{
uint8_t v___x_150_; 
v___x_150_ = 2;
return v___x_150_;
}
default: 
{
uint8_t v___x_151_; 
v___x_151_ = 4;
return v___x_151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag___boxed(lean_object* v_x_152_, lean_object* v_x_153_){
_start:
{
uint8_t v_x_49__boxed_154_; uint8_t v_x_50__boxed_155_; uint8_t v_res_156_; lean_object* v_r_157_; 
v_x_49__boxed_154_ = lean_unbox(v_x_152_);
v_x_50__boxed_155_ = lean_unbox(v_x_153_);
v_res_156_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag(v_x_49__boxed_154_, v_x_50__boxed_155_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString(uint8_t v_x_161_){
_start:
{
switch(v_x_161_)
{
case 0:
{
lean_object* v___x_162_; 
v___x_162_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__0));
return v___x_162_;
}
case 1:
{
lean_object* v___x_163_; 
v___x_163_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__1));
return v___x_163_;
}
default: 
{
lean_object* v___x_164_; 
v___x_164_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__2));
return v___x_164_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___boxed(lean_object* v_x_165_){
_start:
{
uint8_t v_x_31__boxed_166_; lean_object* v_res_167_; 
v_x_31__boxed_166_ = lean_unbox(v_x_165_);
v_res_167_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString(v_x_31__boxed_166_);
return v_res_167_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0(lean_object* v_x_173_, lean_object* v_y_174_){
_start:
{
uint8_t v___x_175_; 
v___x_175_ = lean_nat_dec_lt(v_x_173_, v_y_174_);
if (v___x_175_ == 0)
{
uint8_t v___x_176_; 
v___x_176_ = lean_nat_dec_eq(v_x_173_, v_y_174_);
if (v___x_176_ == 0)
{
uint8_t v___x_177_; 
v___x_177_ = 2;
return v___x_177_;
}
else
{
uint8_t v___x_178_; 
v___x_178_ = 1;
return v___x_178_;
}
}
else
{
uint8_t v___x_179_; 
v___x_179_ = 0;
return v___x_179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0___boxed(lean_object* v_x_180_, lean_object* v_y_181_){
_start:
{
uint8_t v_res_182_; lean_object* v_r_183_; 
v_res_182_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0(v_x_180_, v_y_181_);
lean_dec(v_y_181_);
lean_dec(v_x_180_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1(uint8_t v_b_u2082_184_, lean_object* v_x_185_){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = lean_box(v_b_u2082_184_);
v___x_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1___boxed(lean_object* v_b_u2082_188_, lean_object* v_x_189_){
_start:
{
uint8_t v_b_u2082_boxed_190_; lean_object* v_res_191_; 
v_b_u2082_boxed_190_ = lean_unbox(v_b_u2082_188_);
v_res_191_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1(v_b_u2082_boxed_190_, v_x_189_);
lean_dec(v_x_189_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2(lean_object* v___f_192_, lean_object* v_t_193_, lean_object* v_a_194_, uint8_t v_b_u2082_195_){
_start:
{
lean_object* v___x_196_; lean_object* v___f_197_; lean_object* v___x_198_; 
v___x_196_ = lean_box(v_b_u2082_195_);
v___f_197_ = lean_alloc_closure((void*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1___boxed), 2, 1);
lean_closure_set(v___f_197_, 0, v___x_196_);
v___x_198_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v___f_192_, v_a_194_, v___f_197_, v_t_193_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2___boxed(lean_object* v___f_199_, lean_object* v_t_200_, lean_object* v_a_201_, lean_object* v_b_u2082_202_){
_start:
{
uint8_t v_b_u2082_boxed_203_; lean_object* v_res_204_; 
v_b_u2082_boxed_203_ = lean_unbox(v_b_u2082_202_);
v_res_204_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2(v___f_199_, v_t_200_, v_a_201_, v_b_u2082_boxed_203_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__5(lean_object* v___f_205_, lean_object* v___f_206_, lean_object* v_a_207_, lean_object* v_b_208_){
_start:
{
lean_object* v_changesBefore_209_; lean_object* v_changesAfter_210_; lean_object* v_changesBefore_211_; lean_object* v_changesAfter_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_221_; 
v_changesBefore_209_ = lean_ctor_get(v_a_207_, 0);
lean_inc(v_changesBefore_209_);
v_changesAfter_210_ = lean_ctor_get(v_a_207_, 1);
lean_inc(v_changesAfter_210_);
lean_dec_ref(v_a_207_);
v_changesBefore_211_ = lean_ctor_get(v_b_208_, 0);
v_changesAfter_212_ = lean_ctor_get(v_b_208_, 1);
v_isSharedCheck_221_ = !lean_is_exclusive(v_b_208_);
if (v_isSharedCheck_221_ == 0)
{
v___x_214_ = v_b_208_;
v_isShared_215_ = v_isSharedCheck_221_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_changesAfter_212_);
lean_inc(v_changesBefore_211_);
lean_dec(v_b_208_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_221_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_219_; 
v___x_216_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_205_, v_changesBefore_209_, v_changesBefore_211_);
v___x_217_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_206_, v_changesAfter_210_, v_changesAfter_212_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 1, v___x_217_);
lean_ctor_set(v___x_214_, 0, v___x_216_);
v___x_219_ = v___x_214_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_216_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v___x_217_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0(lean_object* v_x_231_){
_start:
{
lean_object* v_fst_232_; lean_object* v_snd_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v_fst_232_ = lean_ctor_get(v_x_231_, 0);
v_snd_233_ = lean_ctor_get(v_x_231_, 1);
v___x_234_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__0));
v___x_235_ = l_Lean_SubExpr_Pos_toString(v_fst_232_);
v___x_236_ = lean_string_append(v___x_234_, v___x_235_);
lean_dec_ref(v___x_235_);
v___x_237_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__1));
v___x_238_ = lean_string_append(v___x_236_, v___x_237_);
v___x_239_ = lean_unbox(v_snd_233_);
v___x_240_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString(v___x_239_);
v___x_241_ = lean_string_append(v___x_238_, v___x_240_);
lean_dec_ref(v___x_240_);
v___x_242_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__2));
v___x_243_ = lean_string_append(v___x_241_, v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___boxed(lean_object* v_x_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0(v_x_244_);
lean_dec_ref(v_x_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1(lean_object* v_x1_246_, uint8_t v_x2_247_, lean_object* v_x3_248_){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_249_ = lean_box(v_x2_247_);
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v_x1_246_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
v___x_251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v_x3_248_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1___boxed(lean_object* v_x1_252_, lean_object* v_x2_253_, lean_object* v_x3_254_){
_start:
{
uint8_t v_x2_243__boxed_255_; lean_object* v_res_256_; 
v_x2_243__boxed_255_ = lean_unbox(v_x2_253_);
v_res_256_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1(v_x1_252_, v_x2_243__boxed_255_, v_x3_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2(lean_object* v___f_276_, lean_object* v___f_277_, lean_object* v_p_278_){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_279_ = lean_box(0);
v___x_280_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__9));
v___x_281_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_280_, v___f_276_, v___x_279_, v_p_278_);
v___x_282_ = l_List_mapTR_loop___redArg(v___f_277_, v___x_281_, v___x_279_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3(lean_object* v_f_285_, lean_object* v___f_286_, lean_object* v_x_287_){
_start:
{
lean_object* v_changesBefore_288_; lean_object* v_changesAfter_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v_changesBefore_288_ = lean_ctor_get(v_x_287_, 0);
lean_inc(v_changesBefore_288_);
v_changesAfter_289_ = lean_ctor_get(v_x_287_, 1);
lean_inc(v_changesAfter_289_);
lean_dec_ref(v_x_287_);
v___x_290_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__0));
lean_inc_ref(v_f_285_);
v___x_291_ = lean_apply_1(v_f_285_, v_changesBefore_288_);
lean_inc_ref(v___f_286_);
v___x_292_ = l_List_toString___redArg(v___f_286_, v___x_291_);
v___x_293_ = lean_string_append(v___x_290_, v___x_292_);
lean_dec_ref(v___x_292_);
v___x_294_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__1));
v___x_295_ = lean_string_append(v___x_293_, v___x_294_);
v___x_296_ = lean_apply_1(v_f_285_, v_changesAfter_289_);
v___x_297_ = l_List_toString___redArg(v___f_286_, v___x_296_);
v___x_298_ = lean_string_append(v___x_295_, v___x_297_);
lean_dec_ref(v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(lean_object* v_k_309_, lean_object* v_v_310_, lean_object* v_t_311_){
_start:
{
if (lean_obj_tag(v_t_311_) == 0)
{
lean_object* v_size_312_; lean_object* v_k_313_; lean_object* v_v_314_; lean_object* v_l_315_; lean_object* v_r_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_597_; 
v_size_312_ = lean_ctor_get(v_t_311_, 0);
v_k_313_ = lean_ctor_get(v_t_311_, 1);
v_v_314_ = lean_ctor_get(v_t_311_, 2);
v_l_315_ = lean_ctor_get(v_t_311_, 3);
v_r_316_ = lean_ctor_get(v_t_311_, 4);
v_isSharedCheck_597_ = !lean_is_exclusive(v_t_311_);
if (v_isSharedCheck_597_ == 0)
{
v___x_318_ = v_t_311_;
v_isShared_319_ = v_isSharedCheck_597_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_r_316_);
lean_inc(v_l_315_);
lean_inc(v_v_314_);
lean_inc(v_k_313_);
lean_inc(v_size_312_);
lean_dec(v_t_311_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_597_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
uint8_t v___x_320_; 
v___x_320_ = lean_nat_dec_lt(v_k_309_, v_k_313_);
if (v___x_320_ == 0)
{
uint8_t v___x_321_; 
v___x_321_ = lean_nat_dec_eq(v_k_309_, v_k_313_);
if (v___x_321_ == 0)
{
lean_object* v_impl_322_; lean_object* v___x_323_; 
lean_dec(v_size_312_);
v_impl_322_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_k_309_, v_v_310_, v_r_316_);
v___x_323_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_315_) == 0)
{
lean_object* v_size_324_; lean_object* v_size_325_; lean_object* v_k_326_; lean_object* v_v_327_; lean_object* v_l_328_; lean_object* v_r_329_; lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v_size_324_ = lean_ctor_get(v_l_315_, 0);
v_size_325_ = lean_ctor_get(v_impl_322_, 0);
lean_inc(v_size_325_);
v_k_326_ = lean_ctor_get(v_impl_322_, 1);
lean_inc(v_k_326_);
v_v_327_ = lean_ctor_get(v_impl_322_, 2);
lean_inc(v_v_327_);
v_l_328_ = lean_ctor_get(v_impl_322_, 3);
lean_inc(v_l_328_);
v_r_329_ = lean_ctor_get(v_impl_322_, 4);
lean_inc(v_r_329_);
v___x_330_ = lean_unsigned_to_nat(3u);
v___x_331_ = lean_nat_mul(v___x_330_, v_size_324_);
v___x_332_ = lean_nat_dec_lt(v___x_331_, v_size_325_);
lean_dec(v___x_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_336_; 
lean_dec(v_r_329_);
lean_dec(v_l_328_);
lean_dec(v_v_327_);
lean_dec(v_k_326_);
v___x_333_ = lean_nat_add(v___x_323_, v_size_324_);
v___x_334_ = lean_nat_add(v___x_333_, v_size_325_);
lean_dec(v_size_325_);
lean_dec(v___x_333_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 4, v_impl_322_);
lean_ctor_set(v___x_318_, 0, v___x_334_);
v___x_336_ = v___x_318_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_334_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_k_313_);
lean_ctor_set(v_reuseFailAlloc_337_, 2, v_v_314_);
lean_ctor_set(v_reuseFailAlloc_337_, 3, v_l_315_);
lean_ctor_set(v_reuseFailAlloc_337_, 4, v_impl_322_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
else
{
lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_401_; 
v_isSharedCheck_401_ = !lean_is_exclusive(v_impl_322_);
if (v_isSharedCheck_401_ == 0)
{
lean_object* v_unused_402_; lean_object* v_unused_403_; lean_object* v_unused_404_; lean_object* v_unused_405_; lean_object* v_unused_406_; 
v_unused_402_ = lean_ctor_get(v_impl_322_, 4);
lean_dec(v_unused_402_);
v_unused_403_ = lean_ctor_get(v_impl_322_, 3);
lean_dec(v_unused_403_);
v_unused_404_ = lean_ctor_get(v_impl_322_, 2);
lean_dec(v_unused_404_);
v_unused_405_ = lean_ctor_get(v_impl_322_, 1);
lean_dec(v_unused_405_);
v_unused_406_ = lean_ctor_get(v_impl_322_, 0);
lean_dec(v_unused_406_);
v___x_339_ = v_impl_322_;
v_isShared_340_ = v_isSharedCheck_401_;
goto v_resetjp_338_;
}
else
{
lean_dec(v_impl_322_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_401_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v_size_341_; lean_object* v_k_342_; lean_object* v_v_343_; lean_object* v_l_344_; lean_object* v_r_345_; lean_object* v_size_346_; lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v_size_341_ = lean_ctor_get(v_l_328_, 0);
v_k_342_ = lean_ctor_get(v_l_328_, 1);
v_v_343_ = lean_ctor_get(v_l_328_, 2);
v_l_344_ = lean_ctor_get(v_l_328_, 3);
v_r_345_ = lean_ctor_get(v_l_328_, 4);
v_size_346_ = lean_ctor_get(v_r_329_, 0);
v___x_347_ = lean_unsigned_to_nat(2u);
v___x_348_ = lean_nat_mul(v___x_347_, v_size_346_);
v___x_349_ = lean_nat_dec_lt(v_size_341_, v___x_348_);
lean_dec(v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_377_; 
lean_inc(v_r_345_);
lean_inc(v_l_344_);
lean_inc(v_v_343_);
lean_inc(v_k_342_);
v_isSharedCheck_377_ = !lean_is_exclusive(v_l_328_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; lean_object* v_unused_379_; lean_object* v_unused_380_; lean_object* v_unused_381_; lean_object* v_unused_382_; 
v_unused_378_ = lean_ctor_get(v_l_328_, 4);
lean_dec(v_unused_378_);
v_unused_379_ = lean_ctor_get(v_l_328_, 3);
lean_dec(v_unused_379_);
v_unused_380_ = lean_ctor_get(v_l_328_, 2);
lean_dec(v_unused_380_);
v_unused_381_ = lean_ctor_get(v_l_328_, 1);
lean_dec(v_unused_381_);
v_unused_382_ = lean_ctor_get(v_l_328_, 0);
lean_dec(v_unused_382_);
v___x_351_ = v_l_328_;
v_isShared_352_ = v_isSharedCheck_377_;
goto v_resetjp_350_;
}
else
{
lean_dec(v_l_328_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_377_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_367_; 
v___x_353_ = lean_nat_add(v___x_323_, v_size_324_);
v___x_354_ = lean_nat_add(v___x_353_, v_size_325_);
lean_dec(v_size_325_);
if (lean_obj_tag(v_l_344_) == 0)
{
lean_object* v_size_375_; 
v_size_375_ = lean_ctor_get(v_l_344_, 0);
lean_inc(v_size_375_);
v___y_367_ = v_size_375_;
goto v___jp_366_;
}
else
{
lean_object* v___x_376_; 
v___x_376_ = lean_unsigned_to_nat(0u);
v___y_367_ = v___x_376_;
goto v___jp_366_;
}
v___jp_355_:
{
lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_359_ = lean_nat_add(v___y_357_, v___y_358_);
lean_dec(v___y_358_);
lean_dec(v___y_357_);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 4, v_r_329_);
lean_ctor_set(v___x_351_, 3, v_r_345_);
lean_ctor_set(v___x_351_, 2, v_v_327_);
lean_ctor_set(v___x_351_, 1, v_k_326_);
lean_ctor_set(v___x_351_, 0, v___x_359_);
v___x_361_ = v___x_351_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_359_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_k_326_);
lean_ctor_set(v_reuseFailAlloc_365_, 2, v_v_327_);
lean_ctor_set(v_reuseFailAlloc_365_, 3, v_r_345_);
lean_ctor_set(v_reuseFailAlloc_365_, 4, v_r_329_);
v___x_361_ = v_reuseFailAlloc_365_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_363_; 
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 4, v___x_361_);
lean_ctor_set(v___x_339_, 3, v___y_356_);
lean_ctor_set(v___x_339_, 2, v_v_343_);
lean_ctor_set(v___x_339_, 1, v_k_342_);
lean_ctor_set(v___x_339_, 0, v___x_354_);
v___x_363_ = v___x_339_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_354_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_k_342_);
lean_ctor_set(v_reuseFailAlloc_364_, 2, v_v_343_);
lean_ctor_set(v_reuseFailAlloc_364_, 3, v___y_356_);
lean_ctor_set(v_reuseFailAlloc_364_, 4, v___x_361_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
v___jp_366_:
{
lean_object* v___x_368_; lean_object* v___x_370_; 
v___x_368_ = lean_nat_add(v___x_353_, v___y_367_);
lean_dec(v___y_367_);
lean_dec(v___x_353_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 4, v_l_344_);
lean_ctor_set(v___x_318_, 0, v___x_368_);
v___x_370_ = v___x_318_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_k_313_);
lean_ctor_set(v_reuseFailAlloc_374_, 2, v_v_314_);
lean_ctor_set(v_reuseFailAlloc_374_, 3, v_l_315_);
lean_ctor_set(v_reuseFailAlloc_374_, 4, v_l_344_);
v___x_370_ = v_reuseFailAlloc_374_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_371_; 
v___x_371_ = lean_nat_add(v___x_323_, v_size_346_);
if (lean_obj_tag(v_r_345_) == 0)
{
lean_object* v_size_372_; 
v_size_372_ = lean_ctor_get(v_r_345_, 0);
lean_inc(v_size_372_);
v___y_356_ = v___x_370_;
v___y_357_ = v___x_371_;
v___y_358_ = v_size_372_;
goto v___jp_355_;
}
else
{
lean_object* v___x_373_; 
v___x_373_ = lean_unsigned_to_nat(0u);
v___y_356_ = v___x_370_;
v___y_357_ = v___x_371_;
v___y_358_ = v___x_373_;
goto v___jp_355_;
}
}
}
}
}
else
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_387_; 
lean_del_object(v___x_318_);
v___x_383_ = lean_nat_add(v___x_323_, v_size_324_);
v___x_384_ = lean_nat_add(v___x_383_, v_size_325_);
lean_dec(v_size_325_);
v___x_385_ = lean_nat_add(v___x_383_, v_size_341_);
lean_dec(v___x_383_);
lean_inc_ref(v_l_315_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 4, v_l_328_);
lean_ctor_set(v___x_339_, 3, v_l_315_);
lean_ctor_set(v___x_339_, 2, v_v_314_);
lean_ctor_set(v___x_339_, 1, v_k_313_);
lean_ctor_set(v___x_339_, 0, v___x_385_);
v___x_387_ = v___x_339_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_385_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v_k_313_);
lean_ctor_set(v_reuseFailAlloc_400_, 2, v_v_314_);
lean_ctor_set(v_reuseFailAlloc_400_, 3, v_l_315_);
lean_ctor_set(v_reuseFailAlloc_400_, 4, v_l_328_);
v___x_387_ = v_reuseFailAlloc_400_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
v_isSharedCheck_394_ = !lean_is_exclusive(v_l_315_);
if (v_isSharedCheck_394_ == 0)
{
lean_object* v_unused_395_; lean_object* v_unused_396_; lean_object* v_unused_397_; lean_object* v_unused_398_; lean_object* v_unused_399_; 
v_unused_395_ = lean_ctor_get(v_l_315_, 4);
lean_dec(v_unused_395_);
v_unused_396_ = lean_ctor_get(v_l_315_, 3);
lean_dec(v_unused_396_);
v_unused_397_ = lean_ctor_get(v_l_315_, 2);
lean_dec(v_unused_397_);
v_unused_398_ = lean_ctor_get(v_l_315_, 1);
lean_dec(v_unused_398_);
v_unused_399_ = lean_ctor_get(v_l_315_, 0);
lean_dec(v_unused_399_);
v___x_389_ = v_l_315_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_dec(v_l_315_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 4, v_r_329_);
lean_ctor_set(v___x_389_, 3, v___x_387_);
lean_ctor_set(v___x_389_, 2, v_v_327_);
lean_ctor_set(v___x_389_, 1, v_k_326_);
lean_ctor_set(v___x_389_, 0, v___x_384_);
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_384_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v_k_326_);
lean_ctor_set(v_reuseFailAlloc_393_, 2, v_v_327_);
lean_ctor_set(v_reuseFailAlloc_393_, 3, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_393_, 4, v_r_329_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_407_; 
v_l_407_ = lean_ctor_get(v_impl_322_, 3);
lean_inc(v_l_407_);
if (lean_obj_tag(v_l_407_) == 0)
{
lean_object* v_r_408_; lean_object* v_k_409_; lean_object* v_v_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_433_; 
v_r_408_ = lean_ctor_get(v_impl_322_, 4);
v_k_409_ = lean_ctor_get(v_impl_322_, 1);
v_v_410_ = lean_ctor_get(v_impl_322_, 2);
v_isSharedCheck_433_ = !lean_is_exclusive(v_impl_322_);
if (v_isSharedCheck_433_ == 0)
{
lean_object* v_unused_434_; lean_object* v_unused_435_; 
v_unused_434_ = lean_ctor_get(v_impl_322_, 3);
lean_dec(v_unused_434_);
v_unused_435_ = lean_ctor_get(v_impl_322_, 0);
lean_dec(v_unused_435_);
v___x_412_ = v_impl_322_;
v_isShared_413_ = v_isSharedCheck_433_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_r_408_);
lean_inc(v_v_410_);
lean_inc(v_k_409_);
lean_dec(v_impl_322_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_433_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v_k_414_; lean_object* v_v_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_429_; 
v_k_414_ = lean_ctor_get(v_l_407_, 1);
v_v_415_ = lean_ctor_get(v_l_407_, 2);
v_isSharedCheck_429_ = !lean_is_exclusive(v_l_407_);
if (v_isSharedCheck_429_ == 0)
{
lean_object* v_unused_430_; lean_object* v_unused_431_; lean_object* v_unused_432_; 
v_unused_430_ = lean_ctor_get(v_l_407_, 4);
lean_dec(v_unused_430_);
v_unused_431_ = lean_ctor_get(v_l_407_, 3);
lean_dec(v_unused_431_);
v_unused_432_ = lean_ctor_get(v_l_407_, 0);
lean_dec(v_unused_432_);
v___x_417_ = v_l_407_;
v_isShared_418_ = v_isSharedCheck_429_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_v_415_);
lean_inc(v_k_414_);
lean_dec(v_l_407_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_429_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_419_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_408_, 2);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 4, v_r_408_);
lean_ctor_set(v___x_417_, 3, v_r_408_);
lean_ctor_set(v___x_417_, 2, v_v_314_);
lean_ctor_set(v___x_417_, 1, v_k_313_);
lean_ctor_set(v___x_417_, 0, v___x_323_);
v___x_421_ = v___x_417_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_k_313_);
lean_ctor_set(v_reuseFailAlloc_428_, 2, v_v_314_);
lean_ctor_set(v_reuseFailAlloc_428_, 3, v_r_408_);
lean_ctor_set(v_reuseFailAlloc_428_, 4, v_r_408_);
v___x_421_ = v_reuseFailAlloc_428_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
lean_object* v___x_423_; 
lean_inc(v_r_408_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 3, v_r_408_);
lean_ctor_set(v___x_412_, 0, v___x_323_);
v___x_423_ = v___x_412_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_k_409_);
lean_ctor_set(v_reuseFailAlloc_427_, 2, v_v_410_);
lean_ctor_set(v_reuseFailAlloc_427_, 3, v_r_408_);
lean_ctor_set(v_reuseFailAlloc_427_, 4, v_r_408_);
v___x_423_ = v_reuseFailAlloc_427_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_425_; 
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 4, v___x_423_);
lean_ctor_set(v___x_318_, 3, v___x_421_);
lean_ctor_set(v___x_318_, 2, v_v_415_);
lean_ctor_set(v___x_318_, 1, v_k_414_);
lean_ctor_set(v___x_318_, 0, v___x_419_);
v___x_425_ = v___x_318_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_k_414_);
lean_ctor_set(v_reuseFailAlloc_426_, 2, v_v_415_);
lean_ctor_set(v_reuseFailAlloc_426_, 3, v___x_421_);
lean_ctor_set(v_reuseFailAlloc_426_, 4, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
}
}
else
{
lean_object* v_r_436_; 
v_r_436_ = lean_ctor_get(v_impl_322_, 4);
lean_inc(v_r_436_);
if (lean_obj_tag(v_r_436_) == 0)
{
lean_object* v_k_437_; lean_object* v_v_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_449_; 
v_k_437_ = lean_ctor_get(v_impl_322_, 1);
v_v_438_ = lean_ctor_get(v_impl_322_, 2);
v_isSharedCheck_449_ = !lean_is_exclusive(v_impl_322_);
if (v_isSharedCheck_449_ == 0)
{
lean_object* v_unused_450_; lean_object* v_unused_451_; lean_object* v_unused_452_; 
v_unused_450_ = lean_ctor_get(v_impl_322_, 4);
lean_dec(v_unused_450_);
v_unused_451_ = lean_ctor_get(v_impl_322_, 3);
lean_dec(v_unused_451_);
v_unused_452_ = lean_ctor_get(v_impl_322_, 0);
lean_dec(v_unused_452_);
v___x_440_ = v_impl_322_;
v_isShared_441_ = v_isSharedCheck_449_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_v_438_);
lean_inc(v_k_437_);
lean_dec(v_impl_322_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_449_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_442_ = lean_unsigned_to_nat(3u);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 4, v_l_407_);
lean_ctor_set(v___x_440_, 2, v_v_314_);
lean_ctor_set(v___x_440_, 1, v_k_313_);
lean_ctor_set(v___x_440_, 0, v___x_323_);
v___x_444_ = v___x_440_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_k_313_);
lean_ctor_set(v_reuseFailAlloc_448_, 2, v_v_314_);
lean_ctor_set(v_reuseFailAlloc_448_, 3, v_l_407_);
lean_ctor_set(v_reuseFailAlloc_448_, 4, v_l_407_);
v___x_444_ = v_reuseFailAlloc_448_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_446_; 
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 4, v_r_436_);
lean_ctor_set(v___x_318_, 3, v___x_444_);
lean_ctor_set(v___x_318_, 2, v_v_438_);
lean_ctor_set(v___x_318_, 1, v_k_437_);
lean_ctor_set(v___x_318_, 0, v___x_442_);
v___x_446_ = v___x_318_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_k_437_);
lean_ctor_set(v_reuseFailAlloc_447_, 2, v_v_438_);
lean_ctor_set(v_reuseFailAlloc_447_, 3, v___x_444_);
lean_ctor_set(v_reuseFailAlloc_447_, 4, v_r_436_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
else
{
lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_453_ = lean_unsigned_to_nat(2u);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 4, v_impl_322_);
lean_ctor_set(v___x_318_, 3, v_r_436_);
lean_ctor_set(v___x_318_, 0, v___x_453_);
v___x_455_ = v___x_318_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_k_313_);
lean_ctor_set(v_reuseFailAlloc_456_, 2, v_v_314_);
lean_ctor_set(v_reuseFailAlloc_456_, 3, v_r_436_);
lean_ctor_set(v_reuseFailAlloc_456_, 4, v_impl_322_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
}
else
{
lean_object* v___x_458_; 
lean_dec(v_v_314_);
lean_dec(v_k_313_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 2, v_v_310_);
lean_ctor_set(v___x_318_, 1, v_k_309_);
v___x_458_ = v___x_318_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_size_312_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_k_309_);
lean_ctor_set(v_reuseFailAlloc_459_, 2, v_v_310_);
lean_ctor_set(v_reuseFailAlloc_459_, 3, v_l_315_);
lean_ctor_set(v_reuseFailAlloc_459_, 4, v_r_316_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
else
{
lean_object* v_impl_460_; lean_object* v___x_461_; 
lean_dec(v_size_312_);
v_impl_460_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_k_309_, v_v_310_, v_l_315_);
v___x_461_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_316_) == 0)
{
lean_object* v_size_462_; lean_object* v_size_463_; lean_object* v_k_464_; lean_object* v_v_465_; lean_object* v_l_466_; lean_object* v_r_467_; lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v_size_462_ = lean_ctor_get(v_r_316_, 0);
v_size_463_ = lean_ctor_get(v_impl_460_, 0);
lean_inc(v_size_463_);
v_k_464_ = lean_ctor_get(v_impl_460_, 1);
lean_inc(v_k_464_);
v_v_465_ = lean_ctor_get(v_impl_460_, 2);
lean_inc(v_v_465_);
v_l_466_ = lean_ctor_get(v_impl_460_, 3);
lean_inc(v_l_466_);
v_r_467_ = lean_ctor_get(v_impl_460_, 4);
lean_inc(v_r_467_);
v___x_468_ = lean_unsigned_to_nat(3u);
v___x_469_ = lean_nat_mul(v___x_468_, v_size_462_);
v___x_470_ = lean_nat_dec_lt(v___x_469_, v_size_463_);
lean_dec(v___x_469_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
lean_dec(v_r_467_);
lean_dec(v_l_466_);
lean_dec(v_v_465_);
lean_dec(v_k_464_);
v___x_471_ = lean_nat_add(v___x_461_, v_size_463_);
lean_dec(v_size_463_);
v___x_472_ = lean_nat_add(v___x_471_, v_size_462_);
lean_dec(v___x_471_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 3, v_impl_460_);
lean_ctor_set(v___x_318_, 0, v___x_472_);
v___x_474_ = v___x_318_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_472_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_k_313_);
lean_ctor_set(v_reuseFailAlloc_475_, 2, v_v_314_);
lean_ctor_set(v_reuseFailAlloc_475_, 3, v_impl_460_);
lean_ctor_set(v_reuseFailAlloc_475_, 4, v_r_316_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
else
{
lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_541_; 
v_isSharedCheck_541_ = !lean_is_exclusive(v_impl_460_);
if (v_isSharedCheck_541_ == 0)
{
lean_object* v_unused_542_; lean_object* v_unused_543_; lean_object* v_unused_544_; lean_object* v_unused_545_; lean_object* v_unused_546_; 
v_unused_542_ = lean_ctor_get(v_impl_460_, 4);
lean_dec(v_unused_542_);
v_unused_543_ = lean_ctor_get(v_impl_460_, 3);
lean_dec(v_unused_543_);
v_unused_544_ = lean_ctor_get(v_impl_460_, 2);
lean_dec(v_unused_544_);
v_unused_545_ = lean_ctor_get(v_impl_460_, 1);
lean_dec(v_unused_545_);
v_unused_546_ = lean_ctor_get(v_impl_460_, 0);
lean_dec(v_unused_546_);
v___x_477_ = v_impl_460_;
v_isShared_478_ = v_isSharedCheck_541_;
goto v_resetjp_476_;
}
else
{
lean_dec(v_impl_460_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_541_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v_size_479_; lean_object* v_size_480_; lean_object* v_k_481_; lean_object* v_v_482_; lean_object* v_l_483_; lean_object* v_r_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v_size_479_ = lean_ctor_get(v_l_466_, 0);
v_size_480_ = lean_ctor_get(v_r_467_, 0);
v_k_481_ = lean_ctor_get(v_r_467_, 1);
v_v_482_ = lean_ctor_get(v_r_467_, 2);
v_l_483_ = lean_ctor_get(v_r_467_, 3);
v_r_484_ = lean_ctor_get(v_r_467_, 4);
v___x_485_ = lean_unsigned_to_nat(2u);
v___x_486_ = lean_nat_mul(v___x_485_, v_size_479_);
v___x_487_ = lean_nat_dec_lt(v_size_480_, v___x_486_);
lean_dec(v___x_486_);
if (v___x_487_ == 0)
{
lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_516_; 
lean_inc(v_r_484_);
lean_inc(v_l_483_);
lean_inc(v_v_482_);
lean_inc(v_k_481_);
v_isSharedCheck_516_ = !lean_is_exclusive(v_r_467_);
if (v_isSharedCheck_516_ == 0)
{
lean_object* v_unused_517_; lean_object* v_unused_518_; lean_object* v_unused_519_; lean_object* v_unused_520_; lean_object* v_unused_521_; 
v_unused_517_ = lean_ctor_get(v_r_467_, 4);
lean_dec(v_unused_517_);
v_unused_518_ = lean_ctor_get(v_r_467_, 3);
lean_dec(v_unused_518_);
v_unused_519_ = lean_ctor_get(v_r_467_, 2);
lean_dec(v_unused_519_);
v_unused_520_ = lean_ctor_get(v_r_467_, 1);
lean_dec(v_unused_520_);
v_unused_521_ = lean_ctor_get(v_r_467_, 0);
lean_dec(v_unused_521_);
v___x_489_ = v_r_467_;
v_isShared_490_ = v_isSharedCheck_516_;
goto v_resetjp_488_;
}
else
{
lean_dec(v_r_467_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_516_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___x_504_; lean_object* v___y_506_; 
v___x_491_ = lean_nat_add(v___x_461_, v_size_463_);
lean_dec(v_size_463_);
v___x_492_ = lean_nat_add(v___x_491_, v_size_462_);
lean_dec(v___x_491_);
v___x_504_ = lean_nat_add(v___x_461_, v_size_479_);
if (lean_obj_tag(v_l_483_) == 0)
{
lean_object* v_size_514_; 
v_size_514_ = lean_ctor_get(v_l_483_, 0);
lean_inc(v_size_514_);
v___y_506_ = v_size_514_;
goto v___jp_505_;
}
else
{
lean_object* v___x_515_; 
v___x_515_ = lean_unsigned_to_nat(0u);
v___y_506_ = v___x_515_;
goto v___jp_505_;
}
v___jp_493_:
{
lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_497_ = lean_nat_add(v___y_495_, v___y_496_);
lean_dec(v___y_496_);
lean_dec(v___y_495_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 4, v_r_316_);
lean_ctor_set(v___x_489_, 3, v_r_484_);
lean_ctor_set(v___x_489_, 2, v_v_314_);
lean_ctor_set(v___x_489_, 1, v_k_313_);
lean_ctor_set(v___x_489_, 0, v___x_497_);
v___x_499_ = v___x_489_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v_k_313_);
lean_ctor_set(v_reuseFailAlloc_503_, 2, v_v_314_);
lean_ctor_set(v_reuseFailAlloc_503_, 3, v_r_484_);
lean_ctor_set(v_reuseFailAlloc_503_, 4, v_r_316_);
v___x_499_ = v_reuseFailAlloc_503_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_501_; 
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 4, v___x_499_);
lean_ctor_set(v___x_477_, 3, v___y_494_);
lean_ctor_set(v___x_477_, 2, v_v_482_);
lean_ctor_set(v___x_477_, 1, v_k_481_);
lean_ctor_set(v___x_477_, 0, v___x_492_);
v___x_501_ = v___x_477_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v_k_481_);
lean_ctor_set(v_reuseFailAlloc_502_, 2, v_v_482_);
lean_ctor_set(v_reuseFailAlloc_502_, 3, v___y_494_);
lean_ctor_set(v_reuseFailAlloc_502_, 4, v___x_499_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
v___jp_505_:
{
lean_object* v___x_507_; lean_object* v___x_509_; 
v___x_507_ = lean_nat_add(v___x_504_, v___y_506_);
lean_dec(v___y_506_);
lean_dec(v___x_504_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 4, v_l_483_);
lean_ctor_set(v___x_318_, 3, v_l_466_);
lean_ctor_set(v___x_318_, 2, v_v_465_);
lean_ctor_set(v___x_318_, 1, v_k_464_);
lean_ctor_set(v___x_318_, 0, v___x_507_);
v___x_509_ = v___x_318_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_513_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_513_, 3, v_l_466_);
lean_ctor_set(v_reuseFailAlloc_513_, 4, v_l_483_);
v___x_509_ = v_reuseFailAlloc_513_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
lean_object* v___x_510_; 
v___x_510_ = lean_nat_add(v___x_461_, v_size_462_);
if (lean_obj_tag(v_r_484_) == 0)
{
lean_object* v_size_511_; 
v_size_511_ = lean_ctor_get(v_r_484_, 0);
lean_inc(v_size_511_);
v___y_494_ = v___x_509_;
v___y_495_ = v___x_510_;
v___y_496_ = v_size_511_;
goto v___jp_493_;
}
else
{
lean_object* v___x_512_; 
v___x_512_ = lean_unsigned_to_nat(0u);
v___y_494_ = v___x_509_;
v___y_495_ = v___x_510_;
v___y_496_ = v___x_512_;
goto v___jp_493_;
}
}
}
}
}
else
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
lean_del_object(v___x_318_);
v___x_522_ = lean_nat_add(v___x_461_, v_size_463_);
lean_dec(v_size_463_);
v___x_523_ = lean_nat_add(v___x_522_, v_size_462_);
lean_dec(v___x_522_);
v___x_524_ = lean_nat_add(v___x_461_, v_size_462_);
v___x_525_ = lean_nat_add(v___x_524_, v_size_480_);
lean_dec(v___x_524_);
lean_inc_ref(v_r_316_);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 4, v_r_316_);
lean_ctor_set(v___x_477_, 3, v_r_467_);
lean_ctor_set(v___x_477_, 2, v_v_314_);
lean_ctor_set(v___x_477_, 1, v_k_313_);
lean_ctor_set(v___x_477_, 0, v___x_525_);
v___x_527_ = v___x_477_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_525_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v_k_313_);
lean_ctor_set(v_reuseFailAlloc_540_, 2, v_v_314_);
lean_ctor_set(v_reuseFailAlloc_540_, 3, v_r_467_);
lean_ctor_set(v_reuseFailAlloc_540_, 4, v_r_316_);
v___x_527_ = v_reuseFailAlloc_540_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
v_isSharedCheck_534_ = !lean_is_exclusive(v_r_316_);
if (v_isSharedCheck_534_ == 0)
{
lean_object* v_unused_535_; lean_object* v_unused_536_; lean_object* v_unused_537_; lean_object* v_unused_538_; lean_object* v_unused_539_; 
v_unused_535_ = lean_ctor_get(v_r_316_, 4);
lean_dec(v_unused_535_);
v_unused_536_ = lean_ctor_get(v_r_316_, 3);
lean_dec(v_unused_536_);
v_unused_537_ = lean_ctor_get(v_r_316_, 2);
lean_dec(v_unused_537_);
v_unused_538_ = lean_ctor_get(v_r_316_, 1);
lean_dec(v_unused_538_);
v_unused_539_ = lean_ctor_get(v_r_316_, 0);
lean_dec(v_unused_539_);
v___x_529_ = v_r_316_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_dec(v_r_316_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 4, v___x_527_);
lean_ctor_set(v___x_529_, 3, v_l_466_);
lean_ctor_set(v___x_529_, 2, v_v_465_);
lean_ctor_set(v___x_529_, 1, v_k_464_);
lean_ctor_set(v___x_529_, 0, v___x_523_);
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_523_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_533_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_533_, 3, v_l_466_);
lean_ctor_set(v_reuseFailAlloc_533_, 4, v___x_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_547_; 
v_l_547_ = lean_ctor_get(v_impl_460_, 3);
lean_inc(v_l_547_);
if (lean_obj_tag(v_l_547_) == 0)
{
lean_object* v_r_548_; lean_object* v_k_549_; lean_object* v_v_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_561_; 
v_r_548_ = lean_ctor_get(v_impl_460_, 4);
v_k_549_ = lean_ctor_get(v_impl_460_, 1);
v_v_550_ = lean_ctor_get(v_impl_460_, 2);
v_isSharedCheck_561_ = !lean_is_exclusive(v_impl_460_);
if (v_isSharedCheck_561_ == 0)
{
lean_object* v_unused_562_; lean_object* v_unused_563_; 
v_unused_562_ = lean_ctor_get(v_impl_460_, 3);
lean_dec(v_unused_562_);
v_unused_563_ = lean_ctor_get(v_impl_460_, 0);
lean_dec(v_unused_563_);
v___x_552_ = v_impl_460_;
v_isShared_553_ = v_isSharedCheck_561_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_r_548_);
lean_inc(v_v_550_);
lean_inc(v_k_549_);
lean_dec(v_impl_460_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_561_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_554_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_548_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 3, v_r_548_);
lean_ctor_set(v___x_552_, 2, v_v_314_);
lean_ctor_set(v___x_552_, 1, v_k_313_);
lean_ctor_set(v___x_552_, 0, v___x_461_);
v___x_556_ = v___x_552_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_k_313_);
lean_ctor_set(v_reuseFailAlloc_560_, 2, v_v_314_);
lean_ctor_set(v_reuseFailAlloc_560_, 3, v_r_548_);
lean_ctor_set(v_reuseFailAlloc_560_, 4, v_r_548_);
v___x_556_ = v_reuseFailAlloc_560_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_558_; 
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 4, v___x_556_);
lean_ctor_set(v___x_318_, 3, v_l_547_);
lean_ctor_set(v___x_318_, 2, v_v_550_);
lean_ctor_set(v___x_318_, 1, v_k_549_);
lean_ctor_set(v___x_318_, 0, v___x_554_);
v___x_558_ = v___x_318_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_k_549_);
lean_ctor_set(v_reuseFailAlloc_559_, 2, v_v_550_);
lean_ctor_set(v_reuseFailAlloc_559_, 3, v_l_547_);
lean_ctor_set(v_reuseFailAlloc_559_, 4, v___x_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
else
{
lean_object* v_r_564_; 
v_r_564_ = lean_ctor_get(v_impl_460_, 4);
lean_inc(v_r_564_);
if (lean_obj_tag(v_r_564_) == 0)
{
lean_object* v_k_565_; lean_object* v_v_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_589_; 
v_k_565_ = lean_ctor_get(v_impl_460_, 1);
v_v_566_ = lean_ctor_get(v_impl_460_, 2);
v_isSharedCheck_589_ = !lean_is_exclusive(v_impl_460_);
if (v_isSharedCheck_589_ == 0)
{
lean_object* v_unused_590_; lean_object* v_unused_591_; lean_object* v_unused_592_; 
v_unused_590_ = lean_ctor_get(v_impl_460_, 4);
lean_dec(v_unused_590_);
v_unused_591_ = lean_ctor_get(v_impl_460_, 3);
lean_dec(v_unused_591_);
v_unused_592_ = lean_ctor_get(v_impl_460_, 0);
lean_dec(v_unused_592_);
v___x_568_ = v_impl_460_;
v_isShared_569_ = v_isSharedCheck_589_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_v_566_);
lean_inc(v_k_565_);
lean_dec(v_impl_460_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_589_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v_k_570_; lean_object* v_v_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_585_; 
v_k_570_ = lean_ctor_get(v_r_564_, 1);
v_v_571_ = lean_ctor_get(v_r_564_, 2);
v_isSharedCheck_585_ = !lean_is_exclusive(v_r_564_);
if (v_isSharedCheck_585_ == 0)
{
lean_object* v_unused_586_; lean_object* v_unused_587_; lean_object* v_unused_588_; 
v_unused_586_ = lean_ctor_get(v_r_564_, 4);
lean_dec(v_unused_586_);
v_unused_587_ = lean_ctor_get(v_r_564_, 3);
lean_dec(v_unused_587_);
v_unused_588_ = lean_ctor_get(v_r_564_, 0);
lean_dec(v_unused_588_);
v___x_573_ = v_r_564_;
v_isShared_574_ = v_isSharedCheck_585_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_v_571_);
lean_inc(v_k_570_);
lean_dec(v_r_564_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_585_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_575_ = lean_unsigned_to_nat(3u);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 4, v_l_547_);
lean_ctor_set(v___x_573_, 3, v_l_547_);
lean_ctor_set(v___x_573_, 2, v_v_566_);
lean_ctor_set(v___x_573_, 1, v_k_565_);
lean_ctor_set(v___x_573_, 0, v___x_461_);
v___x_577_ = v___x_573_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_k_565_);
lean_ctor_set(v_reuseFailAlloc_584_, 2, v_v_566_);
lean_ctor_set(v_reuseFailAlloc_584_, 3, v_l_547_);
lean_ctor_set(v_reuseFailAlloc_584_, 4, v_l_547_);
v___x_577_ = v_reuseFailAlloc_584_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_579_; 
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 4, v_l_547_);
lean_ctor_set(v___x_568_, 2, v_v_314_);
lean_ctor_set(v___x_568_, 1, v_k_313_);
lean_ctor_set(v___x_568_, 0, v___x_461_);
v___x_579_ = v___x_568_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_k_313_);
lean_ctor_set(v_reuseFailAlloc_583_, 2, v_v_314_);
lean_ctor_set(v_reuseFailAlloc_583_, 3, v_l_547_);
lean_ctor_set(v_reuseFailAlloc_583_, 4, v_l_547_);
v___x_579_ = v_reuseFailAlloc_583_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_581_; 
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 4, v___x_579_);
lean_ctor_set(v___x_318_, 3, v___x_577_);
lean_ctor_set(v___x_318_, 2, v_v_571_);
lean_ctor_set(v___x_318_, 1, v_k_570_);
lean_ctor_set(v___x_318_, 0, v___x_575_);
v___x_581_ = v___x_318_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_k_570_);
lean_ctor_set(v_reuseFailAlloc_582_, 2, v_v_571_);
lean_ctor_set(v_reuseFailAlloc_582_, 3, v___x_577_);
lean_ctor_set(v_reuseFailAlloc_582_, 4, v___x_579_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
}
}
else
{
lean_object* v___x_593_; lean_object* v___x_595_; 
v___x_593_ = lean_unsigned_to_nat(2u);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 4, v_r_564_);
lean_ctor_set(v___x_318_, 3, v_impl_460_);
lean_ctor_set(v___x_318_, 0, v___x_593_);
v___x_595_ = v___x_318_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_k_313_);
lean_ctor_set(v_reuseFailAlloc_596_, 2, v_v_314_);
lean_ctor_set(v_reuseFailAlloc_596_, 3, v_impl_460_);
lean_ctor_set(v_reuseFailAlloc_596_, 4, v_r_564_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_unsigned_to_nat(1u);
v___x_599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
lean_ctor_set(v___x_599_, 1, v_k_309_);
lean_ctor_set(v___x_599_, 2, v_v_310_);
lean_ctor_set(v___x_599_, 3, v_t_311_);
lean_ctor_set(v___x_599_, 4, v_t_311_);
return v___x_599_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange(lean_object* v_p_600_, uint8_t v_d_601_, lean_object* v_00_u03b4_602_){
_start:
{
lean_object* v_changesBefore_603_; lean_object* v_changesAfter_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_613_; 
v_changesBefore_603_ = lean_ctor_get(v_00_u03b4_602_, 0);
v_changesAfter_604_ = lean_ctor_get(v_00_u03b4_602_, 1);
v_isSharedCheck_613_ = !lean_is_exclusive(v_00_u03b4_602_);
if (v_isSharedCheck_613_ == 0)
{
v___x_606_ = v_00_u03b4_602_;
v_isShared_607_ = v_isSharedCheck_613_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_changesAfter_604_);
lean_inc(v_changesBefore_603_);
lean_dec(v_00_u03b4_602_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_613_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_608_ = lean_box(v_d_601_);
v___x_609_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_p_600_, v___x_608_, v_changesBefore_603_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v___x_609_);
v___x_611_ = v___x_606_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_changesAfter_604_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange___boxed(lean_object* v_p_614_, lean_object* v_d_615_, lean_object* v_00_u03b4_616_){
_start:
{
uint8_t v_d_boxed_617_; lean_object* v_res_618_; 
v_d_boxed_617_ = lean_unbox(v_d_615_);
v_res_618_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange(v_p_614_, v_d_boxed_617_, v_00_u03b4_616_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0(lean_object* v_00_u03b2_619_, lean_object* v_k_620_, lean_object* v_v_621_, lean_object* v_t_622_, lean_object* v_hl_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_k_620_, v_v_621_, v_t_622_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertAfterChange(lean_object* v_p_625_, uint8_t v_d_626_, lean_object* v_00_u03b4_627_){
_start:
{
lean_object* v_changesBefore_628_; lean_object* v_changesAfter_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_638_; 
v_changesBefore_628_ = lean_ctor_get(v_00_u03b4_627_, 0);
v_changesAfter_629_ = lean_ctor_get(v_00_u03b4_627_, 1);
v_isSharedCheck_638_ = !lean_is_exclusive(v_00_u03b4_627_);
if (v_isSharedCheck_638_ == 0)
{
v___x_631_ = v_00_u03b4_627_;
v_isShared_632_ = v_isSharedCheck_638_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_changesAfter_629_);
lean_inc(v_changesBefore_628_);
lean_dec(v_00_u03b4_627_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_638_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_633_ = lean_box(v_d_626_);
v___x_634_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_p_625_, v___x_633_, v_changesAfter_629_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 1, v___x_634_);
v___x_636_ = v___x_631_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_changesBefore_628_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v___x_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertAfterChange___boxed(lean_object* v_p_639_, lean_object* v_d_640_, lean_object* v_00_u03b4_641_){
_start:
{
uint8_t v_d_boxed_642_; lean_object* v_res_643_; 
v_d_boxed_642_ = lean_unbox(v_d_640_);
v_res_643_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertAfterChange(v_p_639_, v_d_boxed_642_, v_00_u03b4_641_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(lean_object* v_before_644_, lean_object* v_after_645_, uint8_t v_d_646_){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_647_ = lean_box(1);
v___x_648_ = lean_box(v_d_646_);
v___x_649_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_before_644_, v___x_648_, v___x_647_);
v___x_650_ = lean_box(v_d_646_);
v___x_651_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_after_645_, v___x_650_, v___x_647_);
v___x_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_649_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos___boxed(lean_object* v_before_653_, lean_object* v_after_654_, lean_object* v_d_655_){
_start:
{
uint8_t v_d_boxed_656_; lean_object* v_res_657_; 
v_d_boxed_656_ = lean_unbox(v_d_655_);
v_res_657_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v_before_653_, v_after_654_, v_d_boxed_656_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(lean_object* v_before_658_, lean_object* v_after_659_, uint8_t v_d_660_){
_start:
{
lean_object* v_pos_661_; lean_object* v_pos_662_; lean_object* v___x_663_; 
v_pos_661_ = lean_ctor_get(v_before_658_, 1);
lean_inc(v_pos_661_);
lean_dec_ref(v_before_658_);
v_pos_662_ = lean_ctor_get(v_after_659_, 1);
lean_inc(v_pos_662_);
lean_dec_ref(v_after_659_);
v___x_663_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v_pos_661_, v_pos_662_, v_d_660_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange___boxed(lean_object* v_before_664_, lean_object* v_after_665_, lean_object* v_d_666_){
_start:
{
uint8_t v_d_boxed_667_; lean_object* v_res_668_; 
v_d_boxed_667_ = lean_unbox(v_d_666_);
v_res_668_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_664_, v_after_665_, v_d_boxed_667_);
return v_res_668_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(lean_object* v_d_669_){
_start:
{
lean_object* v_changesAfter_670_; 
v_changesAfter_670_ = lean_ctor_get(v_d_669_, 1);
if (lean_obj_tag(v_changesAfter_670_) == 0)
{
uint8_t v___x_671_; 
v___x_671_ = 0;
return v___x_671_;
}
else
{
lean_object* v_changesBefore_672_; 
v_changesBefore_672_ = lean_ctor_get(v_d_669_, 0);
if (lean_obj_tag(v_changesBefore_672_) == 0)
{
uint8_t v___x_673_; 
v___x_673_ = 0;
return v___x_673_;
}
else
{
uint8_t v___x_674_; 
v___x_674_ = 1;
return v___x_674_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty___boxed(lean_object* v_d_675_){
_start:
{
uint8_t v_res_676_; lean_object* v_r_677_; 
v_res_676_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_d_675_);
lean_dec_ref(v_d_675_);
v_r_677_ = lean_box(v_res_676_);
return v_r_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0(lean_object* v_k_678_, lean_object* v_b_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v___x_685_; 
lean_inc(v___y_683_);
lean_inc_ref(v___y_682_);
lean_inc(v___y_681_);
lean_inc_ref(v___y_680_);
v___x_685_ = lean_apply_6(v_k_678_, v_b_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, lean_box(0));
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0___boxed(lean_object* v_k_686_, lean_object* v_b_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0(v_k_686_, v_b_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(lean_object* v_name_694_, uint8_t v_bi_695_, lean_object* v_type_696_, lean_object* v_k_697_, uint8_t v_kind_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v___f_704_; lean_object* v___x_705_; 
v___f_704_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_704_, 0, v_k_697_);
v___x_705_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_694_, v_bi_695_, v_type_696_, v___f_704_, v_kind_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_705_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_705_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
v_a_714_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_705_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_705_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___boxed(lean_object* v_name_722_, lean_object* v_bi_723_, lean_object* v_type_724_, lean_object* v_k_725_, lean_object* v_kind_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
uint8_t v_bi_boxed_732_; uint8_t v_kind_boxed_733_; lean_object* v_res_734_; 
v_bi_boxed_732_ = lean_unbox(v_bi_723_);
v_kind_boxed_733_ = lean_unbox(v_kind_726_);
v_res_734_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_name_722_, v_bi_boxed_732_, v_type_724_, v_k_725_, v_kind_boxed_733_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6(lean_object* v_00_u03b1_735_, lean_object* v_name_736_, uint8_t v_bi_737_, lean_object* v_type_738_, lean_object* v_k_739_, uint8_t v_kind_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_name_736_, v_bi_737_, v_type_738_, v_k_739_, v_kind_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___boxed(lean_object* v_00_u03b1_747_, lean_object* v_name_748_, lean_object* v_bi_749_, lean_object* v_type_750_, lean_object* v_k_751_, lean_object* v_kind_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
uint8_t v_bi_boxed_758_; uint8_t v_kind_boxed_759_; lean_object* v_res_760_; 
v_bi_boxed_758_ = lean_unbox(v_bi_749_);
v_kind_boxed_759_ = lean_unbox(v_kind_752_);
v_res_760_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6(v_00_u03b1_747_, v_name_748_, v_bi_boxed_758_, v_type_750_, v_k_751_, v_kind_boxed_759_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(lean_object* v_msgData_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v___x_767_; lean_object* v_env_768_; lean_object* v___x_769_; lean_object* v_mctx_770_; lean_object* v_lctx_771_; lean_object* v_options_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_767_ = lean_st_ref_get(v___y_765_);
v_env_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc_ref(v_env_768_);
lean_dec(v___x_767_);
v___x_769_ = lean_st_ref_get(v___y_763_);
v_mctx_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc_ref(v_mctx_770_);
lean_dec(v___x_769_);
v_lctx_771_ = lean_ctor_get(v___y_762_, 2);
v_options_772_ = lean_ctor_get(v___y_764_, 2);
lean_inc_ref(v_options_772_);
lean_inc_ref(v_lctx_771_);
v___x_773_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_773_, 0, v_env_768_);
lean_ctor_set(v___x_773_, 1, v_mctx_770_);
lean_ctor_set(v___x_773_, 2, v_lctx_771_);
lean_ctor_set(v___x_773_, 3, v_options_772_);
v___x_774_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
lean_ctor_set(v___x_774_, 1, v_msgData_761_);
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4___boxed(lean_object* v_msgData_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(v_msgData_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(lean_object* v_msg_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_ref_789_; lean_object* v___x_790_; lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_799_; 
v_ref_789_ = lean_ctor_get(v___y_786_, 5);
v___x_790_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(v_msg_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
v_a_791_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_799_ == 0)
{
v___x_793_ = v___x_790_;
v_isShared_794_ = v_isSharedCheck_799_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_790_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_799_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v___x_797_; 
lean_inc(v_ref_789_);
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v_ref_789_);
lean_ctor_set(v___x_795_, 1, v_a_791_);
if (v_isShared_794_ == 0)
{
lean_ctor_set_tag(v___x_793_, 1);
lean_ctor_set(v___x_793_, 0, v___x_795_);
v___x_797_ = v___x_793_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_795_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg___boxed(lean_object* v_msg_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v_msg_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(lean_object* v_x_807_, lean_object* v_x_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
if (lean_obj_tag(v_x_807_) == 0)
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = l_List_reverse___redArg(v_x_808_);
v___x_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
return v___x_815_;
}
else
{
lean_object* v_head_816_; lean_object* v_tail_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_835_; 
v_head_816_ = lean_ctor_get(v_x_807_, 0);
v_tail_817_ = lean_ctor_get(v_x_807_, 1);
v_isSharedCheck_835_ = !lean_is_exclusive(v_x_807_);
if (v_isSharedCheck_835_ == 0)
{
v___x_819_ = v_x_807_;
v_isShared_820_ = v_isSharedCheck_835_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_tail_817_);
lean_inc(v_head_816_);
lean_dec(v_x_807_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_835_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; 
v___x_821_ = l_Lean_Meta_getFVarFromUserName(v_head_816_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_824_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_a_822_);
lean_dec_ref_known(v___x_821_, 1);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 1, v_x_808_);
lean_ctor_set(v___x_819_, 0, v_a_822_);
v___x_824_ = v___x_819_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_822_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v_x_808_);
v___x_824_ = v_reuseFailAlloc_826_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
v_x_807_ = v_tail_817_;
v_x_808_ = v___x_824_;
goto _start;
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_del_object(v___x_819_);
lean_dec(v_tail_817_);
lean_dec(v_x_808_);
v_a_827_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_821_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_821_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2___boxed(lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(v_x_836_, v_x_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(lean_object* v_upperBound_844_, lean_object* v_before_845_, lean_object* v_a_846_, lean_object* v_b_847_){
_start:
{
uint8_t v___x_849_; 
v___x_849_ = lean_nat_dec_lt(v_a_846_, v_upperBound_844_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; 
lean_dec(v_a_846_);
lean_dec_ref(v_before_845_);
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v_b_847_);
return v___x_850_;
}
else
{
lean_object* v_pos_851_; lean_object* v___x_852_; uint8_t v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v_pos_851_ = lean_ctor_get(v_before_845_, 1);
lean_inc(v_pos_851_);
lean_inc(v_a_846_);
v___x_852_ = l_Lean_SubExpr_Pos_pushNthBindingDomain(v_a_846_, v_pos_851_);
v___x_853_ = 1;
v___x_854_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange(v___x_852_, v___x_853_, v_b_847_);
v___x_855_ = lean_unsigned_to_nat(1u);
v___x_856_ = lean_nat_add(v_a_846_, v___x_855_);
lean_dec(v_a_846_);
v_a_846_ = v___x_856_;
v_b_847_ = v___x_854_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg___boxed(lean_object* v_upperBound_858_, lean_object* v_before_859_, lean_object* v_a_860_, lean_object* v_b_861_, lean_object* v___y_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v_upperBound_858_, v_before_859_, v_a_860_, v_b_861_);
lean_dec(v_upperBound_858_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0(lean_object* v_x_864_, lean_object* v_x_865_){
_start:
{
if (lean_obj_tag(v_x_864_) == 0)
{
lean_object* v___x_866_; 
v___x_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_866_, 0, v_x_865_);
return v___x_866_;
}
else
{
if (lean_obj_tag(v_x_865_) == 0)
{
lean_object* v___x_867_; 
v___x_867_ = lean_box(0);
return v___x_867_;
}
else
{
lean_object* v_head_868_; lean_object* v_tail_869_; lean_object* v_head_870_; lean_object* v_tail_871_; uint8_t v___x_872_; 
v_head_868_ = lean_ctor_get(v_x_864_, 0);
v_tail_869_ = lean_ctor_get(v_x_864_, 1);
v_head_870_ = lean_ctor_get(v_x_865_, 0);
lean_inc(v_head_870_);
v_tail_871_ = lean_ctor_get(v_x_865_, 1);
lean_inc(v_tail_871_);
lean_dec_ref_known(v_x_865_, 2);
v___x_872_ = lean_name_eq(v_head_868_, v_head_870_);
lean_dec(v_head_870_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; 
lean_dec(v_tail_871_);
v___x_873_ = lean_box(0);
return v___x_873_;
}
else
{
v_x_864_ = v_tail_869_;
v_x_865_ = v_tail_871_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0___boxed(lean_object* v_x_875_, lean_object* v_x_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0(v_x_875_, v_x_876_);
lean_dec(v_x_875_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0(lean_object* v_l_u2081_878_, lean_object* v_l_u2082_879_){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_880_ = l_List_reverse___redArg(v_l_u2081_878_);
v___x_881_ = l_List_reverse___redArg(v_l_u2082_879_);
v___x_882_ = l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0(v___x_880_, v___x_881_);
lean_dec(v___x_880_);
if (lean_obj_tag(v___x_882_) == 0)
{
return v___x_882_;
}
else
{
lean_object* v_val_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_891_; 
v_val_883_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_891_ == 0)
{
v___x_885_ = v___x_882_;
v_isShared_886_ = v_isSharedCheck_891_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_val_883_);
lean_dec(v___x_882_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_891_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_887_ = l_List_reverse___redArg(v_val_883_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_887_);
v___x_889_ = v___x_885_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(uint8_t v_b_u2082_892_, lean_object* v_k_893_, lean_object* v_t_894_){
_start:
{
if (lean_obj_tag(v_t_894_) == 0)
{
lean_object* v_size_895_; lean_object* v_k_896_; lean_object* v_v_897_; lean_object* v_l_898_; lean_object* v_r_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_913_; 
v_size_895_ = lean_ctor_get(v_t_894_, 0);
v_k_896_ = lean_ctor_get(v_t_894_, 1);
v_v_897_ = lean_ctor_get(v_t_894_, 2);
v_l_898_ = lean_ctor_get(v_t_894_, 3);
v_r_899_ = lean_ctor_get(v_t_894_, 4);
v_isSharedCheck_913_ = !lean_is_exclusive(v_t_894_);
if (v_isSharedCheck_913_ == 0)
{
v___x_901_ = v_t_894_;
v_isShared_902_ = v_isSharedCheck_913_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_r_899_);
lean_inc(v_l_898_);
lean_inc(v_v_897_);
lean_inc(v_k_896_);
lean_inc(v_size_895_);
lean_dec(v_t_894_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_913_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
uint8_t v___x_903_; 
v___x_903_ = lean_nat_dec_lt(v_k_893_, v_k_896_);
if (v___x_903_ == 0)
{
uint8_t v___x_904_; 
v___x_904_ = lean_nat_dec_eq(v_k_893_, v_k_896_);
if (v___x_904_ == 0)
{
lean_object* v_impl_905_; lean_object* v___x_906_; 
lean_del_object(v___x_901_);
lean_dec(v_size_895_);
v_impl_905_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_892_, v_k_893_, v_r_899_);
v___x_906_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_896_, v_v_897_, v_l_898_, v_impl_905_);
return v___x_906_;
}
else
{
lean_object* v___x_907_; lean_object* v___x_909_; 
lean_dec(v_v_897_);
lean_dec(v_k_896_);
v___x_907_ = lean_box(v_b_u2082_892_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 2, v___x_907_);
lean_ctor_set(v___x_901_, 1, v_k_893_);
v___x_909_ = v___x_901_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_size_895_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_k_893_);
lean_ctor_set(v_reuseFailAlloc_910_, 2, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_910_, 3, v_l_898_);
lean_ctor_set(v_reuseFailAlloc_910_, 4, v_r_899_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
else
{
lean_object* v_impl_911_; lean_object* v___x_912_; 
lean_del_object(v___x_901_);
lean_dec(v_size_895_);
v_impl_911_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_892_, v_k_893_, v_l_898_);
v___x_912_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_896_, v_v_897_, v_impl_911_, v_r_899_);
return v___x_912_;
}
}
}
else
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_914_ = lean_unsigned_to_nat(1u);
v___x_915_ = lean_box(v_b_u2082_892_);
v___x_916_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_916_, 0, v___x_914_);
lean_ctor_set(v___x_916_, 1, v_k_893_);
lean_ctor_set(v___x_916_, 2, v___x_915_);
lean_ctor_set(v___x_916_, 3, v_t_894_);
lean_ctor_set(v___x_916_, 4, v_t_894_);
return v___x_916_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg___boxed(lean_object* v_b_u2082_917_, lean_object* v_k_918_, lean_object* v_t_919_){
_start:
{
uint8_t v_b_u2082_boxed_920_; lean_object* v_res_921_; 
v_b_u2082_boxed_920_ = lean_unbox(v_b_u2082_917_);
v_res_921_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_boxed_920_, v_k_918_, v_t_919_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(lean_object* v_init_922_, lean_object* v_x_923_){
_start:
{
if (lean_obj_tag(v_x_923_) == 0)
{
lean_object* v_k_924_; lean_object* v_v_925_; lean_object* v_l_926_; lean_object* v_r_927_; lean_object* v___x_928_; uint8_t v___x_929_; lean_object* v___x_930_; 
v_k_924_ = lean_ctor_get(v_x_923_, 1);
lean_inc(v_k_924_);
v_v_925_ = lean_ctor_get(v_x_923_, 2);
lean_inc(v_v_925_);
v_l_926_ = lean_ctor_get(v_x_923_, 3);
lean_inc(v_l_926_);
v_r_927_ = lean_ctor_get(v_x_923_, 4);
lean_inc(v_r_927_);
lean_dec_ref_known(v_x_923_, 5);
v___x_928_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_init_922_, v_l_926_);
v___x_929_ = lean_unbox(v_v_925_);
lean_dec(v_v_925_);
v___x_930_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v___x_929_, v_k_924_, v___x_928_);
v_init_922_ = v___x_930_;
v_x_923_ = v_r_927_;
goto _start;
}
else
{
return v_init_922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(lean_object* v_as_932_, size_t v_i_933_, size_t v_stop_934_, lean_object* v_b_935_){
_start:
{
uint8_t v___x_936_; 
v___x_936_ = lean_usize_dec_eq(v_i_933_, v_stop_934_);
if (v___x_936_ == 0)
{
lean_object* v_changesBefore_937_; lean_object* v_changesAfter_938_; lean_object* v___x_939_; lean_object* v_changesBefore_940_; lean_object* v_changesAfter_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_953_; 
v_changesBefore_937_ = lean_ctor_get(v_b_935_, 0);
lean_inc(v_changesBefore_937_);
v_changesAfter_938_ = lean_ctor_get(v_b_935_, 1);
lean_inc(v_changesAfter_938_);
lean_dec_ref(v_b_935_);
v___x_939_ = lean_array_uget(v_as_932_, v_i_933_);
v_changesBefore_940_ = lean_ctor_get(v___x_939_, 0);
v_changesAfter_941_ = lean_ctor_get(v___x_939_, 1);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_953_ == 0)
{
v___x_943_ = v___x_939_;
v_isShared_944_ = v_isSharedCheck_953_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_changesAfter_941_);
lean_inc(v_changesBefore_940_);
lean_dec(v___x_939_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_953_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_948_; 
v___x_945_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesBefore_937_, v_changesBefore_940_);
v___x_946_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesAfter_938_, v_changesAfter_941_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 1, v___x_946_);
lean_ctor_set(v___x_943_, 0, v___x_945_);
v___x_948_ = v___x_943_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v___x_946_);
v___x_948_ = v_reuseFailAlloc_952_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
size_t v___x_949_; size_t v___x_950_; 
v___x_949_ = ((size_t)1ULL);
v___x_950_ = lean_usize_add(v_i_933_, v___x_949_);
v_i_933_ = v___x_950_;
v_b_935_ = v___x_948_;
goto _start;
}
}
}
else
{
return v_b_935_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10___boxed(lean_object* v_as_954_, lean_object* v_i_955_, lean_object* v_stop_956_, lean_object* v_b_957_){
_start:
{
size_t v_i_boxed_958_; size_t v_stop_boxed_959_; lean_object* v_res_960_; 
v_i_boxed_958_ = lean_unbox_usize(v_i_955_);
lean_dec(v_i_955_);
v_stop_boxed_959_ = lean_unbox_usize(v_stop_956_);
lean_dec(v_stop_956_);
v_res_960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_as_954_, v_i_boxed_958_, v_stop_boxed_959_, v_b_957_);
lean_dec_ref(v_as_954_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(lean_object* v_x_961_, lean_object* v_x_962_, lean_object* v_x_963_){
_start:
{
if (lean_obj_tag(v_x_961_) == 5)
{
lean_object* v_fn_964_; lean_object* v_arg_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v_fn_964_ = lean_ctor_get(v_x_961_, 0);
lean_inc_ref(v_fn_964_);
v_arg_965_ = lean_ctor_get(v_x_961_, 1);
lean_inc_ref(v_arg_965_);
lean_dec_ref_known(v_x_961_, 2);
v___x_966_ = lean_array_set(v_x_962_, v_x_963_, v_arg_965_);
v___x_967_ = lean_unsigned_to_nat(1u);
v___x_968_ = lean_nat_sub(v_x_963_, v___x_967_);
lean_dec(v_x_963_);
v_x_961_ = v_fn_964_;
v_x_962_ = v___x_966_;
v_x_963_ = v___x_968_;
goto _start;
}
else
{
lean_object* v___x_970_; 
lean_dec(v_x_963_);
v___x_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_970_, 0, v_x_961_);
lean_ctor_set(v___x_970_, 1, v_x_962_);
return v___x_970_;
}
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0(void){
_start:
{
lean_object* v___x_971_; lean_object* v_dummy_972_; 
v___x_971_ = lean_box(0);
v_dummy_972_ = l_Lean_Expr_sort___override(v___x_971_);
return v_dummy_972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(lean_object* v_snd_973_, lean_object* v_before_974_, lean_object* v_after_975_, size_t v_sz_976_, size_t v_i_977_, lean_object* v_bs_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
uint8_t v___x_984_; 
v___x_984_ = lean_usize_dec_lt(v_i_977_, v_sz_976_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; 
v___x_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_985_, 0, v_bs_978_);
return v___x_985_;
}
else
{
lean_object* v_v_986_; lean_object* v_fst_987_; lean_object* v_snd_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1018_; 
v_v_986_ = lean_array_uget(v_bs_978_, v_i_977_);
v_fst_987_ = lean_ctor_get(v_v_986_, 0);
v_snd_988_ = lean_ctor_get(v_v_986_, 1);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_v_986_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_990_ = v_v_986_;
v_isShared_991_ = v_isSharedCheck_1018_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_snd_988_);
lean_inc(v_fst_987_);
lean_dec(v_v_986_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1018_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v_pos_992_; lean_object* v_pos_993_; lean_object* v___x_994_; lean_object* v_bs_x27_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_1000_; 
v_pos_992_ = lean_ctor_get(v_before_974_, 1);
v_pos_993_ = lean_ctor_get(v_after_975_, 1);
v___x_994_ = lean_unsigned_to_nat(0u);
v_bs_x27_995_ = lean_array_uset(v_bs_978_, v_i_977_, v___x_994_);
v___x_996_ = lean_usize_to_nat(v_i_977_);
v___x_997_ = lean_array_get_size(v_snd_973_);
v___x_998_ = l_Lean_SubExpr_Pos_pushNaryArg(v___x_997_, v___x_996_, v_pos_992_);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 1, v___x_998_);
v___x_1000_ = v___x_990_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_fst_987_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v___x_998_);
v___x_1000_ = v_reuseFailAlloc_1017_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1001_ = l_Lean_SubExpr_Pos_pushNaryArg(v___x_997_, v___x_996_, v_pos_993_);
lean_dec(v___x_996_);
v___x_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1002_, 0, v_snd_988_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1000_, v___x_1002_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; size_t v___x_1005_; size_t v___x_1006_; lean_object* v___x_1007_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1005_ = ((size_t)1ULL);
v___x_1006_ = lean_usize_add(v_i_977_, v___x_1005_);
v___x_1007_ = lean_array_uset(v_bs_x27_995_, v_i_977_, v_a_1004_);
v_i_977_ = v___x_1006_;
v_bs_978_ = v___x_1007_;
goto _start;
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
lean_dec_ref(v_bs_x27_995_);
v_a_1009_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_1003_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1003_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
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
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__0));
v___x_1021_ = l_Lean_stringToMessageData(v___x_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0___boxed(lean_object* v_body_1022_, lean_object* v_pos_1023_, lean_object* v_body_1024_, lean_object* v_pos_1025_, lean_object* v_x_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0(v_body_1022_, v_pos_1023_, v_body_1024_, v_pos_1025_, v_x_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec_ref(v_x_1026_);
lean_dec(v_pos_1025_);
lean_dec_ref(v_body_1024_);
lean_dec(v_pos_1023_);
lean_dec_ref(v_body_1022_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(lean_object* v_before_1033_, lean_object* v_after_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v_a_1046_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; uint8_t v___y_1057_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v_a_1076_; lean_object* v_expr_1079_; lean_object* v_pos_1080_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; 
v_expr_1079_ = lean_ctor_get(v_before_1033_, 0);
v_pos_1080_ = lean_ctor_get(v_before_1033_, 1);
if (lean_obj_tag(v_expr_1079_) == 7)
{
lean_object* v_binderName_1117_; lean_object* v_binderType_1118_; lean_object* v_body_1119_; uint8_t v_binderInfo_1120_; lean_object* v_expr_1121_; lean_object* v_pos_1122_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; 
v_binderName_1117_ = lean_ctor_get(v_expr_1079_, 0);
v_binderType_1118_ = lean_ctor_get(v_expr_1079_, 1);
v_body_1119_ = lean_ctor_get(v_expr_1079_, 2);
v_binderInfo_1120_ = lean_ctor_get_uint8(v_expr_1079_, sizeof(void*)*3 + 8);
v_expr_1121_ = lean_ctor_get(v_after_1034_, 0);
v_pos_1122_ = lean_ctor_get(v_after_1034_, 1);
if (lean_obj_tag(v_expr_1121_) == 7)
{
lean_object* v_binderName_1148_; lean_object* v_binderType_1149_; lean_object* v_body_1150_; uint8_t v_binderInfo_1151_; lean_object* v___f_1152_; uint8_t v___y_1154_; uint8_t v___x_1204_; 
v_binderName_1148_ = lean_ctor_get(v_expr_1121_, 0);
v_binderType_1149_ = lean_ctor_get(v_expr_1121_, 1);
v_body_1150_ = lean_ctor_get(v_expr_1121_, 2);
v_binderInfo_1151_ = lean_ctor_get_uint8(v_expr_1121_, sizeof(void*)*3 + 8);
lean_inc(v_pos_1122_);
lean_inc_ref(v_body_1150_);
lean_inc(v_pos_1080_);
lean_inc_ref(v_body_1119_);
v___f_1152_ = lean_alloc_closure((void*)(l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1152_, 0, v_body_1119_);
lean_closure_set(v___f_1152_, 1, v_pos_1080_);
lean_closure_set(v___f_1152_, 2, v_body_1150_);
lean_closure_set(v___f_1152_, 3, v_pos_1122_);
v___x_1204_ = lean_name_eq(v_binderName_1117_, v_binderName_1148_);
if (v___x_1204_ == 0)
{
v___y_1154_ = v___x_1204_;
goto v___jp_1153_;
}
else
{
uint8_t v___x_1205_; 
v___x_1205_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1120_, v_binderInfo_1151_);
v___y_1154_ = v___x_1205_;
goto v___jp_1153_;
}
v___jp_1153_:
{
if (v___y_1154_ == 0)
{
lean_dec_ref(v___f_1152_);
v___y_1124_ = v_a_1035_;
v___y_1125_ = v_a_1036_;
v___y_1126_ = v_a_1037_;
v___y_1127_ = v_a_1038_;
goto v___jp_1123_;
}
else
{
lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1201_; 
lean_inc_ref(v_binderType_1149_);
lean_inc(v_pos_1122_);
lean_inc_ref(v_binderType_1118_);
lean_inc(v_binderName_1117_);
lean_inc(v_pos_1080_);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_before_1033_);
if (v_isSharedCheck_1201_ == 0)
{
lean_object* v_unused_1202_; lean_object* v_unused_1203_; 
v_unused_1202_ = lean_ctor_get(v_before_1033_, 1);
lean_dec(v_unused_1202_);
v_unused_1203_ = lean_ctor_get(v_before_1033_, 0);
lean_dec(v_unused_1203_);
v___x_1156_ = v_before_1033_;
v_isShared_1157_ = v_isSharedCheck_1201_;
goto v_resetjp_1155_;
}
else
{
lean_dec(v_before_1033_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1201_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1198_; 
v_isSharedCheck_1198_ = !lean_is_exclusive(v_after_1034_);
if (v_isSharedCheck_1198_ == 0)
{
lean_object* v_unused_1199_; lean_object* v_unused_1200_; 
v_unused_1199_ = lean_ctor_get(v_after_1034_, 1);
lean_dec(v_unused_1199_);
v_unused_1200_ = lean_ctor_get(v_after_1034_, 0);
lean_dec(v_unused_1200_);
v___x_1159_ = v_after_1034_;
v_isShared_1160_ = v_isSharedCheck_1198_;
goto v_resetjp_1158_;
}
else
{
lean_dec(v_after_1034_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1198_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v___x_1163_; 
v___x_1161_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1080_);
lean_inc_ref(v_binderType_1118_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 1, v___x_1161_);
lean_ctor_set(v___x_1159_, 0, v_binderType_1118_);
v___x_1163_ = v___x_1159_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_binderType_1118_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v___x_1161_);
v___x_1163_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1164_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1122_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 1, v___x_1164_);
lean_ctor_set(v___x_1156_, 0, v_binderType_1149_);
v___x_1166_ = v___x_1156_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_binderType_1149_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1167_; 
v___x_1167_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1163_, v___x_1166_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1195_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1170_ = v___x_1167_;
v_isShared_1171_ = v_isSharedCheck_1195_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1167_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1195_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
uint8_t v___x_1172_; 
v___x_1172_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_a_1168_);
if (v___x_1172_ == 0)
{
lean_object* v_changesBefore_1173_; lean_object* v_changesAfter_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; lean_object* v___x_1178_; lean_object* v_changesBefore_1179_; lean_object* v_changesAfter_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1192_; 
lean_dec_ref(v___f_1152_);
lean_dec_ref(v_binderType_1118_);
lean_dec(v_binderName_1117_);
v_changesBefore_1173_ = lean_ctor_get(v_a_1168_, 0);
lean_inc(v_changesBefore_1173_);
v_changesAfter_1174_ = lean_ctor_get(v_a_1168_, 1);
lean_inc(v_changesAfter_1174_);
lean_dec(v_a_1168_);
v___x_1175_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1080_);
lean_dec(v_pos_1080_);
v___x_1176_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1122_);
lean_dec(v_pos_1122_);
v___x_1177_ = 0;
v___x_1178_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v___x_1175_, v___x_1176_, v___x_1177_);
v_changesBefore_1179_ = lean_ctor_get(v___x_1178_, 0);
v_changesAfter_1180_ = lean_ctor_get(v___x_1178_, 1);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1182_ = v___x_1178_;
v_isShared_1183_ = v_isSharedCheck_1192_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_changesAfter_1180_);
lean_inc(v_changesBefore_1179_);
lean_dec(v___x_1178_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1192_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1184_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesBefore_1173_, v_changesBefore_1179_);
v___x_1185_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesAfter_1174_, v_changesAfter_1180_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 1, v___x_1185_);
lean_ctor_set(v___x_1182_, 0, v___x_1184_);
v___x_1187_ = v___x_1182_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1184_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1189_; 
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 0, v___x_1187_);
v___x_1189_ = v___x_1170_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
else
{
uint8_t v___x_1193_; lean_object* v___x_1194_; 
lean_del_object(v___x_1170_);
lean_dec(v_a_1168_);
lean_dec(v_pos_1122_);
lean_dec(v_pos_1080_);
v___x_1193_ = 0;
v___x_1194_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_binderName_1117_, v_binderInfo_1120_, v_binderType_1118_, v___f_1152_, v___x_1193_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
return v___x_1194_;
}
}
}
else
{
lean_dec_ref(v___f_1152_);
lean_dec(v_pos_1122_);
lean_dec_ref(v_binderType_1118_);
lean_dec(v_binderName_1117_);
lean_dec(v_pos_1080_);
return v___x_1167_;
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
v___y_1124_ = v_a_1035_;
v___y_1125_ = v_a_1036_;
v___y_1126_ = v_a_1037_;
v___y_1127_ = v_a_1038_;
goto v___jp_1123_;
}
v___jp_1123_:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1128_ = l_Lean_Expr_getForallBinderNames(v_expr_1121_);
v___x_1129_ = l_Lean_Expr_getForallBinderNames(v_expr_1079_);
v___x_1130_ = l_List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0(v___x_1128_, v___x_1129_);
if (lean_obj_tag(v___x_1130_) == 1)
{
lean_object* v_val_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
v_val_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_val_1131_);
lean_dec_ref_known(v___x_1130_, 1);
v___x_1132_ = l_List_lengthTR___redArg(v_val_1131_);
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = lean_nat_dec_eq(v___x_1132_, v___x_1133_);
lean_dec(v___x_1132_);
if (v___x_1134_ == 0)
{
v___y_1082_ = v_val_1131_;
v___y_1083_ = v___y_1124_;
v___y_1084_ = v___y_1125_;
v___y_1085_ = v___y_1126_;
v___y_1086_ = v___y_1127_;
goto v___jp_1081_;
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1, &l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1);
v___x_1136_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_1135_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_dec_ref_known(v___x_1136_, 1);
v___y_1082_ = v_val_1131_;
v___y_1083_ = v___y_1124_;
v___y_1084_ = v___y_1125_;
v___y_1085_ = v___y_1126_;
v___y_1086_ = v___y_1127_;
goto v___jp_1081_;
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec(v_val_1131_);
lean_dec_ref(v_after_1034_);
lean_dec_ref(v_before_1033_);
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1136_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1136_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
}
else
{
uint8_t v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
lean_dec(v___x_1130_);
v___x_1145_ = 0;
v___x_1146_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1033_, v_after_1034_, v___x_1145_);
v___x_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
return v___x_1147_;
}
}
}
else
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
lean_dec_ref(v_after_1034_);
lean_dec_ref(v_before_1033_);
v___x_1206_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___x_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
return v___x_1207_;
}
v___jp_1040_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = lean_unsigned_to_nat(0u);
v___x_1048_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v___y_1045_, v_before_1033_, v___x_1047_, v_a_1046_);
lean_dec(v___y_1045_);
return v___x_1048_;
}
v___jp_1049_:
{
if (v___y_1057_ == 0)
{
lean_object* v___x_1058_; 
lean_dec_ref(v___y_1054_);
v___x_1058_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1055_, v___y_1051_, v___y_1053_);
lean_dec_ref(v___y_1055_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v___x_1059_; 
lean_dec_ref_known(v___x_1058_, 1);
v___x_1059_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___y_1041_ = v___y_1050_;
v___y_1042_ = v___y_1051_;
v___y_1043_ = v___y_1052_;
v___y_1044_ = v___y_1053_;
v___y_1045_ = v___y_1056_;
v_a_1046_ = v___x_1059_;
goto v___jp_1040_;
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
lean_dec(v___y_1056_);
lean_dec_ref(v_before_1033_);
v_a_1060_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1058_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1058_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
else
{
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec_ref(v_before_1033_);
return v___y_1054_;
}
}
v___jp_1068_:
{
uint8_t v___x_1077_; 
v___x_1077_ = l_Lean_Exception_isInterrupt(v_a_1076_);
if (v___x_1077_ == 0)
{
uint8_t v___x_1078_; 
v___x_1078_ = l_Lean_Exception_isRuntime(v_a_1076_);
v___y_1050_ = v___y_1069_;
v___y_1051_ = v___y_1070_;
v___y_1052_ = v___y_1071_;
v___y_1053_ = v___y_1072_;
v___y_1054_ = v___y_1075_;
v___y_1055_ = v___y_1073_;
v___y_1056_ = v___y_1074_;
v___y_1057_ = v___x_1078_;
goto v___jp_1049_;
}
else
{
lean_dec_ref(v_a_1076_);
v___y_1050_ = v___y_1069_;
v___y_1051_ = v___y_1070_;
v___y_1052_ = v___y_1071_;
v___y_1053_ = v___y_1072_;
v___y_1054_ = v___y_1075_;
v___y_1055_ = v___y_1073_;
v___y_1056_ = v___y_1074_;
v___y_1057_ = v___x_1077_;
goto v___jp_1049_;
}
}
v___jp_1081_:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Lean_Meta_saveState___redArg(v___y_1084_, v___y_1086_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v___x_1087_, 1);
v___x_1089_ = l_List_lengthTR___redArg(v___y_1082_);
v___x_1090_ = lean_box(0);
v___x_1091_ = l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(v___y_1082_, v___x_1090_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v_body_u2080_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1092_);
lean_dec_ref_known(v___x_1091_, 1);
lean_inc_n(v___x_1089_, 2);
v_body_u2080_1093_ = l_Lean_Expr_getForallBodyMaxDepth(v___x_1089_, v_expr_1079_);
v___x_1094_ = lean_array_mk(v_a_1092_);
v___x_1095_ = lean_expr_instantiate_rev(v_body_u2080_1093_, v___x_1094_);
lean_dec_ref(v___x_1094_);
lean_dec_ref(v_body_u2080_1093_);
lean_inc(v_pos_1080_);
v___x_1096_ = l_Lean_SubExpr_Pos_pushNthBindingBody(v___x_1089_, v_pos_1080_);
v___x_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1095_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1097_, v_after_1034_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; 
lean_dec(v_a_1088_);
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_a_1099_);
lean_dec_ref_known(v___x_1098_, 1);
v___y_1041_ = v___y_1085_;
v___y_1042_ = v___y_1084_;
v___y_1043_ = v___y_1083_;
v___y_1044_ = v___y_1086_;
v___y_1045_ = v___x_1089_;
v_a_1046_ = v_a_1099_;
goto v___jp_1040_;
}
else
{
lean_object* v_a_1100_; 
v_a_1100_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_a_1100_);
v___y_1069_ = v___y_1085_;
v___y_1070_ = v___y_1084_;
v___y_1071_ = v___y_1083_;
v___y_1072_ = v___y_1086_;
v___y_1073_ = v_a_1088_;
v___y_1074_ = v___x_1089_;
v___y_1075_ = v___x_1098_;
v_a_1076_ = v_a_1100_;
goto v___jp_1068_;
}
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
lean_dec_ref(v_after_1034_);
v_a_1101_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1091_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1091_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
lean_inc(v_a_1101_);
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
v___y_1069_ = v___y_1085_;
v___y_1070_ = v___y_1084_;
v___y_1071_ = v___y_1083_;
v___y_1072_ = v___y_1086_;
v___y_1073_ = v_a_1088_;
v___y_1074_ = v___x_1089_;
v___y_1075_ = v___x_1106_;
v_a_1076_ = v_a_1101_;
goto v___jp_1068_;
}
}
}
}
else
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
lean_dec(v___y_1082_);
lean_dec_ref(v_after_1034_);
lean_dec_ref(v_before_1033_);
v_a_1109_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v___x_1087_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1087_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(lean_object* v_before_1208_, lean_object* v_after_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v_expr_1231_; lean_object* v_pos_1232_; lean_object* v_expr_1233_; lean_object* v_pos_1234_; lean_object* v_e_u2081_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; uint8_t v___x_1243_; 
v_expr_1231_ = lean_ctor_get(v_before_1208_, 0);
v_pos_1232_ = lean_ctor_get(v_before_1208_, 1);
v_expr_1233_ = lean_ctor_get(v_after_1209_, 0);
v_pos_1234_ = lean_ctor_get(v_after_1209_, 1);
v___x_1243_ = lean_expr_eqv(v_expr_1231_, v_expr_1233_);
if (v___x_1243_ == 0)
{
switch(lean_obj_tag(v_expr_1231_))
{
case 10:
{
lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1252_; 
lean_inc_ref(v_expr_1231_);
lean_inc(v_pos_1232_);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_before_1208_);
if (v_isSharedCheck_1252_ == 0)
{
lean_object* v_unused_1253_; lean_object* v_unused_1254_; 
v_unused_1253_ = lean_ctor_get(v_before_1208_, 1);
lean_dec(v_unused_1253_);
v_unused_1254_ = lean_ctor_get(v_before_1208_, 0);
lean_dec(v_unused_1254_);
v___x_1245_ = v_before_1208_;
v_isShared_1246_ = v_isSharedCheck_1252_;
goto v_resetjp_1244_;
}
else
{
lean_dec(v_before_1208_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1252_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v_expr_1247_; lean_object* v___x_1249_; 
v_expr_1247_ = lean_ctor_get(v_expr_1231_, 1);
lean_inc_ref(v_expr_1247_);
lean_dec_ref_known(v_expr_1231_, 2);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v_expr_1247_);
v___x_1249_ = v___x_1245_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_expr_1247_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_pos_1232_);
v___x_1249_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
v_before_1208_ = v___x_1249_;
goto _start;
}
}
}
case 5:
{
switch(lean_obj_tag(v_expr_1233_))
{
case 10:
{
lean_object* v_expr_1255_; 
lean_inc_ref(v_expr_1233_);
lean_inc(v_pos_1234_);
lean_dec_ref(v_after_1209_);
v_expr_1255_ = lean_ctor_get(v_expr_1233_, 1);
lean_inc_ref(v_expr_1255_);
lean_dec_ref_known(v_expr_1233_, 2);
v_e_u2081_1236_ = v_expr_1255_;
v___y_1237_ = v_a_1210_;
v___y_1238_ = v_a_1211_;
v___y_1239_ = v_a_1212_;
v___y_1240_ = v_a_1213_;
goto v___jp_1235_;
}
case 5:
{
lean_object* v_dummy_1256_; lean_object* v_nargs_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v_fst_1262_; lean_object* v_snd_1263_; lean_object* v_nargs_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v_fst_1268_; lean_object* v_snd_1269_; uint8_t v___x_1270_; 
v_dummy_1256_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0, &l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0);
v_nargs_1257_ = l_Lean_Expr_getAppNumArgs(v_expr_1233_);
lean_inc(v_nargs_1257_);
v___x_1258_ = lean_mk_array(v_nargs_1257_, v_dummy_1256_);
v___x_1259_ = lean_unsigned_to_nat(1u);
v___x_1260_ = lean_nat_sub(v_nargs_1257_, v___x_1259_);
lean_dec(v_nargs_1257_);
lean_inc_ref(v_expr_1233_);
v___x_1261_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(v_expr_1233_, v___x_1258_, v___x_1260_);
v_fst_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_fst_1262_);
v_snd_1263_ = lean_ctor_get(v___x_1261_, 1);
lean_inc(v_snd_1263_);
lean_dec_ref(v___x_1261_);
v_nargs_1264_ = l_Lean_Expr_getAppNumArgs(v_expr_1231_);
lean_inc(v_nargs_1264_);
v___x_1265_ = lean_mk_array(v_nargs_1264_, v_dummy_1256_);
v___x_1266_ = lean_nat_sub(v_nargs_1264_, v___x_1259_);
lean_dec(v_nargs_1264_);
lean_inc_ref(v_expr_1231_);
v___x_1267_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(v_expr_1231_, v___x_1265_, v___x_1266_);
v_fst_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_fst_1268_);
v_snd_1269_ = lean_ctor_get(v___x_1267_, 1);
lean_inc(v_snd_1269_);
lean_dec_ref(v___x_1267_);
v___x_1270_ = lean_expr_eqv(v_fst_1262_, v_fst_1268_);
lean_dec(v_fst_1268_);
lean_dec(v_fst_1262_);
if (v___x_1270_ == 0)
{
lean_dec(v_snd_1269_);
lean_dec(v_snd_1263_);
goto v___jp_1223_;
}
else
{
if (v___x_1243_ == 0)
{
lean_object* v___x_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; 
v___x_1271_ = lean_array_get_size(v_snd_1263_);
v___x_1272_ = lean_array_get_size(v_snd_1269_);
v___x_1273_ = lean_nat_dec_eq(v___x_1271_, v___x_1272_);
if (v___x_1273_ == 0)
{
lean_dec(v_snd_1269_);
lean_dec(v_snd_1263_);
goto v___jp_1223_;
}
else
{
lean_object* v_args_1274_; size_t v_sz_1275_; size_t v___x_1276_; lean_object* v___x_1277_; 
v_args_1274_ = l_Array_zip___redArg(v_snd_1263_, v_snd_1269_);
lean_dec(v_snd_1269_);
v_sz_1275_ = lean_array_size(v_args_1274_);
v___x_1276_ = ((size_t)0ULL);
v___x_1277_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_1263_, v_before_1208_, v_after_1209_, v_sz_1275_, v___x_1276_, v_args_1274_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
lean_dec_ref(v_after_1209_);
lean_dec_ref(v_before_1208_);
lean_dec(v_snd_1263_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1303_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1280_ = v___x_1277_;
v_isShared_1281_ = v_isSharedCheck_1303_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1277_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1303_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v___x_1282_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___x_1283_ = lean_unsigned_to_nat(0u);
v___x_1284_ = lean_array_get_size(v_a_1278_);
v___x_1285_ = lean_nat_dec_lt(v___x_1283_, v___x_1284_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1287_; 
lean_dec(v_a_1278_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 0, v___x_1282_);
v___x_1287_ = v___x_1280_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
else
{
uint8_t v___x_1289_; 
v___x_1289_ = lean_nat_dec_le(v___x_1284_, v___x_1284_);
if (v___x_1289_ == 0)
{
if (v___x_1285_ == 0)
{
lean_object* v___x_1291_; 
lean_dec(v_a_1278_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 0, v___x_1282_);
v___x_1291_ = v___x_1280_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1282_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
else
{
size_t v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1296_; 
v___x_1293_ = lean_usize_of_nat(v___x_1284_);
v___x_1294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_a_1278_, v___x_1276_, v___x_1293_, v___x_1282_);
lean_dec(v_a_1278_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 0, v___x_1294_);
v___x_1296_ = v___x_1280_;
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
else
{
size_t v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1301_; 
v___x_1298_ = lean_usize_of_nat(v___x_1284_);
v___x_1299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_a_1278_, v___x_1276_, v___x_1298_, v___x_1282_);
lean_dec(v_a_1278_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 0, v___x_1299_);
v___x_1301_ = v___x_1280_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
v_a_1304_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1277_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1277_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
else
{
lean_dec(v_snd_1269_);
lean_dec(v_snd_1263_);
goto v___jp_1223_;
}
}
}
default: 
{
goto v___jp_1227_;
}
}
}
case 7:
{
if (lean_obj_tag(v_expr_1233_) == 10)
{
lean_object* v_expr_1312_; 
lean_inc_ref(v_expr_1233_);
lean_inc(v_pos_1234_);
lean_dec_ref(v_after_1209_);
v_expr_1312_ = lean_ctor_get(v_expr_1233_, 1);
lean_inc_ref(v_expr_1312_);
lean_dec_ref_known(v_expr_1233_, 2);
v_e_u2081_1236_ = v_expr_1312_;
v___y_1237_ = v_a_1210_;
v___y_1238_ = v_a_1211_;
v___y_1239_ = v_a_1212_;
v___y_1240_ = v_a_1213_;
goto v___jp_1235_;
}
else
{
lean_object* v___x_1313_; 
v___x_1313_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(v_before_1208_, v_after_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
return v___x_1313_;
}
}
case 6:
{
switch(lean_obj_tag(v_expr_1233_))
{
case 10:
{
lean_object* v_expr_1314_; 
lean_inc_ref(v_expr_1233_);
lean_inc(v_pos_1234_);
lean_dec_ref(v_after_1209_);
v_expr_1314_ = lean_ctor_get(v_expr_1233_, 1);
lean_inc_ref(v_expr_1314_);
lean_dec_ref_known(v_expr_1233_, 2);
v_e_u2081_1236_ = v_expr_1314_;
v___y_1237_ = v_a_1210_;
v___y_1238_ = v_a_1211_;
v___y_1239_ = v_a_1212_;
v___y_1240_ = v_a_1213_;
goto v___jp_1235_;
}
case 6:
{
lean_object* v_binderName_1315_; lean_object* v_binderType_1316_; lean_object* v_body_1317_; uint8_t v_binderInfo_1318_; lean_object* v_binderName_1319_; lean_object* v_binderType_1320_; lean_object* v_body_1321_; uint8_t v_binderInfo_1322_; uint8_t v___x_1323_; 
v_binderName_1315_ = lean_ctor_get(v_expr_1231_, 0);
v_binderType_1316_ = lean_ctor_get(v_expr_1231_, 1);
v_body_1317_ = lean_ctor_get(v_expr_1231_, 2);
v_binderInfo_1318_ = lean_ctor_get_uint8(v_expr_1231_, sizeof(void*)*3 + 8);
v_binderName_1319_ = lean_ctor_get(v_expr_1233_, 0);
v_binderType_1320_ = lean_ctor_get(v_expr_1233_, 1);
v_body_1321_ = lean_ctor_get(v_expr_1233_, 2);
v_binderInfo_1322_ = lean_ctor_get_uint8(v_expr_1233_, sizeof(void*)*3 + 8);
v___x_1323_ = lean_name_eq(v_binderName_1315_, v_binderName_1319_);
if (v___x_1323_ == 0)
{
goto v___jp_1219_;
}
else
{
if (v___x_1243_ == 0)
{
uint8_t v___x_1324_; 
v___x_1324_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1318_, v_binderInfo_1322_);
if (v___x_1324_ == 0)
{
goto v___jp_1219_;
}
else
{
lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1374_; 
lean_inc_ref(v_body_1321_);
lean_inc_ref(v_binderType_1320_);
lean_inc_ref(v_body_1317_);
lean_inc_ref(v_binderType_1316_);
lean_inc(v_pos_1234_);
lean_inc(v_pos_1232_);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_before_1208_);
if (v_isSharedCheck_1374_ == 0)
{
lean_object* v_unused_1375_; lean_object* v_unused_1376_; 
v_unused_1375_ = lean_ctor_get(v_before_1208_, 1);
lean_dec(v_unused_1375_);
v_unused_1376_ = lean_ctor_get(v_before_1208_, 0);
lean_dec(v_unused_1376_);
v___x_1326_ = v_before_1208_;
v_isShared_1327_ = v_isSharedCheck_1374_;
goto v_resetjp_1325_;
}
else
{
lean_dec(v_before_1208_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1374_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1371_; 
v_isSharedCheck_1371_ = !lean_is_exclusive(v_after_1209_);
if (v_isSharedCheck_1371_ == 0)
{
lean_object* v_unused_1372_; lean_object* v_unused_1373_; 
v_unused_1372_ = lean_ctor_get(v_after_1209_, 1);
lean_dec(v_unused_1372_);
v_unused_1373_ = lean_ctor_get(v_after_1209_, 0);
lean_dec(v_unused_1373_);
v___x_1329_ = v_after_1209_;
v_isShared_1330_ = v_isSharedCheck_1371_;
goto v_resetjp_1328_;
}
else
{
lean_dec(v_after_1209_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1371_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1331_; lean_object* v___x_1333_; 
v___x_1331_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1232_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 1, v___x_1331_);
lean_ctor_set(v___x_1329_, 0, v_binderType_1316_);
v___x_1333_ = v___x_1329_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_binderType_1316_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1334_; lean_object* v___x_1336_; 
v___x_1334_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1234_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 1, v___x_1334_);
lean_ctor_set(v___x_1326_, 0, v_binderType_1320_);
v___x_1336_ = v___x_1326_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_binderType_1320_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1337_; 
v___x_1337_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1333_, v___x_1336_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1368_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1340_ = v___x_1337_;
v_isShared_1341_ = v_isSharedCheck_1368_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1337_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1368_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
uint8_t v___x_1342_; 
v___x_1342_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_a_1338_);
if (v___x_1342_ == 0)
{
lean_object* v_changesBefore_1343_; lean_object* v_changesAfter_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; lean_object* v___x_1348_; lean_object* v_changesBefore_1349_; lean_object* v_changesAfter_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1362_; 
lean_dec_ref(v_body_1321_);
lean_dec_ref(v_body_1317_);
v_changesBefore_1343_ = lean_ctor_get(v_a_1338_, 0);
lean_inc(v_changesBefore_1343_);
v_changesAfter_1344_ = lean_ctor_get(v_a_1338_, 1);
lean_inc(v_changesAfter_1344_);
lean_dec(v_a_1338_);
v___x_1345_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1232_);
lean_dec(v_pos_1232_);
v___x_1346_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1234_);
lean_dec(v_pos_1234_);
v___x_1347_ = 0;
v___x_1348_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v___x_1345_, v___x_1346_, v___x_1347_);
v_changesBefore_1349_ = lean_ctor_get(v___x_1348_, 0);
v_changesAfter_1350_ = lean_ctor_get(v___x_1348_, 1);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1352_ = v___x_1348_;
v_isShared_1353_ = v_isSharedCheck_1362_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_changesAfter_1350_);
lean_inc(v_changesBefore_1349_);
lean_dec(v___x_1348_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1362_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1354_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesBefore_1343_, v_changesBefore_1349_);
v___x_1355_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesAfter_1344_, v_changesAfter_1350_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 1, v___x_1355_);
lean_ctor_set(v___x_1352_, 0, v___x_1354_);
v___x_1357_ = v___x_1352_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1354_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1359_; 
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v___x_1357_);
v___x_1359_ = v___x_1340_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1357_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
else
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
lean_del_object(v___x_1340_);
lean_dec(v_a_1338_);
v___x_1363_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1232_);
lean_dec(v_pos_1232_);
v___x_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1364_, 0, v_body_1317_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
v___x_1365_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1234_);
lean_dec(v_pos_1234_);
v___x_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1366_, 0, v_body_1321_);
lean_ctor_set(v___x_1366_, 1, v___x_1365_);
v_before_1208_ = v___x_1364_;
v_after_1209_ = v___x_1366_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_body_1321_);
lean_dec_ref(v_body_1317_);
lean_dec(v_pos_1234_);
lean_dec(v_pos_1232_);
return v___x_1337_;
}
}
}
}
}
}
}
else
{
goto v___jp_1219_;
}
}
}
default: 
{
goto v___jp_1227_;
}
}
}
case 11:
{
switch(lean_obj_tag(v_expr_1233_))
{
case 10:
{
lean_object* v_expr_1377_; 
lean_inc_ref(v_expr_1233_);
lean_inc(v_pos_1234_);
lean_dec_ref(v_after_1209_);
v_expr_1377_ = lean_ctor_get(v_expr_1233_, 1);
lean_inc_ref(v_expr_1377_);
lean_dec_ref_known(v_expr_1233_, 2);
v_e_u2081_1236_ = v_expr_1377_;
v___y_1237_ = v_a_1210_;
v___y_1238_ = v_a_1211_;
v___y_1239_ = v_a_1212_;
v___y_1240_ = v_a_1213_;
goto v___jp_1235_;
}
case 11:
{
lean_object* v_typeName_1378_; lean_object* v_idx_1379_; lean_object* v_struct_1380_; lean_object* v_typeName_1381_; lean_object* v_idx_1382_; lean_object* v_struct_1383_; uint8_t v___x_1384_; 
v_typeName_1378_ = lean_ctor_get(v_expr_1231_, 0);
v_idx_1379_ = lean_ctor_get(v_expr_1231_, 1);
v_struct_1380_ = lean_ctor_get(v_expr_1231_, 2);
v_typeName_1381_ = lean_ctor_get(v_expr_1233_, 0);
v_idx_1382_ = lean_ctor_get(v_expr_1233_, 1);
v_struct_1383_ = lean_ctor_get(v_expr_1233_, 2);
v___x_1384_ = lean_name_eq(v_typeName_1378_, v_typeName_1381_);
if (v___x_1384_ == 0)
{
goto v___jp_1215_;
}
else
{
if (v___x_1243_ == 0)
{
uint8_t v___x_1385_; 
v___x_1385_ = lean_nat_dec_eq(v_idx_1379_, v_idx_1382_);
if (v___x_1385_ == 0)
{
goto v___jp_1215_;
}
else
{
lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1404_; 
lean_inc_ref(v_struct_1383_);
lean_inc_ref(v_struct_1380_);
lean_inc(v_pos_1234_);
lean_inc(v_pos_1232_);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_before_1208_);
if (v_isSharedCheck_1404_ == 0)
{
lean_object* v_unused_1405_; lean_object* v_unused_1406_; 
v_unused_1405_ = lean_ctor_get(v_before_1208_, 1);
lean_dec(v_unused_1405_);
v_unused_1406_ = lean_ctor_get(v_before_1208_, 0);
lean_dec(v_unused_1406_);
v___x_1387_ = v_before_1208_;
v_isShared_1388_ = v_isSharedCheck_1404_;
goto v_resetjp_1386_;
}
else
{
lean_dec(v_before_1208_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1404_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1401_; 
v_isSharedCheck_1401_ = !lean_is_exclusive(v_after_1209_);
if (v_isSharedCheck_1401_ == 0)
{
lean_object* v_unused_1402_; lean_object* v_unused_1403_; 
v_unused_1402_ = lean_ctor_get(v_after_1209_, 1);
lean_dec(v_unused_1402_);
v_unused_1403_ = lean_ctor_get(v_after_1209_, 0);
lean_dec(v_unused_1403_);
v___x_1390_ = v_after_1209_;
v_isShared_1391_ = v_isSharedCheck_1401_;
goto v_resetjp_1389_;
}
else
{
lean_dec(v_after_1209_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1401_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1392_; lean_object* v___x_1394_; 
v___x_1392_ = l_Lean_SubExpr_Pos_pushProj(v_pos_1232_);
lean_dec(v_pos_1232_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 1, v___x_1392_);
lean_ctor_set(v___x_1390_, 0, v_struct_1380_);
v___x_1394_ = v___x_1390_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_struct_1380_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v___x_1392_);
v___x_1394_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
lean_object* v___x_1395_; lean_object* v___x_1397_; 
v___x_1395_ = l_Lean_SubExpr_Pos_pushProj(v_pos_1234_);
lean_dec(v_pos_1234_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 1, v___x_1395_);
lean_ctor_set(v___x_1387_, 0, v_struct_1383_);
v___x_1397_ = v___x_1387_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_struct_1383_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v___x_1395_);
v___x_1397_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
v_before_1208_ = v___x_1394_;
v_after_1209_ = v___x_1397_;
goto _start;
}
}
}
}
}
}
else
{
goto v___jp_1215_;
}
}
}
default: 
{
goto v___jp_1227_;
}
}
}
default: 
{
if (lean_obj_tag(v_expr_1233_) == 10)
{
lean_object* v_expr_1407_; 
lean_inc_ref(v_expr_1233_);
lean_inc(v_pos_1234_);
lean_dec_ref(v_after_1209_);
v_expr_1407_ = lean_ctor_get(v_expr_1233_, 1);
lean_inc_ref(v_expr_1407_);
lean_dec_ref_known(v_expr_1233_, 2);
v_e_u2081_1236_ = v_expr_1407_;
v___y_1237_ = v_a_1210_;
v___y_1238_ = v_a_1211_;
v___y_1239_ = v_a_1212_;
v___y_1240_ = v_a_1213_;
goto v___jp_1235_;
}
else
{
goto v___jp_1227_;
}
}
}
}
else
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
lean_dec_ref(v_after_1209_);
lean_dec_ref(v_before_1208_);
v___x_1408_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___x_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1408_);
return v___x_1409_;
}
v___jp_1215_:
{
uint8_t v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1216_ = 0;
v___x_1217_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1208_, v_after_1209_, v___x_1216_);
v___x_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
return v___x_1218_;
}
v___jp_1219_:
{
uint8_t v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1220_ = 0;
v___x_1221_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1208_, v_after_1209_, v___x_1220_);
v___x_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
return v___x_1222_;
}
v___jp_1223_:
{
uint8_t v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1224_ = 0;
v___x_1225_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1208_, v_after_1209_, v___x_1224_);
v___x_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
return v___x_1226_;
}
v___jp_1227_:
{
uint8_t v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1228_ = 0;
v___x_1229_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1208_, v_after_1209_, v___x_1228_);
v___x_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
return v___x_1230_;
}
v___jp_1235_:
{
lean_object* v___x_1241_; 
v___x_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1241_, 0, v_e_u2081_1236_);
lean_ctor_set(v___x_1241_, 1, v_pos_1234_);
v_after_1209_ = v___x_1241_;
v_a_1210_ = v___y_1237_;
v_a_1211_ = v___y_1238_;
v_a_1212_ = v___y_1239_;
v_a_1213_ = v___y_1240_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0(lean_object* v_body_1410_, lean_object* v_pos_1411_, lean_object* v_body_1412_, lean_object* v_pos_1413_, lean_object* v_x_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1420_ = lean_expr_instantiate1(v_body_1410_, v_x_1414_);
v___x_1421_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1411_);
v___x_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1420_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
v___x_1423_ = lean_expr_instantiate1(v_body_1412_, v_x_1414_);
v___x_1424_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1413_);
v___x_1425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1423_);
lean_ctor_set(v___x_1425_, 1, v___x_1424_);
v___x_1426_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1422_, v___x_1425_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg___boxed(lean_object* v_snd_1427_, lean_object* v_before_1428_, lean_object* v_after_1429_, lean_object* v_sz_1430_, lean_object* v_i_1431_, lean_object* v_bs_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
size_t v_sz_boxed_1438_; size_t v_i_boxed_1439_; lean_object* v_res_1440_; 
v_sz_boxed_1438_ = lean_unbox_usize(v_sz_1430_);
lean_dec(v_sz_1430_);
v_i_boxed_1439_ = lean_unbox_usize(v_i_1431_);
lean_dec(v_i_1431_);
v_res_1440_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_1427_, v_before_1428_, v_after_1429_, v_sz_boxed_1438_, v_i_boxed_1439_, v_bs_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec_ref(v_after_1429_);
lean_dec_ref(v_before_1428_);
lean_dec_ref(v_snd_1427_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___boxed(lean_object* v_before_1441_, lean_object* v_after_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(v_before_1441_, v_after_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
lean_dec(v_a_1446_);
lean_dec_ref(v_a_1445_);
lean_dec(v_a_1444_);
lean_dec_ref(v_a_1443_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___boxed(lean_object* v_before_1449_, lean_object* v_after_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v_before_1449_, v_after_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_);
lean_dec(v_a_1454_);
lean_dec_ref(v_a_1453_);
lean_dec(v_a_1452_);
lean_dec_ref(v_a_1451_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1(lean_object* v_upperBound_1457_, lean_object* v_before_1458_, lean_object* v_inst_1459_, lean_object* v_R_1460_, lean_object* v_a_1461_, lean_object* v_b_1462_, lean_object* v_c_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v___x_1469_; 
v___x_1469_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v_upperBound_1457_, v_before_1458_, v_a_1461_, v_b_1462_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___boxed(lean_object* v_upperBound_1470_, lean_object* v_before_1471_, lean_object* v_inst_1472_, lean_object* v_R_1473_, lean_object* v_a_1474_, lean_object* v_b_1475_, lean_object* v_c_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1(v_upperBound_1470_, v_before_1471_, v_inst_1472_, v_R_1473_, v_a_1474_, v_b_1475_, v_c_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v_upperBound_1470_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3(lean_object* v_00_u03b1_1483_, lean_object* v_msg_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v_msg_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___boxed(lean_object* v_00_u03b1_1491_, lean_object* v_msg_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3(v_00_u03b1_1491_, v_msg_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4(uint8_t v_b_u2082_1499_, lean_object* v_k_1500_, lean_object* v_t_1501_, lean_object* v_hl_1502_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_1499_, v_k_1500_, v_t_1501_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___boxed(lean_object* v_b_u2082_1504_, lean_object* v_k_1505_, lean_object* v_t_1506_, lean_object* v_hl_1507_){
_start:
{
uint8_t v_b_u2082_boxed_1508_; lean_object* v_res_1509_; 
v_b_u2082_boxed_1508_ = lean_unbox(v_b_u2082_1504_);
v_res_1509_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4(v_b_u2082_boxed_1508_, v_k_1505_, v_t_1506_, v_hl_1507_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5(lean_object* v_init_1510_, lean_object* v_t_1511_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_init_1510_, v_t_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9(lean_object* v_snd_1513_, lean_object* v_before_1514_, lean_object* v_after_1515_, lean_object* v_as_1516_, size_t v_sz_1517_, size_t v_i_1518_, lean_object* v_bs_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_1513_, v_before_1514_, v_after_1515_, v_sz_1517_, v_i_1518_, v_bs_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___boxed(lean_object* v_snd_1526_, lean_object* v_before_1527_, lean_object* v_after_1528_, lean_object* v_as_1529_, lean_object* v_sz_1530_, lean_object* v_i_1531_, lean_object* v_bs_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
size_t v_sz_boxed_1538_; size_t v_i_boxed_1539_; lean_object* v_res_1540_; 
v_sz_boxed_1538_ = lean_unbox_usize(v_sz_1530_);
lean_dec(v_sz_1530_);
v_i_boxed_1539_ = lean_unbox_usize(v_i_1531_);
lean_dec(v_i_1531_);
v_res_1540_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9(v_snd_1526_, v_before_1527_, v_after_1528_, v_as_1529_, v_sz_boxed_1538_, v_i_boxed_1539_, v_bs_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec_ref(v_as_1529_);
lean_dec_ref(v_after_1528_);
lean_dec_ref(v_before_1527_);
lean_dec_ref(v_snd_1526_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(lean_object* v_e_u2080_1541_, lean_object* v_e_u2081_1542_, uint8_t v_useAfter_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_){
_start:
{
lean_object* v___x_1549_; lean_object* v_s_u2080_1550_; lean_object* v_s_u2081_1551_; 
v___x_1549_ = l_Lean_SubExpr_Pos_root;
v_s_u2080_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_u2080_1550_, 0, v_e_u2080_1541_);
lean_ctor_set(v_s_u2080_1550_, 1, v___x_1549_);
v_s_u2081_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_u2081_1551_, 0, v_e_u2081_1542_);
lean_ctor_set(v_s_u2081_1551_, 1, v___x_1549_);
if (v_useAfter_1543_ == 0)
{
lean_object* v___x_1552_; 
v___x_1552_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v_s_u2081_1551_, v_s_u2080_1550_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
return v___x_1552_;
}
else
{
lean_object* v___x_1553_; 
v___x_1553_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v_s_u2080_1550_, v_s_u2081_1551_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
return v___x_1553_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff___boxed(lean_object* v_e_u2080_1554_, lean_object* v_e_u2081_1555_, lean_object* v_useAfter_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_){
_start:
{
uint8_t v_useAfter_boxed_1562_; lean_object* v_res_1563_; 
v_useAfter_boxed_1562_ = lean_unbox(v_useAfter_1556_);
v_res_1563_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(v_e_u2080_1554_, v_e_u2081_1555_, v_useAfter_boxed_1562_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
lean_dec(v_a_1558_);
lean_dec_ref(v_a_1557_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0(uint8_t v_useAfter_1564_, lean_object* v_info_1565_, uint8_t v_d_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
uint8_t v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1572_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag(v_useAfter_1564_, v_d_1566_);
v___x_1573_ = l_Lean_Widget_SubexprInfo_withDiffTag(v___x_1572_, v_info_1565_);
v___x_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0___boxed(lean_object* v_useAfter_1575_, lean_object* v_info_1576_, lean_object* v_d_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
uint8_t v_useAfter_boxed_1583_; uint8_t v_d_boxed_1584_; lean_object* v_res_1585_; 
v_useAfter_boxed_1583_ = lean_unbox(v_useAfter_1575_);
v_d_boxed_1584_ = lean_unbox(v_d_1577_);
v_res_1585_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0(v_useAfter_boxed_1583_, v_info_1576_, v_d_boxed_1584_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(lean_object* v_f_1586_, lean_object* v_x_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
switch(lean_obj_tag(v_x_1587_))
{
case 0:
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1601_; 
lean_dec_ref(v_f_1586_);
v_a_1593_ = lean_ctor_get(v_x_1587_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v_x_1587_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1595_ = v_x_1587_;
v_isShared_1596_ = v_isSharedCheck_1601_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v_x_1587_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1601_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
return v___x_1599_;
}
}
}
case 1:
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1628_; 
v_a_1602_ = lean_ctor_get(v_x_1587_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_x_1587_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1604_ = v_x_1587_;
v_isShared_1605_ = v_isSharedCheck_1628_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v_x_1587_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1628_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
size_t v_sz_1606_; size_t v___x_1607_; lean_object* v___x_1608_; 
v_sz_1606_ = lean_array_size(v_a_1602_);
v___x_1607_ = ((size_t)0ULL);
v___x_1608_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_1586_, v_sz_1606_, v___x_1607_, v_a_1602_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1619_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1611_ = v___x_1608_;
v_isShared_1612_ = v_isSharedCheck_1619_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1608_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1619_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v_a_1609_);
v___x_1614_ = v___x_1604_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1609_);
v___x_1614_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
lean_object* v___x_1616_; 
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 0, v___x_1614_);
v___x_1616_ = v___x_1611_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1614_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_del_object(v___x_1604_);
v_a_1620_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1608_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1608_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
}
default: 
{
lean_object* v_a_1629_; lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1656_; 
v_a_1629_ = lean_ctor_get(v_x_1587_, 0);
v_a_1630_ = lean_ctor_get(v_x_1587_, 1);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_x_1587_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1632_ = v_x_1587_;
v_isShared_1633_ = v_isSharedCheck_1656_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_inc(v_a_1629_);
lean_dec(v_x_1587_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1656_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1634_; 
lean_inc_ref(v_f_1586_);
lean_inc(v___y_1591_);
lean_inc_ref(v___y_1590_);
lean_inc(v___y_1589_);
lean_inc_ref(v___y_1588_);
v___x_1634_ = lean_apply_6(v_f_1586_, v_a_1629_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, lean_box(0));
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1636_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_a_1635_);
lean_dec_ref_known(v___x_1634_, 1);
v___x_1636_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1586_, v_a_1630_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1647_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1639_ = v___x_1636_;
v_isShared_1640_ = v_isSharedCheck_1647_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1636_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1647_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 1, v_a_1637_);
lean_ctor_set(v___x_1632_, 0, v_a_1635_);
v___x_1642_ = v___x_1632_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1635_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
lean_object* v___x_1644_; 
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 0, v___x_1642_);
v___x_1644_ = v___x_1639_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
else
{
lean_dec(v_a_1635_);
lean_del_object(v___x_1632_);
return v___x_1636_;
}
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
lean_del_object(v___x_1632_);
lean_dec_ref(v_a_1630_);
lean_dec_ref(v_f_1586_);
v_a_1648_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1634_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1634_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(lean_object* v_f_1657_, size_t v_sz_1658_, size_t v_i_1659_, lean_object* v_bs_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
uint8_t v___x_1666_; 
v___x_1666_ = lean_usize_dec_lt(v_i_1659_, v_sz_1658_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1667_; 
lean_dec_ref(v_f_1657_);
v___x_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1667_, 0, v_bs_1660_);
return v___x_1667_;
}
else
{
lean_object* v_v_1668_; lean_object* v___x_1669_; 
v_v_1668_ = lean_array_uget_borrowed(v_bs_1660_, v_i_1659_);
lean_inc(v_v_1668_);
lean_inc_ref(v_f_1657_);
v___x_1669_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1657_, v_v_1668_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1671_; lean_object* v_bs_x27_1672_; size_t v___x_1673_; size_t v___x_1674_; lean_object* v___x_1675_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_a_1670_);
lean_dec_ref_known(v___x_1669_, 1);
v___x_1671_ = lean_unsigned_to_nat(0u);
v_bs_x27_1672_ = lean_array_uset(v_bs_1660_, v_i_1659_, v___x_1671_);
v___x_1673_ = ((size_t)1ULL);
v___x_1674_ = lean_usize_add(v_i_1659_, v___x_1673_);
v___x_1675_ = lean_array_uset(v_bs_x27_1672_, v_i_1659_, v_a_1670_);
v_i_1659_ = v___x_1674_;
v_bs_1660_ = v___x_1675_;
goto _start;
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
lean_dec_ref(v_bs_1660_);
lean_dec_ref(v_f_1657_);
v_a_1677_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v___x_1669_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1669_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1677_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_1685_, lean_object* v_sz_1686_, lean_object* v_i_1687_, lean_object* v_bs_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
size_t v_sz_boxed_1694_; size_t v_i_boxed_1695_; lean_object* v_res_1696_; 
v_sz_boxed_1694_ = lean_unbox_usize(v_sz_1686_);
lean_dec(v_sz_1686_);
v_i_boxed_1695_ = lean_unbox_usize(v_i_1687_);
lean_dec(v_i_1687_);
v_res_1696_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_1685_, v_sz_boxed_1694_, v_i_boxed_1695_, v_bs_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg___boxed(lean_object* v_f_1697_, lean_object* v_x_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1697_, v_x_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(lean_object* v_t_1705_, lean_object* v_k_1706_){
_start:
{
if (lean_obj_tag(v_t_1705_) == 0)
{
lean_object* v_k_1707_; lean_object* v_v_1708_; lean_object* v_l_1709_; lean_object* v_r_1710_; uint8_t v___x_1711_; 
v_k_1707_ = lean_ctor_get(v_t_1705_, 1);
v_v_1708_ = lean_ctor_get(v_t_1705_, 2);
v_l_1709_ = lean_ctor_get(v_t_1705_, 3);
v_r_1710_ = lean_ctor_get(v_t_1705_, 4);
v___x_1711_ = lean_nat_dec_lt(v_k_1706_, v_k_1707_);
if (v___x_1711_ == 0)
{
uint8_t v___x_1712_; 
v___x_1712_ = lean_nat_dec_eq(v_k_1706_, v_k_1707_);
if (v___x_1712_ == 0)
{
v_t_1705_ = v_r_1710_;
goto _start;
}
else
{
lean_object* v___x_1714_; 
lean_inc(v_v_1708_);
v___x_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1714_, 0, v_v_1708_);
return v___x_1714_;
}
}
else
{
v_t_1705_ = v_l_1709_;
goto _start;
}
}
else
{
lean_object* v___x_1716_; 
v___x_1716_ = lean_box(0);
return v___x_1716_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg___boxed(lean_object* v_t_1717_, lean_object* v_k_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_t_1717_, v_k_1718_);
lean_dec(v_k_1718_);
lean_dec(v_t_1717_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0(lean_object* v_pm_1720_, lean_object* v_merger_1721_, lean_object* v_info_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v_subexprPos_1728_; lean_object* v___x_1729_; 
v_subexprPos_1728_ = lean_ctor_get(v_info_1722_, 1);
v___x_1729_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_pm_1720_, v_subexprPos_1728_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v___x_1730_; 
lean_dec_ref(v_merger_1721_);
v___x_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1730_, 0, v_info_1722_);
return v___x_1730_;
}
else
{
lean_object* v_val_1731_; lean_object* v___x_1732_; 
v_val_1731_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_val_1731_);
lean_dec_ref_known(v___x_1729_, 1);
lean_inc(v___y_1726_);
lean_inc_ref(v___y_1725_);
lean_inc(v___y_1724_);
lean_inc_ref(v___y_1723_);
v___x_1732_ = lean_apply_7(v_merger_1721_, v_info_1722_, v_val_1731_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, lean_box(0));
return v___x_1732_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0___boxed(lean_object* v_pm_1733_, lean_object* v_merger_1734_, lean_object* v_info_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0(v_pm_1733_, v_merger_1734_, v_info_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v_pm_1733_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(lean_object* v_merger_1742_, lean_object* v_pm_1743_, lean_object* v_tt_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
if (lean_obj_tag(v_pm_1743_) == 0)
{
lean_object* v___f_1750_; lean_object* v___x_1751_; 
v___f_1750_ = lean_alloc_closure((void*)(l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1750_, 0, v_pm_1743_);
lean_closure_set(v___f_1750_, 1, v_merger_1742_);
v___x_1751_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v___f_1750_, v_tt_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
return v___x_1751_;
}
else
{
lean_object* v___x_1752_; 
lean_dec_ref(v_merger_1742_);
v___x_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1752_, 0, v_tt_1744_);
return v___x_1752_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___boxed(lean_object* v_merger_1753_, lean_object* v_pm_1754_, lean_object* v_tt_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v_merger_1753_, v_pm_1754_, v_tt_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(uint8_t v_useAfter_1762_, lean_object* v_diff_1763_, lean_object* v_info_u2081_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_){
_start:
{
lean_object* v___x_1770_; lean_object* v___f_1771_; 
v___x_1770_ = lean_box(v_useAfter_1762_);
v___f_1771_ = lean_alloc_closure((void*)(l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1771_, 0, v___x_1770_);
if (v_useAfter_1762_ == 0)
{
lean_object* v_changesBefore_1772_; lean_object* v___x_1773_; 
v_changesBefore_1772_ = lean_ctor_get(v_diff_1763_, 0);
lean_inc(v_changesBefore_1772_);
lean_dec_ref(v_diff_1763_);
v___x_1773_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v___f_1771_, v_changesBefore_1772_, v_info_u2081_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_);
return v___x_1773_;
}
else
{
lean_object* v_changesAfter_1774_; lean_object* v___x_1775_; 
v_changesAfter_1774_ = lean_ctor_get(v_diff_1763_, 1);
lean_inc(v_changesAfter_1774_);
lean_dec_ref(v_diff_1763_);
v___x_1775_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v___f_1771_, v_changesAfter_1774_, v_info_u2081_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_);
return v___x_1775_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___boxed(lean_object* v_useAfter_1776_, lean_object* v_diff_1777_, lean_object* v_info_u2081_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_){
_start:
{
uint8_t v_useAfter_boxed_1784_; lean_object* v_res_1785_; 
v_useAfter_boxed_1784_ = lean_unbox(v_useAfter_1776_);
v_res_1785_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(v_useAfter_boxed_1784_, v_diff_1777_, v_info_u2081_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_);
lean_dec(v_a_1782_);
lean_dec_ref(v_a_1781_);
lean_dec(v_a_1780_);
lean_dec_ref(v_a_1779_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0(lean_object* v_00_u03b1_1786_, lean_object* v_merger_1787_, lean_object* v_pm_1788_, lean_object* v_tt_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v_merger_1787_, v_pm_1788_, v_tt_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___boxed(lean_object* v_00_u03b1_1796_, lean_object* v_merger_1797_, lean_object* v_pm_1798_, lean_object* v_tt_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0(v_00_u03b1_1796_, v_merger_1797_, v_pm_1798_, v_tt_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0(lean_object* v_00_u03b4_1806_, lean_object* v_t_1807_, lean_object* v_k_1808_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_t_1807_, v_k_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___boxed(lean_object* v_00_u03b4_1810_, lean_object* v_t_1811_, lean_object* v_k_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0(v_00_u03b4_1810_, v_t_1811_, v_k_1812_);
lean_dec(v_k_1812_);
lean_dec(v_t_1811_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1(lean_object* v_00_u03b1_1814_, lean_object* v_00_u03b2_1815_, lean_object* v_f_1816_, lean_object* v_x_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1816_, v_x_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1824_, lean_object* v_00_u03b2_1825_, lean_object* v_f_1826_, lean_object* v_x_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1(v_00_u03b1_1824_, v_00_u03b2_1825_, v_f_1826_, v_x_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1834_, lean_object* v_00_u03b2_1835_, lean_object* v_f_1836_, size_t v_sz_1837_, size_t v_i_1838_, lean_object* v_bs_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_1836_, v_sz_1837_, v_i_1838_, v_bs_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1846_, lean_object* v_00_u03b2_1847_, lean_object* v_f_1848_, lean_object* v_sz_1849_, lean_object* v_i_1850_, lean_object* v_bs_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
size_t v_sz_boxed_1857_; size_t v_i_boxed_1858_; lean_object* v_res_1859_; 
v_sz_boxed_1857_ = lean_unbox_usize(v_sz_1849_);
lean_dec(v_sz_1849_);
v_i_boxed_1858_ = lean_unbox_usize(v_i_1850_);
lean_dec(v_i_1850_);
v_res_1859_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2(v_00_u03b1_1846_, v_00_u03b2_1847_, v_f_1848_, v_sz_boxed_1857_, v_i_boxed_1858_, v_bs_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(lean_object* v_e_1860_, lean_object* v___y_1861_){
_start:
{
uint8_t v___x_1863_; 
v___x_1863_ = l_Lean_Expr_hasMVar(v_e_1860_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; 
v___x_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1864_, 0, v_e_1860_);
return v___x_1864_;
}
else
{
lean_object* v___x_1865_; lean_object* v_mctx_1866_; lean_object* v___x_1867_; lean_object* v_fst_1868_; lean_object* v_snd_1869_; lean_object* v___x_1870_; lean_object* v_cache_1871_; lean_object* v_zetaDeltaFVarIds_1872_; lean_object* v_postponed_1873_; lean_object* v_diag_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1883_; 
v___x_1865_ = lean_st_ref_get(v___y_1861_);
v_mctx_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc_ref(v_mctx_1866_);
lean_dec(v___x_1865_);
v___x_1867_ = l_Lean_instantiateMVarsCore(v_mctx_1866_, v_e_1860_);
v_fst_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_fst_1868_);
v_snd_1869_ = lean_ctor_get(v___x_1867_, 1);
lean_inc(v_snd_1869_);
lean_dec_ref(v___x_1867_);
v___x_1870_ = lean_st_ref_take(v___y_1861_);
v_cache_1871_ = lean_ctor_get(v___x_1870_, 1);
v_zetaDeltaFVarIds_1872_ = lean_ctor_get(v___x_1870_, 2);
v_postponed_1873_ = lean_ctor_get(v___x_1870_, 3);
v_diag_1874_ = lean_ctor_get(v___x_1870_, 4);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1883_ == 0)
{
lean_object* v_unused_1884_; 
v_unused_1884_ = lean_ctor_get(v___x_1870_, 0);
lean_dec(v_unused_1884_);
v___x_1876_ = v___x_1870_;
v_isShared_1877_ = v_isSharedCheck_1883_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_diag_1874_);
lean_inc(v_postponed_1873_);
lean_inc(v_zetaDeltaFVarIds_1872_);
lean_inc(v_cache_1871_);
lean_dec(v___x_1870_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1883_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v_snd_1869_);
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_snd_1869_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v_cache_1871_);
lean_ctor_set(v_reuseFailAlloc_1882_, 2, v_zetaDeltaFVarIds_1872_);
lean_ctor_set(v_reuseFailAlloc_1882_, 3, v_postponed_1873_);
lean_ctor_set(v_reuseFailAlloc_1882_, 4, v_diag_1874_);
v___x_1879_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = lean_st_ref_set(v___y_1861_, v___x_1879_);
v___x_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1881_, 0, v_fst_1868_);
return v___x_1881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg___boxed(lean_object* v_e_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_e_1885_, v___y_1886_);
lean_dec(v___y_1886_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0(lean_object* v_e_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_e_1889_, v___y_1891_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___boxed(lean_object* v_e_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0(v_e_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
return v_res_1902_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1(void){
_start:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__0));
v___x_1905_ = l_Lean_stringToMessageData(v___x_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(uint8_t v_useAfter_1906_, lean_object* v_t_u2080_1907_, lean_object* v_h_u2081_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_){
_start:
{
lean_object* v_names_1914_; lean_object* v_fvarIds_1915_; lean_object* v_type_1916_; lean_object* v_val_x3f_1917_; lean_object* v_isInstance_x3f_1918_; lean_object* v_isType_x3f_1919_; lean_object* v_isInserted_x3f_1920_; lean_object* v_isRemoved_x3f_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1976_; 
v_names_1914_ = lean_ctor_get(v_h_u2081_1908_, 0);
v_fvarIds_1915_ = lean_ctor_get(v_h_u2081_1908_, 1);
v_type_1916_ = lean_ctor_get(v_h_u2081_1908_, 2);
v_val_x3f_1917_ = lean_ctor_get(v_h_u2081_1908_, 3);
v_isInstance_x3f_1918_ = lean_ctor_get(v_h_u2081_1908_, 4);
v_isType_x3f_1919_ = lean_ctor_get(v_h_u2081_1908_, 5);
v_isInserted_x3f_1920_ = lean_ctor_get(v_h_u2081_1908_, 6);
v_isRemoved_x3f_1921_ = lean_ctor_get(v_h_u2081_1908_, 7);
v_isSharedCheck_1976_ = !lean_is_exclusive(v_h_u2081_1908_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1923_ = v_h_u2081_1908_;
v_isShared_1924_ = v_isSharedCheck_1976_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_isRemoved_x3f_1921_);
lean_inc(v_isInserted_x3f_1920_);
lean_inc(v_isType_x3f_1919_);
lean_inc(v_isInstance_x3f_1918_);
lean_inc(v_val_x3f_1917_);
lean_inc(v_type_1916_);
lean_inc(v_fvarIds_1915_);
lean_inc(v_names_1914_);
lean_dec(v_h_u2081_1908_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1976_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___y_1926_; lean_object* v___x_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
v___x_1966_ = lean_unsigned_to_nat(0u);
v___x_1967_ = lean_array_get_size(v_fvarIds_1915_);
v___x_1968_ = lean_nat_dec_lt(v___x_1966_, v___x_1967_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
lean_del_object(v___x_1923_);
lean_dec(v_isRemoved_x3f_1921_);
lean_dec(v_isInserted_x3f_1920_);
lean_dec(v_isType_x3f_1919_);
lean_dec(v_isInstance_x3f_1918_);
lean_dec(v_val_x3f_1917_);
lean_dec_ref(v_type_1916_);
lean_dec_ref(v_fvarIds_1915_);
lean_dec_ref(v_names_1914_);
lean_dec_ref(v_t_u2080_1907_);
v___x_1969_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1);
v___x_1970_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_1969_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
return v___x_1970_;
}
else
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1971_ = lean_array_fget_borrowed(v_fvarIds_1915_, v___x_1966_);
lean_inc(v___x_1971_);
v___x_1972_ = l_Lean_Expr_fvar___override(v___x_1971_);
lean_inc(v_a_1912_);
lean_inc_ref(v_a_1911_);
lean_inc(v_a_1910_);
lean_inc_ref(v_a_1909_);
v___x_1973_ = lean_infer_type(v___x_1972_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1975_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc(v_a_1974_);
lean_dec_ref_known(v___x_1973_, 1);
v___x_1975_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_a_1974_, v_a_1910_);
v___y_1926_ = v___x_1975_;
goto v___jp_1925_;
}
else
{
v___y_1926_ = v___x_1973_;
goto v___jp_1925_;
}
}
v___jp_1925_:
{
if (lean_obj_tag(v___y_1926_) == 0)
{
lean_object* v_a_1927_; lean_object* v___x_1928_; 
v_a_1927_ = lean_ctor_get(v___y_1926_, 0);
lean_inc(v_a_1927_);
lean_dec_ref_known(v___y_1926_, 1);
v___x_1928_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(v_t_u2080_1907_, v_a_1927_, v_useAfter_1906_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1930_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref_known(v___x_1928_, 1);
v___x_1930_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(v_useAfter_1906_, v_a_1929_, v_type_1916_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1941_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1933_ = v___x_1930_;
v_isShared_1934_ = v_isSharedCheck_1941_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1930_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1941_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 2, v_a_1931_);
v___x_1936_ = v___x_1923_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_names_1914_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v_fvarIds_1915_);
lean_ctor_set(v_reuseFailAlloc_1940_, 2, v_a_1931_);
lean_ctor_set(v_reuseFailAlloc_1940_, 3, v_val_x3f_1917_);
lean_ctor_set(v_reuseFailAlloc_1940_, 4, v_isInstance_x3f_1918_);
lean_ctor_set(v_reuseFailAlloc_1940_, 5, v_isType_x3f_1919_);
lean_ctor_set(v_reuseFailAlloc_1940_, 6, v_isInserted_x3f_1920_);
lean_ctor_set(v_reuseFailAlloc_1940_, 7, v_isRemoved_x3f_1921_);
v___x_1936_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
lean_object* v___x_1938_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 0, v___x_1936_);
v___x_1938_ = v___x_1933_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1936_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
lean_del_object(v___x_1923_);
lean_dec(v_isRemoved_x3f_1921_);
lean_dec(v_isInserted_x3f_1920_);
lean_dec(v_isType_x3f_1919_);
lean_dec(v_isInstance_x3f_1918_);
lean_dec(v_val_x3f_1917_);
lean_dec_ref(v_fvarIds_1915_);
lean_dec_ref(v_names_1914_);
v_a_1942_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1930_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1930_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_del_object(v___x_1923_);
lean_dec(v_isRemoved_x3f_1921_);
lean_dec(v_isInserted_x3f_1920_);
lean_dec(v_isType_x3f_1919_);
lean_dec(v_isInstance_x3f_1918_);
lean_dec(v_val_x3f_1917_);
lean_dec_ref(v_type_1916_);
lean_dec_ref(v_fvarIds_1915_);
lean_dec_ref(v_names_1914_);
v_a_1950_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1928_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1928_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
lean_del_object(v___x_1923_);
lean_dec(v_isRemoved_x3f_1921_);
lean_dec(v_isInserted_x3f_1920_);
lean_dec(v_isType_x3f_1919_);
lean_dec(v_isInstance_x3f_1918_);
lean_dec(v_val_x3f_1917_);
lean_dec_ref(v_type_1916_);
lean_dec_ref(v_fvarIds_1915_);
lean_dec_ref(v_names_1914_);
lean_dec_ref(v_t_u2080_1907_);
v_a_1958_ = lean_ctor_get(v___y_1926_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___y_1926_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___y_1926_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___y_1926_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___boxed(lean_object* v_useAfter_1977_, lean_object* v_t_u2080_1978_, lean_object* v_h_u2081_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
uint8_t v_useAfter_boxed_1985_; lean_object* v_res_1986_; 
v_useAfter_boxed_1985_ = lean_unbox(v_useAfter_1977_);
v_res_1986_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(v_useAfter_boxed_1985_, v_t_u2080_1978_, v_h_u2081_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_);
lean_dec(v_a_1983_);
lean_dec_ref(v_a_1982_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(lean_object* v_ctx_u2080_1990_, uint8_t v_useAfter_1991_, lean_object* v_h_u2081_1992_, lean_object* v___x_1993_, lean_object* v___x_1994_, lean_object* v_as_1995_, size_t v_sz_1996_, size_t v_i_1997_, lean_object* v_b_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
uint8_t v___x_2004_; 
v___x_2004_ = lean_usize_dec_lt(v_i_1997_, v_sz_1996_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; 
lean_dec_ref(v___x_1994_);
lean_dec_ref(v___x_1993_);
lean_dec_ref(v_h_u2081_1992_);
v___x_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2005_, 0, v_b_1998_);
return v___x_2005_;
}
else
{
lean_object* v_a_2006_; lean_object* v_fst_2007_; lean_object* v_snd_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2104_; 
lean_dec_ref(v_b_1998_);
v_a_2006_ = lean_array_uget(v_as_1995_, v_i_1997_);
v_fst_2007_ = lean_ctor_get(v_a_2006_, 0);
v_snd_2008_ = lean_ctor_get(v_a_2006_, 1);
v_isSharedCheck_2104_ = !lean_is_exclusive(v_a_2006_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2010_ = v_a_2006_;
v_isShared_2011_ = v_isSharedCheck_2104_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_snd_2008_);
lean_inc(v_fst_2007_);
lean_dec(v_a_2006_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2104_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2012_; uint8_t v___x_2013_; 
v___x_2012_ = lean_box(0);
v___x_2013_ = l_Lean_LocalContext_contains(v_ctx_u2080_1990_, v_snd_2008_);
lean_dec(v_snd_2008_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2014_ = lean_box(0);
v___x_2015_ = l_Lean_Name_str___override(v___x_2014_, v_fst_2007_);
v___x_2016_ = l_Lean_LocalContext_findFromUserName_x3f(v_ctx_u2080_1990_, v___x_2015_);
lean_dec(v___x_2015_);
if (lean_obj_tag(v___x_2016_) == 1)
{
lean_object* v_val_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2055_; 
lean_dec_ref(v___x_1994_);
lean_dec_ref(v___x_1993_);
v_val_2017_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2019_ = v___x_2016_;
v_isShared_2020_ = v_isSharedCheck_2055_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_val_2017_);
lean_dec(v___x_2016_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2055_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2021_ = l_Lean_LocalDecl_type(v_val_2017_);
lean_dec(v_val_2017_);
v___x_2022_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v___x_2021_, v___y_2000_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v___x_2024_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2023_);
lean_dec_ref_known(v___x_2022_, 1);
v___x_2024_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(v_useAfter_1991_, v_a_2023_, v_h_u2081_1992_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2038_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2027_ = v___x_2024_;
v_isShared_2028_ = v_isSharedCheck_2038_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2024_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2038_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v_a_2025_);
v___x_2030_ = v___x_2019_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
lean_object* v___x_2032_; 
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 1, v___x_2012_);
lean_ctor_set(v___x_2010_, 0, v___x_2030_);
v___x_2032_ = v___x_2010_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2030_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v___x_2012_);
v___x_2032_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
lean_object* v___x_2034_; 
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 0, v___x_2032_);
v___x_2034_ = v___x_2027_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2032_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
lean_del_object(v___x_2019_);
lean_del_object(v___x_2010_);
v_a_2039_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_2024_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2024_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
lean_del_object(v___x_2019_);
lean_del_object(v___x_2010_);
lean_dec_ref(v_h_u2081_1992_);
v_a_2047_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_2022_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2022_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
}
else
{
lean_dec(v___x_2016_);
if (v_useAfter_1991_ == 0)
{
lean_object* v_type_2056_; lean_object* v_val_x3f_2057_; lean_object* v_isInstance_x3f_2058_; lean_object* v_isType_x3f_2059_; lean_object* v_isInserted_x3f_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2074_; 
v_type_2056_ = lean_ctor_get(v_h_u2081_1992_, 2);
v_val_x3f_2057_ = lean_ctor_get(v_h_u2081_1992_, 3);
v_isInstance_x3f_2058_ = lean_ctor_get(v_h_u2081_1992_, 4);
v_isType_x3f_2059_ = lean_ctor_get(v_h_u2081_1992_, 5);
v_isInserted_x3f_2060_ = lean_ctor_get(v_h_u2081_1992_, 6);
v_isSharedCheck_2074_ = !lean_is_exclusive(v_h_u2081_1992_);
if (v_isSharedCheck_2074_ == 0)
{
lean_object* v_unused_2075_; lean_object* v_unused_2076_; lean_object* v_unused_2077_; 
v_unused_2075_ = lean_ctor_get(v_h_u2081_1992_, 7);
lean_dec(v_unused_2075_);
v_unused_2076_ = lean_ctor_get(v_h_u2081_1992_, 1);
lean_dec(v_unused_2076_);
v_unused_2077_ = lean_ctor_get(v_h_u2081_1992_, 0);
lean_dec(v_unused_2077_);
v___x_2062_ = v_h_u2081_1992_;
v_isShared_2063_ = v_isSharedCheck_2074_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_isInserted_x3f_2060_);
lean_inc(v_isType_x3f_2059_);
lean_inc(v_isInstance_x3f_2058_);
lean_inc(v_val_x3f_2057_);
lean_inc(v_type_2056_);
lean_dec(v_h_u2081_1992_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2074_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2067_; 
v___x_2064_ = lean_box(v___x_2004_);
v___x_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2064_);
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 7, v___x_2065_);
lean_ctor_set(v___x_2062_, 1, v___x_1994_);
lean_ctor_set(v___x_2062_, 0, v___x_1993_);
v___x_2067_ = v___x_2062_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v___x_1994_);
lean_ctor_set(v_reuseFailAlloc_2073_, 2, v_type_2056_);
lean_ctor_set(v_reuseFailAlloc_2073_, 3, v_val_x3f_2057_);
lean_ctor_set(v_reuseFailAlloc_2073_, 4, v_isInstance_x3f_2058_);
lean_ctor_set(v_reuseFailAlloc_2073_, 5, v_isType_x3f_2059_);
lean_ctor_set(v_reuseFailAlloc_2073_, 6, v_isInserted_x3f_2060_);
lean_ctor_set(v_reuseFailAlloc_2073_, 7, v___x_2065_);
v___x_2067_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
lean_object* v___x_2068_; lean_object* v___x_2070_; 
v___x_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 1, v___x_2012_);
lean_ctor_set(v___x_2010_, 0, v___x_2068_);
v___x_2070_ = v___x_2010_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2068_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v___x_2012_);
v___x_2070_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
lean_object* v___x_2071_; 
v___x_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
return v___x_2071_;
}
}
}
}
else
{
lean_object* v_type_2078_; lean_object* v_val_x3f_2079_; lean_object* v_isInstance_x3f_2080_; lean_object* v_isType_x3f_2081_; lean_object* v_isRemoved_x3f_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2096_; 
v_type_2078_ = lean_ctor_get(v_h_u2081_1992_, 2);
v_val_x3f_2079_ = lean_ctor_get(v_h_u2081_1992_, 3);
v_isInstance_x3f_2080_ = lean_ctor_get(v_h_u2081_1992_, 4);
v_isType_x3f_2081_ = lean_ctor_get(v_h_u2081_1992_, 5);
v_isRemoved_x3f_2082_ = lean_ctor_get(v_h_u2081_1992_, 7);
v_isSharedCheck_2096_ = !lean_is_exclusive(v_h_u2081_1992_);
if (v_isSharedCheck_2096_ == 0)
{
lean_object* v_unused_2097_; lean_object* v_unused_2098_; lean_object* v_unused_2099_; 
v_unused_2097_ = lean_ctor_get(v_h_u2081_1992_, 6);
lean_dec(v_unused_2097_);
v_unused_2098_ = lean_ctor_get(v_h_u2081_1992_, 1);
lean_dec(v_unused_2098_);
v_unused_2099_ = lean_ctor_get(v_h_u2081_1992_, 0);
lean_dec(v_unused_2099_);
v___x_2084_ = v_h_u2081_1992_;
v_isShared_2085_ = v_isSharedCheck_2096_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_isRemoved_x3f_2082_);
lean_inc(v_isType_x3f_2081_);
lean_inc(v_isInstance_x3f_2080_);
lean_inc(v_val_x3f_2079_);
lean_inc(v_type_2078_);
lean_dec(v_h_u2081_1992_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2096_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2089_; 
v___x_2086_ = lean_box(v___x_2004_);
v___x_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 6, v___x_2087_);
lean_ctor_set(v___x_2084_, 1, v___x_1994_);
lean_ctor_set(v___x_2084_, 0, v___x_1993_);
v___x_2089_ = v___x_2084_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v___x_1994_);
lean_ctor_set(v_reuseFailAlloc_2095_, 2, v_type_2078_);
lean_ctor_set(v_reuseFailAlloc_2095_, 3, v_val_x3f_2079_);
lean_ctor_set(v_reuseFailAlloc_2095_, 4, v_isInstance_x3f_2080_);
lean_ctor_set(v_reuseFailAlloc_2095_, 5, v_isType_x3f_2081_);
lean_ctor_set(v_reuseFailAlloc_2095_, 6, v___x_2087_);
lean_ctor_set(v_reuseFailAlloc_2095_, 7, v_isRemoved_x3f_2082_);
v___x_2089_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
lean_object* v___x_2090_; lean_object* v___x_2092_; 
v___x_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 1, v___x_2012_);
lean_ctor_set(v___x_2010_, 0, v___x_2090_);
v___x_2092_ = v___x_2010_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2090_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v___x_2012_);
v___x_2092_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
lean_object* v___x_2093_; 
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
return v___x_2093_;
}
}
}
}
}
}
else
{
lean_object* v___x_2100_; size_t v___x_2101_; size_t v___x_2102_; 
lean_del_object(v___x_2010_);
lean_dec(v_fst_2007_);
v___x_2100_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___closed__0));
v___x_2101_ = ((size_t)1ULL);
v___x_2102_ = lean_usize_add(v_i_1997_, v___x_2101_);
v_i_1997_ = v___x_2102_;
v_b_1998_ = v___x_2100_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___boxed(lean_object* v_ctx_u2080_2105_, lean_object* v_useAfter_2106_, lean_object* v_h_u2081_2107_, lean_object* v___x_2108_, lean_object* v___x_2109_, lean_object* v_as_2110_, lean_object* v_sz_2111_, lean_object* v_i_2112_, lean_object* v_b_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
uint8_t v_useAfter_boxed_2119_; size_t v_sz_boxed_2120_; size_t v_i_boxed_2121_; lean_object* v_res_2122_; 
v_useAfter_boxed_2119_ = lean_unbox(v_useAfter_2106_);
v_sz_boxed_2120_ = lean_unbox_usize(v_sz_2111_);
lean_dec(v_sz_2111_);
v_i_boxed_2121_ = lean_unbox_usize(v_i_2112_);
lean_dec(v_i_2112_);
v_res_2122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(v_ctx_u2080_2105_, v_useAfter_boxed_2119_, v_h_u2081_2107_, v___x_2108_, v___x_2109_, v_as_2110_, v_sz_boxed_2120_, v_i_boxed_2121_, v_b_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec_ref(v_as_2110_);
lean_dec_ref(v_ctx_u2080_2105_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(uint8_t v_useAfter_2123_, lean_object* v_ctx_u2080_2124_, lean_object* v_h_u2081_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_){
_start:
{
lean_object* v_names_2131_; lean_object* v_fvarIds_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; size_t v_sz_2135_; size_t v___x_2136_; lean_object* v___x_2137_; 
v_names_2131_ = lean_ctor_get(v_h_u2081_2125_, 0);
v_fvarIds_2132_ = lean_ctor_get(v_h_u2081_2125_, 1);
v___x_2133_ = l_Array_zip___redArg(v_names_2131_, v_fvarIds_2132_);
v___x_2134_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___closed__0));
v_sz_2135_ = lean_array_size(v___x_2133_);
v___x_2136_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_2132_);
lean_inc_ref(v_names_2131_);
lean_inc_ref(v_h_u2081_2125_);
v___x_2137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(v_ctx_u2080_2124_, v_useAfter_2123_, v_h_u2081_2125_, v_names_2131_, v_fvarIds_2132_, v___x_2133_, v_sz_2135_, v___x_2136_, v___x_2134_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_);
lean_dec_ref(v___x_2133_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2150_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2140_ = v___x_2137_;
v_isShared_2141_ = v_isSharedCheck_2150_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2137_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2150_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v_fst_2142_; 
v_fst_2142_ = lean_ctor_get(v_a_2138_, 0);
lean_inc(v_fst_2142_);
lean_dec(v_a_2138_);
if (lean_obj_tag(v_fst_2142_) == 0)
{
lean_object* v___x_2144_; 
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v_h_u2081_2125_);
v___x_2144_ = v___x_2140_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_h_u2081_2125_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
else
{
lean_object* v_val_2146_; lean_object* v___x_2148_; 
lean_dec_ref(v_h_u2081_2125_);
v_val_2146_ = lean_ctor_get(v_fst_2142_, 0);
lean_inc(v_val_2146_);
lean_dec_ref_known(v_fst_2142_, 1);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v_val_2146_);
v___x_2148_ = v___x_2140_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_val_2146_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_dec_ref(v_h_u2081_2125_);
v_a_2151_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2137_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2137_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle___boxed(lean_object* v_useAfter_2159_, lean_object* v_ctx_u2080_2160_, lean_object* v_h_u2081_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_){
_start:
{
uint8_t v_useAfter_boxed_2167_; lean_object* v_res_2168_; 
v_useAfter_boxed_2167_ = lean_unbox(v_useAfter_2159_);
v_res_2168_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(v_useAfter_boxed_2167_, v_ctx_u2080_2160_, v_h_u2081_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
lean_dec(v_a_2165_);
lean_dec_ref(v_a_2164_);
lean_dec(v_a_2163_);
lean_dec_ref(v_a_2162_);
lean_dec_ref(v_ctx_u2080_2160_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(uint8_t v_useAfter_2169_, lean_object* v_lctx_u2080_2170_, size_t v_sz_2171_, size_t v_i_2172_, lean_object* v_bs_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
uint8_t v___x_2179_; 
v___x_2179_ = lean_usize_dec_lt(v_i_2172_, v_sz_2171_);
if (v___x_2179_ == 0)
{
lean_object* v___x_2180_; 
v___x_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2180_, 0, v_bs_2173_);
return v___x_2180_;
}
else
{
lean_object* v_v_2181_; lean_object* v___x_2182_; 
v_v_2181_ = lean_array_uget_borrowed(v_bs_2173_, v_i_2172_);
lean_inc(v_v_2181_);
v___x_2182_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(v_useAfter_2169_, v_lctx_u2080_2170_, v_v_2181_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; lean_object* v___x_2184_; lean_object* v_bs_x27_2185_; size_t v___x_2186_; size_t v___x_2187_; lean_object* v___x_2188_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_a_2183_);
lean_dec_ref_known(v___x_2182_, 1);
v___x_2184_ = lean_unsigned_to_nat(0u);
v_bs_x27_2185_ = lean_array_uset(v_bs_2173_, v_i_2172_, v___x_2184_);
v___x_2186_ = ((size_t)1ULL);
v___x_2187_ = lean_usize_add(v_i_2172_, v___x_2186_);
v___x_2188_ = lean_array_uset(v_bs_x27_2185_, v_i_2172_, v_a_2183_);
v_i_2172_ = v___x_2187_;
v_bs_2173_ = v___x_2188_;
goto _start;
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec_ref(v_bs_2173_);
v_a_2190_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2182_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2182_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0___boxed(lean_object* v_useAfter_2198_, lean_object* v_lctx_u2080_2199_, lean_object* v_sz_2200_, lean_object* v_i_2201_, lean_object* v_bs_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
uint8_t v_useAfter_boxed_2208_; size_t v_sz_boxed_2209_; size_t v_i_boxed_2210_; lean_object* v_res_2211_; 
v_useAfter_boxed_2208_ = lean_unbox(v_useAfter_2198_);
v_sz_boxed_2209_ = lean_unbox_usize(v_sz_2200_);
lean_dec(v_sz_2200_);
v_i_boxed_2210_ = lean_unbox_usize(v_i_2201_);
lean_dec(v_i_2201_);
v_res_2211_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(v_useAfter_boxed_2208_, v_lctx_u2080_2199_, v_sz_boxed_2209_, v_i_boxed_2210_, v_bs_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec_ref(v_lctx_u2080_2199_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(uint8_t v_useAfter_2212_, lean_object* v_lctx_u2080_2213_, lean_object* v_hs_u2081_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_){
_start:
{
size_t v_sz_2220_; size_t v___x_2221_; lean_object* v___x_2222_; 
v_sz_2220_ = lean_array_size(v_hs_u2081_2214_);
v___x_2221_ = ((size_t)0ULL);
v___x_2222_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(v_useAfter_2212_, v_lctx_u2080_2213_, v_sz_2220_, v___x_2221_, v_hs_u2081_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses___boxed(lean_object* v_useAfter_2223_, lean_object* v_lctx_u2080_2224_, lean_object* v_hs_u2081_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
uint8_t v_useAfter_boxed_2231_; lean_object* v_res_2232_; 
v_useAfter_boxed_2231_ = lean_unbox(v_useAfter_2223_);
v_res_2232_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(v_useAfter_boxed_2231_, v_lctx_u2080_2224_, v_hs_u2081_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
lean_dec_ref(v_lctx_u2080_2224_);
return v_res_2232_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2(void){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__1));
v___x_2238_ = l_Lean_stringToMessageData(v___x_2237_);
return v___x_2238_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4(void){
_start:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2240_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__3));
v___x_2241_ = l_Lean_stringToMessageData(v___x_2240_);
return v___x_2241_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6(void){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2243_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__5));
v___x_2244_ = l_Lean_stringToMessageData(v___x_2243_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(uint8_t v_useAfter_2245_, lean_object* v_g_u2080_2246_, lean_object* v_i_u2081_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_){
_start:
{
lean_object* v___x_2253_; lean_object* v_mctx_2254_; lean_object* v___x_2255_; 
v___x_2253_ = lean_st_ref_get(v_a_2249_);
v_mctx_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc_ref(v_mctx_2254_);
lean_dec(v___x_2253_);
v___x_2255_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2254_, v_g_u2080_2246_);
lean_dec_ref(v_mctx_2254_);
if (lean_obj_tag(v___x_2255_) == 1)
{
lean_object* v_val_2256_; lean_object* v_options_2257_; lean_object* v_lctx_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v_toInteractiveGoalCore_2262_; lean_object* v_fst_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2360_; 
v_val_2256_ = lean_ctor_get(v___x_2255_, 0);
lean_inc(v_val_2256_);
lean_dec_ref_known(v___x_2255_, 1);
v_options_2257_ = lean_ctor_get(v_a_2250_, 2);
v_lctx_2258_ = lean_ctor_get(v_val_2256_, 1);
lean_inc_ref(v_lctx_2258_);
lean_dec(v_val_2256_);
v___x_2259_ = lean_box(1);
lean_inc_ref(v_options_2257_);
v___x_2260_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2260_, 0, v_options_2257_);
lean_ctor_set(v___x_2260_, 1, v___x_2259_);
lean_ctor_set(v___x_2260_, 2, v___x_2259_);
v___x_2261_ = l_Lean_LocalContext_sanitizeNames(v_lctx_2258_, v___x_2260_);
v_toInteractiveGoalCore_2262_ = lean_ctor_get(v_i_u2081_2247_, 0);
lean_inc_ref(v_toInteractiveGoalCore_2262_);
v_fst_2263_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2360_ == 0)
{
lean_object* v_unused_2361_; 
v_unused_2361_ = lean_ctor_get(v___x_2261_, 1);
lean_dec(v_unused_2361_);
v___x_2265_ = v___x_2261_;
v_isShared_2266_ = v_isSharedCheck_2360_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_fst_2263_);
lean_dec(v___x_2261_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2360_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v_userName_x3f_2267_; lean_object* v_goalPrefix_2268_; lean_object* v_mvarId_2269_; lean_object* v_isRemoved_x3f_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2357_; 
v_userName_x3f_2267_ = lean_ctor_get(v_i_u2081_2247_, 1);
v_goalPrefix_2268_ = lean_ctor_get(v_i_u2081_2247_, 2);
v_mvarId_2269_ = lean_ctor_get(v_i_u2081_2247_, 3);
v_isRemoved_x3f_2270_ = lean_ctor_get(v_i_u2081_2247_, 5);
v_isSharedCheck_2357_ = !lean_is_exclusive(v_i_u2081_2247_);
if (v_isSharedCheck_2357_ == 0)
{
lean_object* v_unused_2358_; lean_object* v_unused_2359_; 
v_unused_2358_ = lean_ctor_get(v_i_u2081_2247_, 4);
lean_dec(v_unused_2358_);
v_unused_2359_ = lean_ctor_get(v_i_u2081_2247_, 0);
lean_dec(v_unused_2359_);
v___x_2272_ = v_i_u2081_2247_;
v_isShared_2273_ = v_isSharedCheck_2357_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_isRemoved_x3f_2270_);
lean_inc(v_mvarId_2269_);
lean_inc(v_goalPrefix_2268_);
lean_inc(v_userName_x3f_2267_);
lean_dec(v_i_u2081_2247_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2357_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v_hyps_2274_; lean_object* v_type_2275_; lean_object* v_ctx_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2356_; 
v_hyps_2274_ = lean_ctor_get(v_toInteractiveGoalCore_2262_, 0);
v_type_2275_ = lean_ctor_get(v_toInteractiveGoalCore_2262_, 1);
v_ctx_2276_ = lean_ctor_get(v_toInteractiveGoalCore_2262_, 2);
v_isSharedCheck_2356_ = !lean_is_exclusive(v_toInteractiveGoalCore_2262_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2278_ = v_toInteractiveGoalCore_2262_;
v_isShared_2279_ = v_isSharedCheck_2356_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_ctx_2276_);
lean_inc(v_type_2275_);
lean_inc(v_hyps_2274_);
lean_dec(v_toInteractiveGoalCore_2262_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2356_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2280_; 
v___x_2280_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(v_useAfter_2245_, v_fst_2263_, v_hyps_2274_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_);
lean_dec(v_fst_2263_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_a_2281_);
lean_dec_ref_known(v___x_2280_, 1);
v___x_2282_ = l_Lean_Expr_mvar___override(v_g_u2080_2246_);
lean_inc(v_a_2251_);
lean_inc_ref(v_a_2250_);
lean_inc(v_a_2249_);
lean_inc_ref(v_a_2248_);
v___x_2283_ = lean_infer_type(v___x_2282_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; lean_object* v___x_2285_; lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2339_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc(v_a_2284_);
lean_dec_ref_known(v___x_2283_, 1);
v___x_2285_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_a_2284_, v_a_2249_);
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2288_ = v___x_2285_;
v_isShared_2289_ = v_isSharedCheck_2339_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2285_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2339_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2290_; lean_object* v_mctx_2291_; lean_object* v___x_2292_; 
v___x_2290_ = lean_st_ref_get(v_a_2249_);
v_mctx_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc_ref(v_mctx_2291_);
lean_dec(v___x_2290_);
v___x_2292_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2291_, v_mvarId_2269_);
lean_dec_ref(v_mctx_2291_);
if (lean_obj_tag(v___x_2292_) == 1)
{
lean_object* v_val_2293_; lean_object* v_type_2294_; lean_object* v___x_2295_; lean_object* v_a_2296_; lean_object* v___x_2297_; 
lean_del_object(v___x_2288_);
lean_del_object(v___x_2265_);
v_val_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_val_2293_);
lean_dec_ref_known(v___x_2292_, 1);
v_type_2294_ = lean_ctor_get(v_val_2293_, 2);
lean_inc_ref(v_type_2294_);
lean_dec(v_val_2293_);
v___x_2295_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_type_2294_, v_a_2249_);
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_a_2296_);
lean_dec_ref(v___x_2295_);
v___x_2297_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(v_a_2286_, v_a_2296_, v_useAfter_2245_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; lean_object* v___x_2299_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_a_2298_);
lean_dec_ref_known(v___x_2297_, 1);
v___x_2299_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(v_useAfter_2245_, v_a_2298_, v_type_2275_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2314_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2302_ = v___x_2299_;
v_isShared_2303_ = v_isSharedCheck_2314_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2299_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2314_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2279_ == 0)
{
lean_ctor_set(v___x_2278_, 1, v_a_2300_);
lean_ctor_set(v___x_2278_, 0, v_a_2281_);
v___x_2305_ = v___x_2278_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2281_);
lean_ctor_set(v_reuseFailAlloc_2313_, 1, v_a_2300_);
lean_ctor_set(v_reuseFailAlloc_2313_, 2, v_ctx_2276_);
v___x_2305_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
lean_object* v___x_2306_; lean_object* v___x_2308_; 
v___x_2306_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__0));
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 4, v___x_2306_);
lean_ctor_set(v___x_2272_, 0, v___x_2305_);
v___x_2308_ = v___x_2272_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v___x_2305_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v_userName_x3f_2267_);
lean_ctor_set(v_reuseFailAlloc_2312_, 2, v_goalPrefix_2268_);
lean_ctor_set(v_reuseFailAlloc_2312_, 3, v_mvarId_2269_);
lean_ctor_set(v_reuseFailAlloc_2312_, 4, v___x_2306_);
lean_ctor_set(v_reuseFailAlloc_2312_, 5, v_isRemoved_x3f_2270_);
v___x_2308_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
lean_object* v___x_2310_; 
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 0, v___x_2308_);
v___x_2310_ = v___x_2302_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2308_);
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
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_dec(v_a_2281_);
lean_del_object(v___x_2278_);
lean_dec_ref(v_ctx_2276_);
lean_del_object(v___x_2272_);
lean_dec(v_isRemoved_x3f_2270_);
lean_dec(v_mvarId_2269_);
lean_dec_ref(v_goalPrefix_2268_);
lean_dec(v_userName_x3f_2267_);
v_a_2315_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2299_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2299_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
else
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
lean_dec(v_a_2281_);
lean_del_object(v___x_2278_);
lean_dec_ref(v_ctx_2276_);
lean_dec_ref(v_type_2275_);
lean_del_object(v___x_2272_);
lean_dec(v_isRemoved_x3f_2270_);
lean_dec(v_mvarId_2269_);
lean_dec_ref(v_goalPrefix_2268_);
lean_dec(v_userName_x3f_2267_);
v_a_2323_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2325_ = v___x_2297_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2297_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
}
else
{
lean_object* v___x_2331_; lean_object* v___x_2333_; 
lean_dec(v___x_2292_);
lean_dec(v_a_2286_);
lean_dec(v_a_2281_);
lean_del_object(v___x_2278_);
lean_dec_ref(v_ctx_2276_);
lean_dec_ref(v_type_2275_);
lean_del_object(v___x_2272_);
lean_dec(v_isRemoved_x3f_2270_);
lean_dec_ref(v_goalPrefix_2268_);
lean_dec(v_userName_x3f_2267_);
v___x_2331_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2);
if (v_isShared_2289_ == 0)
{
lean_ctor_set_tag(v___x_2288_, 1);
lean_ctor_set(v___x_2288_, 0, v_mvarId_2269_);
v___x_2333_ = v___x_2288_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_mvarId_2269_);
v___x_2333_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v___x_2335_; 
if (v_isShared_2266_ == 0)
{
lean_ctor_set_tag(v___x_2265_, 7);
lean_ctor_set(v___x_2265_, 1, v___x_2333_);
lean_ctor_set(v___x_2265_, 0, v___x_2331_);
v___x_2335_ = v___x_2265_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v___x_2331_);
lean_ctor_set(v_reuseFailAlloc_2337_, 1, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
lean_object* v___x_2336_; 
v___x_2336_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_2335_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_);
return v___x_2336_;
}
}
}
}
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_dec(v_a_2281_);
lean_del_object(v___x_2278_);
lean_dec_ref(v_ctx_2276_);
lean_dec_ref(v_type_2275_);
lean_del_object(v___x_2272_);
lean_dec(v_isRemoved_x3f_2270_);
lean_dec(v_mvarId_2269_);
lean_dec_ref(v_goalPrefix_2268_);
lean_dec(v_userName_x3f_2267_);
lean_del_object(v___x_2265_);
v_a_2340_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2283_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2283_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
else
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2355_; 
lean_del_object(v___x_2278_);
lean_dec_ref(v_ctx_2276_);
lean_dec_ref(v_type_2275_);
lean_del_object(v___x_2272_);
lean_dec(v_isRemoved_x3f_2270_);
lean_dec(v_mvarId_2269_);
lean_dec_ref(v_goalPrefix_2268_);
lean_dec(v_userName_x3f_2267_);
lean_del_object(v___x_2265_);
lean_dec(v_g_u2080_2246_);
v_a_2348_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2350_ = v___x_2280_;
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2280_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2353_; 
if (v_isShared_2351_ == 0)
{
v___x_2353_ = v___x_2350_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_a_2348_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
lean_dec(v___x_2255_);
lean_dec_ref(v_i_u2081_2247_);
v___x_2362_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4);
v___x_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2363_, 0, v_g_u2080_2246_);
v___x_2364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2362_);
lean_ctor_set(v___x_2364_, 1, v___x_2363_);
v___x_2365_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6);
v___x_2366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2364_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
v___x_2367_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_2366_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_);
return v___x_2367_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___boxed(lean_object* v_useAfter_2368_, lean_object* v_g_u2080_2369_, lean_object* v_i_u2081_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_){
_start:
{
uint8_t v_useAfter_boxed_2376_; lean_object* v_res_2377_; 
v_useAfter_boxed_2376_ = lean_unbox(v_useAfter_2368_);
v_res_2377_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(v_useAfter_boxed_2376_, v_g_u2080_2369_, v_i_u2081_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_);
lean_dec(v_a_2374_);
lean_dec_ref(v_a_2373_);
lean_dec(v_a_2372_);
lean_dec_ref(v_a_2371_);
return v_res_2377_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(lean_object* v_opts_2378_, lean_object* v_opt_2379_){
_start:
{
lean_object* v_name_2380_; lean_object* v_defValue_2381_; lean_object* v_map_2382_; lean_object* v___x_2383_; 
v_name_2380_ = lean_ctor_get(v_opt_2379_, 0);
v_defValue_2381_ = lean_ctor_get(v_opt_2379_, 1);
v_map_2382_ = lean_ctor_get(v_opts_2378_, 0);
v___x_2383_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2382_, v_name_2380_);
if (lean_obj_tag(v___x_2383_) == 0)
{
uint8_t v___x_2384_; 
v___x_2384_ = lean_unbox(v_defValue_2381_);
return v___x_2384_;
}
else
{
lean_object* v_val_2385_; 
v_val_2385_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_val_2385_);
lean_dec_ref_known(v___x_2383_, 1);
if (lean_obj_tag(v_val_2385_) == 1)
{
uint8_t v_v_2386_; 
v_v_2386_ = lean_ctor_get_uint8(v_val_2385_, 0);
lean_dec_ref_known(v_val_2385_, 0);
return v_v_2386_;
}
else
{
uint8_t v___x_2387_; 
lean_dec(v_val_2385_);
v___x_2387_ = lean_unbox(v_defValue_2381_);
return v___x_2387_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0___boxed(lean_object* v_opts_2388_, lean_object* v_opt_2389_){
_start:
{
uint8_t v_res_2390_; lean_object* v_r_2391_; 
v_res_2390_ = l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(v_opts_2388_, v_opt_2389_);
lean_dec_ref(v_opt_2389_);
lean_dec_ref(v_opts_2388_);
v_r_2391_ = lean_box(v_res_2390_);
return v_r_2391_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(lean_object* v_x_2392_, lean_object* v_x_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
if (lean_obj_tag(v_x_2393_) == 0)
{
lean_object* v___x_2399_; 
v___x_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2399_, 0, v_x_2392_);
return v___x_2399_;
}
else
{
lean_object* v_head_2400_; lean_object* v_tail_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v_head_2400_ = lean_ctor_get(v_x_2393_, 0);
lean_inc_n(v_head_2400_, 2);
v_tail_2401_ = lean_ctor_get(v_x_2393_, 1);
lean_inc(v_tail_2401_);
lean_dec_ref_known(v_x_2393_, 2);
v___x_2402_ = l_Lean_Expr_mvar___override(v_head_2400_);
v___x_2403_ = l_Lean_Meta_getMVars(v___x_2402_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v_a_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
lean_inc(v_a_2404_);
lean_dec_ref_known(v___x_2403_, 1);
v___x_2405_ = l_Lean_MVarIdSet_ofArray(v_a_2404_);
lean_dec(v_a_2404_);
v___x_2406_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_head_2400_, v___x_2405_, v_x_2392_);
v_x_2392_ = v___x_2406_;
v_x_2393_ = v_tail_2401_;
goto _start;
}
else
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2415_; 
lean_dec(v_tail_2401_);
lean_dec(v_head_2400_);
lean_dec(v_x_2392_);
v_a_2408_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2410_ = v___x_2403_;
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2403_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2413_; 
if (v_isShared_2411_ == 0)
{
v___x_2413_ = v___x_2410_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_a_2408_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1___boxed(lean_object* v_x_2416_, lean_object* v_x_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(v_x_2416_, v_x_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(lean_object* v_lctx_2424_, lean_object* v_localInsts_2425_, lean_object* v_x_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v___x_2432_; 
v___x_2432_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2424_, v_localInsts_2425_, v_x_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2432_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2432_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
else
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2448_; 
v_a_2441_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2443_ = v___x_2432_;
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2432_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2446_; 
if (v_isShared_2444_ == 0)
{
v___x_2446_ = v___x_2443_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_a_2441_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg___boxed(lean_object* v_lctx_2449_, lean_object* v_localInsts_2450_, lean_object* v_x_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(v_lctx_2449_, v_localInsts_2450_, v_x_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
return v_res_2457_;
}
}
static lean_object* _init_l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = ((lean_object*)(l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__0));
v___x_2460_ = l_Lean_stringToMessageData(v___x_2459_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(lean_object* v_goal_2461_, lean_object* v_action_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v___x_2468_; lean_object* v_mctx_2469_; lean_object* v___x_2470_; 
v___x_2468_ = lean_st_ref_get(v___y_2464_);
v_mctx_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc_ref(v_mctx_2469_);
lean_dec(v___x_2468_);
v___x_2470_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2469_, v_goal_2461_);
lean_dec_ref(v_mctx_2469_);
if (lean_obj_tag(v___x_2470_) == 1)
{
lean_object* v_val_2471_; lean_object* v_options_2472_; lean_object* v_lctx_2473_; lean_object* v_localInstances_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v_fst_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
lean_dec(v_goal_2461_);
v_val_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_val_2471_);
lean_dec_ref_known(v___x_2470_, 1);
v_options_2472_ = lean_ctor_get(v___y_2465_, 2);
v_lctx_2473_ = lean_ctor_get(v_val_2471_, 1);
v_localInstances_2474_ = lean_ctor_get(v_val_2471_, 4);
lean_inc_ref(v_localInstances_2474_);
v___x_2475_ = lean_box(1);
lean_inc_ref(v_options_2472_);
v___x_2476_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2476_, 0, v_options_2472_);
lean_ctor_set(v___x_2476_, 1, v___x_2475_);
lean_ctor_set(v___x_2476_, 2, v___x_2475_);
lean_inc_ref(v_lctx_2473_);
v___x_2477_ = l_Lean_LocalContext_sanitizeNames(v_lctx_2473_, v___x_2476_);
v_fst_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc_n(v_fst_2478_, 2);
lean_dec_ref(v___x_2477_);
v___x_2479_ = lean_apply_2(v_action_2462_, v_fst_2478_, v_val_2471_);
v___x_2480_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(v_fst_2478_, v_localInstances_2474_, v___x_2479_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
return v___x_2480_;
}
else
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
lean_dec(v___x_2470_);
lean_dec_ref(v_action_2462_);
v___x_2481_ = lean_obj_once(&l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1, &l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1_once, _init_l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1);
v___x_2482_ = l_Lean_MessageData_ofName(v_goal_2461_);
v___x_2483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2481_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
v___x_2484_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_2483_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
return v___x_2484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___boxed(lean_object* v_goal_2485_, lean_object* v_action_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(v_goal_2485_, v_action_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
return v_res_2492_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4(lean_object* v___x_2493_, lean_object* v_x_2494_){
_start:
{
if (lean_obj_tag(v_x_2494_) == 0)
{
uint8_t v___x_2495_; 
v___x_2495_ = 0;
return v___x_2495_;
}
else
{
lean_object* v_head_2496_; lean_object* v_tail_2497_; uint8_t v___x_2498_; 
v_head_2496_ = lean_ctor_get(v_x_2494_, 0);
v_tail_2497_ = lean_ctor_get(v_x_2494_, 1);
v___x_2498_ = l_Lean_instBEqMVarId_beq(v_head_2496_, v___x_2493_);
if (v___x_2498_ == 0)
{
v_x_2494_ = v_tail_2497_;
goto _start;
}
else
{
return v___x_2498_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4___boxed(lean_object* v___x_2500_, lean_object* v_x_2501_){
_start:
{
uint8_t v_res_2502_; lean_object* v_r_2503_; 
v_res_2502_ = l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4(v___x_2500_, v_x_2501_);
lean_dec(v_x_2501_);
lean_dec(v___x_2500_);
v_r_2503_ = lean_box(v_res_2502_);
return v_r_2503_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(lean_object* v_t_2504_, lean_object* v_k_2505_){
_start:
{
if (lean_obj_tag(v_t_2504_) == 0)
{
lean_object* v_k_2506_; lean_object* v_v_2507_; lean_object* v_l_2508_; lean_object* v_r_2509_; uint8_t v___x_2510_; 
v_k_2506_ = lean_ctor_get(v_t_2504_, 1);
v_v_2507_ = lean_ctor_get(v_t_2504_, 2);
v_l_2508_ = lean_ctor_get(v_t_2504_, 3);
v_r_2509_ = lean_ctor_get(v_t_2504_, 4);
v___x_2510_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2505_, v_k_2506_);
switch(v___x_2510_)
{
case 0:
{
v_t_2504_ = v_l_2508_;
goto _start;
}
case 1:
{
lean_object* v___x_2512_; 
lean_inc(v_v_2507_);
v___x_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2512_, 0, v_v_2507_);
return v___x_2512_;
}
default: 
{
v_t_2504_ = v_r_2509_;
goto _start;
}
}
}
else
{
lean_object* v___x_2514_; 
v___x_2514_ = lean_box(0);
return v___x_2514_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg___boxed(lean_object* v_t_2515_, lean_object* v_k_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(v_t_2515_, v_k_2516_);
lean_dec(v_k_2516_);
lean_dec(v_t_2515_);
return v_res_2517_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(lean_object* v_k_2518_, lean_object* v_t_2519_){
_start:
{
if (lean_obj_tag(v_t_2519_) == 0)
{
lean_object* v_k_2520_; lean_object* v_l_2521_; lean_object* v_r_2522_; uint8_t v___x_2523_; 
v_k_2520_ = lean_ctor_get(v_t_2519_, 1);
v_l_2521_ = lean_ctor_get(v_t_2519_, 3);
v_r_2522_ = lean_ctor_get(v_t_2519_, 4);
v___x_2523_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2518_, v_k_2520_);
switch(v___x_2523_)
{
case 0:
{
v_t_2519_ = v_l_2521_;
goto _start;
}
case 1:
{
uint8_t v___x_2525_; 
v___x_2525_ = 1;
return v___x_2525_;
}
default: 
{
v_t_2519_ = v_r_2522_;
goto _start;
}
}
}
else
{
uint8_t v___x_2527_; 
v___x_2527_ = 0;
return v___x_2527_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg___boxed(lean_object* v_k_2528_, lean_object* v_t_2529_){
_start:
{
uint8_t v_res_2530_; lean_object* v_r_2531_; 
v_res_2530_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_k_2528_, v_t_2529_);
lean_dec(v_t_2529_);
lean_dec(v_k_2528_);
v_r_2531_ = lean_box(v_res_2530_);
return v_r_2531_;
}
}
LEAN_EXPORT uint8_t l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(lean_object* v_a_2532_, uint8_t v___x_2533_, lean_object* v_before_2534_, lean_object* v_after_2535_){
_start:
{
lean_object* v___x_2536_; 
v___x_2536_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(v_a_2532_, v_before_2534_);
if (lean_obj_tag(v___x_2536_) == 0)
{
return v___x_2533_;
}
else
{
lean_object* v_val_2537_; uint8_t v___x_2538_; 
v_val_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_val_2537_);
lean_dec_ref_known(v___x_2536_, 1);
v___x_2538_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_after_2535_, v_val_2537_);
lean_dec(v_val_2537_);
return v___x_2538_;
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0___boxed(lean_object* v_a_2539_, lean_object* v___x_2540_, lean_object* v_before_2541_, lean_object* v_after_2542_){
_start:
{
uint8_t v___x_3864__boxed_2543_; uint8_t v_res_2544_; lean_object* v_r_2545_; 
v___x_3864__boxed_2543_ = lean_unbox(v___x_2540_);
v_res_2544_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(v_a_2539_, v___x_3864__boxed_2543_, v_before_2541_, v_after_2542_);
lean_dec(v_after_2542_);
lean_dec(v_before_2541_);
lean_dec(v_a_2539_);
v_r_2545_ = lean_box(v_res_2544_);
return v_r_2545_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5(uint8_t v___y_2546_, lean_object* v_a_2547_, lean_object* v___x_2548_, lean_object* v_x_2549_){
_start:
{
if (lean_obj_tag(v_x_2549_) == 0)
{
lean_object* v___x_2550_; 
v___x_2550_ = lean_box(0);
return v___x_2550_;
}
else
{
lean_object* v_head_2551_; lean_object* v_tail_2552_; uint8_t v___y_2554_; uint8_t v___x_2557_; 
v_head_2551_ = lean_ctor_get(v_x_2549_, 0);
v_tail_2552_ = lean_ctor_get(v_x_2549_, 1);
v___x_2557_ = 0;
if (v___y_2546_ == 0)
{
uint8_t v___x_2558_; 
v___x_2558_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(v_a_2547_, v___x_2557_, v___x_2548_, v_head_2551_);
v___y_2554_ = v___x_2558_;
goto v___jp_2553_;
}
else
{
uint8_t v___x_2559_; 
v___x_2559_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(v_a_2547_, v___x_2557_, v_head_2551_, v___x_2548_);
v___y_2554_ = v___x_2559_;
goto v___jp_2553_;
}
v___jp_2553_:
{
if (v___y_2554_ == 0)
{
v_x_2549_ = v_tail_2552_;
goto _start;
}
else
{
lean_object* v___x_2556_; 
lean_inc(v_head_2551_);
v___x_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2556_, 0, v_head_2551_);
return v___x_2556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___boxed(lean_object* v___y_2560_, lean_object* v_a_2561_, lean_object* v___x_2562_, lean_object* v_x_2563_){
_start:
{
uint8_t v___y_3875__boxed_2564_; lean_object* v_res_2565_; 
v___y_3875__boxed_2564_ = lean_unbox(v___y_2560_);
v_res_2565_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5(v___y_3875__boxed_2564_, v_a_2561_, v___x_2562_, v_x_2563_);
lean_dec(v_x_2563_);
lean_dec(v___x_2562_);
lean_dec(v_a_2561_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0(lean_object* v_mvarId_2566_, lean_object* v___y_2567_, uint8_t v___y_2568_, lean_object* v_a_2569_, uint8_t v_useAfter_2570_, lean_object* v_v_2571_, uint8_t v___x_2572_, lean_object* v_toInteractiveGoalCore_2573_, lean_object* v_userName_x3f_2574_, lean_object* v_goalPrefix_2575_, lean_object* v_isInserted_x3f_2576_, lean_object* v_isRemoved_x3f_2577_, lean_object* v___lctx_u2081_2578_, lean_object* v___md_u2081_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
uint8_t v___x_2585_; 
v___x_2585_ = l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4(v_mvarId_2566_, v___y_2567_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2586_; 
v___x_2586_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5(v___y_2568_, v_a_2569_, v_mvarId_2566_, v___y_2567_);
if (lean_obj_tag(v___x_2586_) == 1)
{
lean_object* v_val_2587_; lean_object* v___x_2588_; 
lean_dec(v_isRemoved_x3f_2577_);
lean_dec(v_isInserted_x3f_2576_);
lean_dec_ref(v_goalPrefix_2575_);
lean_dec(v_userName_x3f_2574_);
lean_dec_ref(v_toInteractiveGoalCore_2573_);
lean_dec(v_mvarId_2566_);
v_val_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_val_2587_);
lean_dec_ref_known(v___x_2586_, 1);
v___x_2588_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(v_useAfter_2570_, v_val_2587_, v_v_2571_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2588_;
}
else
{
lean_dec(v___x_2586_);
lean_dec(v_v_2571_);
if (v___y_2568_ == 0)
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
lean_dec(v_isRemoved_x3f_2577_);
v___x_2589_ = lean_box(v___x_2572_);
v___x_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
v___x_2591_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2591_, 0, v_toInteractiveGoalCore_2573_);
lean_ctor_set(v___x_2591_, 1, v_userName_x3f_2574_);
lean_ctor_set(v___x_2591_, 2, v_goalPrefix_2575_);
lean_ctor_set(v___x_2591_, 3, v_mvarId_2566_);
lean_ctor_set(v___x_2591_, 4, v_isInserted_x3f_2576_);
lean_ctor_set(v___x_2591_, 5, v___x_2590_);
v___x_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
return v___x_2592_;
}
else
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
lean_dec(v_isInserted_x3f_2576_);
v___x_2593_ = lean_box(v___x_2572_);
v___x_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
v___x_2595_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2595_, 0, v_toInteractiveGoalCore_2573_);
lean_ctor_set(v___x_2595_, 1, v_userName_x3f_2574_);
lean_ctor_set(v___x_2595_, 2, v_goalPrefix_2575_);
lean_ctor_set(v___x_2595_, 3, v_mvarId_2566_);
lean_ctor_set(v___x_2595_, 4, v___x_2594_);
lean_ctor_set(v___x_2595_, 5, v_isRemoved_x3f_2577_);
v___x_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
return v___x_2596_;
}
}
}
else
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
lean_dec(v_isInserted_x3f_2576_);
lean_dec(v_v_2571_);
v___x_2597_ = lean_box(0);
v___x_2598_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2598_, 0, v_toInteractiveGoalCore_2573_);
lean_ctor_set(v___x_2598_, 1, v_userName_x3f_2574_);
lean_ctor_set(v___x_2598_, 2, v_goalPrefix_2575_);
lean_ctor_set(v___x_2598_, 3, v_mvarId_2566_);
lean_ctor_set(v___x_2598_, 4, v___x_2597_);
lean_ctor_set(v___x_2598_, 5, v_isRemoved_x3f_2577_);
v___x_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2598_);
return v___x_2599_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0___boxed(lean_object** _args){
lean_object* v_mvarId_2600_ = _args[0];
lean_object* v___y_2601_ = _args[1];
lean_object* v___y_2602_ = _args[2];
lean_object* v_a_2603_ = _args[3];
lean_object* v_useAfter_2604_ = _args[4];
lean_object* v_v_2605_ = _args[5];
lean_object* v___x_2606_ = _args[6];
lean_object* v_toInteractiveGoalCore_2607_ = _args[7];
lean_object* v_userName_x3f_2608_ = _args[8];
lean_object* v_goalPrefix_2609_ = _args[9];
lean_object* v_isInserted_x3f_2610_ = _args[10];
lean_object* v_isRemoved_x3f_2611_ = _args[11];
lean_object* v___lctx_u2081_2612_ = _args[12];
lean_object* v___md_u2081_2613_ = _args[13];
lean_object* v___y_2614_ = _args[14];
lean_object* v___y_2615_ = _args[15];
lean_object* v___y_2616_ = _args[16];
lean_object* v___y_2617_ = _args[17];
lean_object* v___y_2618_ = _args[18];
_start:
{
uint8_t v___y_3908__boxed_2619_; uint8_t v_useAfter_boxed_2620_; uint8_t v___x_3910__boxed_2621_; lean_object* v_res_2622_; 
v___y_3908__boxed_2619_ = lean_unbox(v___y_2602_);
v_useAfter_boxed_2620_ = lean_unbox(v_useAfter_2604_);
v___x_3910__boxed_2621_ = lean_unbox(v___x_2606_);
v_res_2622_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0(v_mvarId_2600_, v___y_2601_, v___y_3908__boxed_2619_, v_a_2603_, v_useAfter_boxed_2620_, v_v_2605_, v___x_3910__boxed_2621_, v_toInteractiveGoalCore_2607_, v_userName_x3f_2608_, v_goalPrefix_2609_, v_isInserted_x3f_2610_, v_isRemoved_x3f_2611_, v___lctx_u2081_2612_, v___md_u2081_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec_ref(v___md_u2081_2613_);
lean_dec_ref(v___lctx_u2081_2612_);
lean_dec(v_a_2603_);
lean_dec(v___y_2601_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8(lean_object* v___y_2623_, uint8_t v___y_2624_, lean_object* v_a_2625_, uint8_t v_useAfter_2626_, uint8_t v___x_2627_, size_t v_sz_2628_, size_t v_i_2629_, lean_object* v_bs_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
uint8_t v___x_2636_; 
v___x_2636_ = lean_usize_dec_lt(v_i_2629_, v_sz_2628_);
if (v___x_2636_ == 0)
{
lean_object* v___x_2637_; 
lean_dec(v_a_2625_);
lean_dec(v___y_2623_);
v___x_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2637_, 0, v_bs_2630_);
return v___x_2637_;
}
else
{
lean_object* v_v_2638_; lean_object* v_toInteractiveGoalCore_2639_; lean_object* v_userName_x3f_2640_; lean_object* v_goalPrefix_2641_; lean_object* v_mvarId_2642_; lean_object* v_isInserted_x3f_2643_; lean_object* v_isRemoved_x3f_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___f_2648_; lean_object* v___x_2649_; 
v_v_2638_ = lean_array_uget_borrowed(v_bs_2630_, v_i_2629_);
v_toInteractiveGoalCore_2639_ = lean_ctor_get(v_v_2638_, 0);
v_userName_x3f_2640_ = lean_ctor_get(v_v_2638_, 1);
v_goalPrefix_2641_ = lean_ctor_get(v_v_2638_, 2);
v_mvarId_2642_ = lean_ctor_get(v_v_2638_, 3);
v_isInserted_x3f_2643_ = lean_ctor_get(v_v_2638_, 4);
v_isRemoved_x3f_2644_ = lean_ctor_get(v_v_2638_, 5);
v___x_2645_ = lean_box(v___y_2624_);
v___x_2646_ = lean_box(v_useAfter_2626_);
v___x_2647_ = lean_box(v___x_2627_);
lean_inc(v_isRemoved_x3f_2644_);
lean_inc(v_isInserted_x3f_2643_);
lean_inc_ref(v_goalPrefix_2641_);
lean_inc(v_userName_x3f_2640_);
lean_inc_ref(v_toInteractiveGoalCore_2639_);
lean_inc(v_v_2638_);
lean_inc(v_a_2625_);
lean_inc(v___y_2623_);
lean_inc_n(v_mvarId_2642_, 2);
v___f_2648_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0___boxed), 19, 12);
lean_closure_set(v___f_2648_, 0, v_mvarId_2642_);
lean_closure_set(v___f_2648_, 1, v___y_2623_);
lean_closure_set(v___f_2648_, 2, v___x_2645_);
lean_closure_set(v___f_2648_, 3, v_a_2625_);
lean_closure_set(v___f_2648_, 4, v___x_2646_);
lean_closure_set(v___f_2648_, 5, v_v_2638_);
lean_closure_set(v___f_2648_, 6, v___x_2647_);
lean_closure_set(v___f_2648_, 7, v_toInteractiveGoalCore_2639_);
lean_closure_set(v___f_2648_, 8, v_userName_x3f_2640_);
lean_closure_set(v___f_2648_, 9, v_goalPrefix_2641_);
lean_closure_set(v___f_2648_, 10, v_isInserted_x3f_2643_);
lean_closure_set(v___f_2648_, 11, v_isRemoved_x3f_2644_);
v___x_2649_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(v_mvarId_2642_, v___f_2648_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; lean_object* v___x_2651_; lean_object* v_bs_x27_2652_; size_t v___x_2653_; size_t v___x_2654_; lean_object* v___x_2655_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2650_);
lean_dec_ref_known(v___x_2649_, 1);
v___x_2651_ = lean_unsigned_to_nat(0u);
v_bs_x27_2652_ = lean_array_uset(v_bs_2630_, v_i_2629_, v___x_2651_);
v___x_2653_ = ((size_t)1ULL);
v___x_2654_ = lean_usize_add(v_i_2629_, v___x_2653_);
v___x_2655_ = lean_array_uset(v_bs_x27_2652_, v_i_2629_, v_a_2650_);
v_i_2629_ = v___x_2654_;
v_bs_2630_ = v___x_2655_;
goto _start;
}
else
{
lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2664_; 
lean_dec_ref(v_bs_2630_);
lean_dec(v_a_2625_);
lean_dec(v___y_2623_);
v_a_2657_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2659_ = v___x_2649_;
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v___x_2649_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2662_; 
if (v_isShared_2660_ == 0)
{
v___x_2662_ = v___x_2659_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_a_2657_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8___boxed(lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v_a_2667_, lean_object* v_useAfter_2668_, lean_object* v___x_2669_, lean_object* v_sz_2670_, lean_object* v_i_2671_, lean_object* v_bs_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
uint8_t v___y_3965__boxed_2678_; uint8_t v_useAfter_boxed_2679_; uint8_t v___x_3967__boxed_2680_; size_t v_sz_boxed_2681_; size_t v_i_boxed_2682_; lean_object* v_res_2683_; 
v___y_3965__boxed_2678_ = lean_unbox(v___y_2666_);
v_useAfter_boxed_2679_ = lean_unbox(v_useAfter_2668_);
v___x_3967__boxed_2680_ = lean_unbox(v___x_2669_);
v_sz_boxed_2681_ = lean_unbox_usize(v_sz_2670_);
lean_dec(v_sz_2670_);
v_i_boxed_2682_ = lean_unbox_usize(v_i_2671_);
lean_dec(v_i_2671_);
v_res_2683_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8(v___y_2665_, v___y_3965__boxed_2678_, v_a_2667_, v_useAfter_boxed_2679_, v___x_3967__boxed_2680_, v_sz_boxed_2681_, v_i_boxed_2682_, v_bs_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7(uint8_t v___y_2684_, lean_object* v_a_2685_, lean_object* v___y_2686_, uint8_t v_useAfter_2687_, uint8_t v___x_2688_, size_t v_sz_2689_, size_t v_i_2690_, lean_object* v_bs_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_){
_start:
{
uint8_t v___x_2697_; 
v___x_2697_ = lean_usize_dec_lt(v_i_2690_, v_sz_2689_);
if (v___x_2697_ == 0)
{
lean_object* v___x_2698_; 
lean_dec(v___y_2686_);
lean_dec(v_a_2685_);
v___x_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2698_, 0, v_bs_2691_);
return v___x_2698_;
}
else
{
lean_object* v_v_2699_; lean_object* v_toInteractiveGoalCore_2700_; lean_object* v_userName_x3f_2701_; lean_object* v_goalPrefix_2702_; lean_object* v_mvarId_2703_; lean_object* v_isInserted_x3f_2704_; lean_object* v_isRemoved_x3f_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___f_2709_; lean_object* v___x_2710_; 
v_v_2699_ = lean_array_uget_borrowed(v_bs_2691_, v_i_2690_);
v_toInteractiveGoalCore_2700_ = lean_ctor_get(v_v_2699_, 0);
v_userName_x3f_2701_ = lean_ctor_get(v_v_2699_, 1);
v_goalPrefix_2702_ = lean_ctor_get(v_v_2699_, 2);
v_mvarId_2703_ = lean_ctor_get(v_v_2699_, 3);
v_isInserted_x3f_2704_ = lean_ctor_get(v_v_2699_, 4);
v_isRemoved_x3f_2705_ = lean_ctor_get(v_v_2699_, 5);
v___x_2706_ = lean_box(v___y_2684_);
v___x_2707_ = lean_box(v_useAfter_2687_);
v___x_2708_ = lean_box(v___x_2688_);
lean_inc(v_isRemoved_x3f_2705_);
lean_inc(v_isInserted_x3f_2704_);
lean_inc_ref(v_goalPrefix_2702_);
lean_inc(v_userName_x3f_2701_);
lean_inc_ref(v_toInteractiveGoalCore_2700_);
lean_inc(v_v_2699_);
lean_inc(v_a_2685_);
lean_inc(v___y_2686_);
lean_inc_n(v_mvarId_2703_, 2);
v___f_2709_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0___boxed), 19, 12);
lean_closure_set(v___f_2709_, 0, v_mvarId_2703_);
lean_closure_set(v___f_2709_, 1, v___y_2686_);
lean_closure_set(v___f_2709_, 2, v___x_2706_);
lean_closure_set(v___f_2709_, 3, v_a_2685_);
lean_closure_set(v___f_2709_, 4, v___x_2707_);
lean_closure_set(v___f_2709_, 5, v_v_2699_);
lean_closure_set(v___f_2709_, 6, v___x_2708_);
lean_closure_set(v___f_2709_, 7, v_toInteractiveGoalCore_2700_);
lean_closure_set(v___f_2709_, 8, v_userName_x3f_2701_);
lean_closure_set(v___f_2709_, 9, v_goalPrefix_2702_);
lean_closure_set(v___f_2709_, 10, v_isInserted_x3f_2704_);
lean_closure_set(v___f_2709_, 11, v_isRemoved_x3f_2705_);
v___x_2710_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(v_mvarId_2703_, v___f_2709_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; lean_object* v___x_2712_; lean_object* v_bs_x27_2713_; size_t v___x_2714_; size_t v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_a_2711_);
lean_dec_ref_known(v___x_2710_, 1);
v___x_2712_ = lean_unsigned_to_nat(0u);
v_bs_x27_2713_ = lean_array_uset(v_bs_2691_, v_i_2690_, v___x_2712_);
v___x_2714_ = ((size_t)1ULL);
v___x_2715_ = lean_usize_add(v_i_2690_, v___x_2714_);
v___x_2716_ = lean_array_uset(v_bs_x27_2713_, v_i_2690_, v_a_2711_);
v___x_2717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8(v___y_2686_, v___y_2684_, v_a_2685_, v_useAfter_2687_, v___x_2688_, v_sz_2689_, v___x_2715_, v___x_2716_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
return v___x_2717_;
}
else
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
lean_dec_ref(v_bs_2691_);
lean_dec(v___y_2686_);
lean_dec(v_a_2685_);
v_a_2718_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2720_ = v___x_2710_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2710_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2718_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___boxed(lean_object* v___y_2726_, lean_object* v_a_2727_, lean_object* v___y_2728_, lean_object* v_useAfter_2729_, lean_object* v___x_2730_, lean_object* v_sz_2731_, lean_object* v_i_2732_, lean_object* v_bs_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
uint8_t v___y_4033__boxed_2739_; uint8_t v_useAfter_boxed_2740_; uint8_t v___x_4036__boxed_2741_; size_t v_sz_boxed_2742_; size_t v_i_boxed_2743_; lean_object* v_res_2744_; 
v___y_4033__boxed_2739_ = lean_unbox(v___y_2726_);
v_useAfter_boxed_2740_ = lean_unbox(v_useAfter_2729_);
v___x_4036__boxed_2741_ = lean_unbox(v___x_2730_);
v_sz_boxed_2742_ = lean_unbox_usize(v_sz_2731_);
lean_dec(v_sz_2731_);
v_i_boxed_2743_ = lean_unbox_usize(v_i_2732_);
lean_dec(v_i_2732_);
v_res_2744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7(v___y_4033__boxed_2739_, v_a_2727_, v___y_2728_, v_useAfter_boxed_2740_, v___x_4036__boxed_2741_, v_sz_boxed_2742_, v_i_boxed_2743_, v_bs_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_diffInteractiveGoals(uint8_t v_useAfter_2745_, lean_object* v_info_2746_, lean_object* v_igs_u2081_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v_options_2753_; lean_object* v___x_2754_; uint8_t v___x_2755_; lean_object* v___y_2757_; 
v_options_2753_ = lean_ctor_get(v_a_2750_, 2);
v___x_2754_ = l___private_Lean_Widget_Diff_0__Lean_Widget_showTacticDiff;
v___x_2755_ = l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(v_options_2753_, v___x_2754_);
if (v___x_2755_ == 0)
{
lean_object* v___x_2789_; 
lean_dec_ref(v_info_2746_);
v___x_2789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2789_, 0, v_igs_u2081_2747_);
return v___x_2789_;
}
else
{
if (v_useAfter_2745_ == 0)
{
lean_object* v_goalsAfter_2790_; 
v_goalsAfter_2790_ = lean_ctor_get(v_info_2746_, 4);
lean_inc(v_goalsAfter_2790_);
v___y_2757_ = v_goalsAfter_2790_;
goto v___jp_2756_;
}
else
{
lean_object* v_goalsBefore_2791_; 
v_goalsBefore_2791_ = lean_ctor_get(v_info_2746_, 2);
lean_inc(v_goalsBefore_2791_);
v___y_2757_ = v_goalsBefore_2791_;
goto v___jp_2756_;
}
}
v___jp_2756_:
{
lean_object* v_goalsBefore_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
v_goalsBefore_2758_ = lean_ctor_get(v_info_2746_, 2);
lean_inc(v_goalsBefore_2758_);
lean_dec_ref(v_info_2746_);
v___x_2759_ = lean_box(1);
v___x_2760_ = l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(v___x_2759_, v_goalsBefore_2758_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v_a_2761_; size_t v_sz_2762_; size_t v___x_2763_; lean_object* v___x_2764_; 
v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
lean_inc(v_a_2761_);
lean_dec_ref_known(v___x_2760_, 1);
v_sz_2762_ = lean_array_size(v_igs_u2081_2747_);
v___x_2763_ = ((size_t)0ULL);
v___x_2764_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7(v_useAfter_2745_, v_a_2761_, v___y_2757_, v_useAfter_2745_, v___x_2755_, v_sz_2762_, v___x_2763_, v_igs_u2081_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___x_2764_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2764_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2770_; 
if (v_isShared_2768_ == 0)
{
v___x_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2765_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
else
{
lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2780_; 
v_a_2773_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2775_ = v___x_2764_;
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v___x_2764_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2778_; 
if (v_isShared_2776_ == 0)
{
v___x_2778_ = v___x_2775_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_a_2773_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
else
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
lean_dec(v___y_2757_);
lean_dec_ref(v_igs_u2081_2747_);
v_a_2781_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2783_ = v___x_2760_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2760_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2781_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_diffInteractiveGoals___boxed(lean_object* v_useAfter_2792_, lean_object* v_info_2793_, lean_object* v_igs_u2081_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_){
_start:
{
uint8_t v_useAfter_boxed_2800_; lean_object* v_res_2801_; 
v_useAfter_boxed_2800_ = lean_unbox(v_useAfter_2792_);
v_res_2801_ = l_Lean_Widget_diffInteractiveGoals(v_useAfter_boxed_2800_, v_info_2793_, v_igs_u2081_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_);
lean_dec(v_a_2798_);
lean_dec_ref(v_a_2797_);
lean_dec(v_a_2796_);
lean_dec_ref(v_a_2795_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2(lean_object* v_00_u03b4_2802_, lean_object* v_t_2803_, lean_object* v_k_2804_){
_start:
{
lean_object* v___x_2805_; 
v___x_2805_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(v_t_2803_, v_k_2804_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___boxed(lean_object* v_00_u03b4_2806_, lean_object* v_t_2807_, lean_object* v_k_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2(v_00_u03b4_2806_, v_t_2807_, v_k_2808_);
lean_dec(v_k_2808_);
lean_dec(v_t_2807_);
return v_res_2809_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3(lean_object* v_00_u03b2_2810_, lean_object* v_k_2811_, lean_object* v_t_2812_){
_start:
{
uint8_t v___x_2813_; 
v___x_2813_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_k_2811_, v_t_2812_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___boxed(lean_object* v_00_u03b2_2814_, lean_object* v_k_2815_, lean_object* v_t_2816_){
_start:
{
uint8_t v_res_2817_; lean_object* v_r_2818_; 
v_res_2817_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3(v_00_u03b2_2814_, v_k_2815_, v_t_2816_);
lean_dec(v_t_2816_);
lean_dec(v_k_2815_);
v_r_2818_ = lean_box(v_res_2817_);
return v_r_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6(lean_object* v_00_u03b1_2819_, lean_object* v_lctx_2820_, lean_object* v_localInsts_2821_, lean_object* v_x_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_){
_start:
{
lean_object* v___x_2828_; 
v___x_2828_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(v_lctx_2820_, v_localInsts_2821_, v_x_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___boxed(lean_object* v_00_u03b1_2829_, lean_object* v_lctx_2830_, lean_object* v_localInsts_2831_, lean_object* v_x_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6(v_00_u03b1_2829_, v_lctx_2830_, v_localInsts_2831_, v_x_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6(lean_object* v_00_u03b1_2839_, lean_object* v_goal_2840_, lean_object* v_action_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v___x_2847_; 
v___x_2847_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(v_goal_2840_, v_action_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___boxed(lean_object* v_00_u03b1_2848_, lean_object* v_goal_2849_, lean_object* v_action_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6(v_00_u03b1_2848_, v_goal_2849_, v_action_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
return v_res_2856_;
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
