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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
uint8_t v_x2_241__boxed_250_; lean_object* v_res_251_; 
v_x2_241__boxed_250_ = lean_unbox(v_x2_248_);
v_res_251_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1(v_x1_247_, v_x2_241__boxed_250_, v_x3_249_);
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
v___x_354_ = lean_nat_add(v___y_352_, v___y_353_);
lean_dec(v___y_353_);
lean_dec(v___y_352_);
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
lean_ctor_set(v___x_334_, 3, v___y_351_);
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
lean_ctor_set(v_reuseFailAlloc_359_, 3, v___y_351_);
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
v___y_351_ = v___x_365_;
v___y_352_ = v___x_366_;
v___y_353_ = v_size_367_;
goto v___jp_350_;
}
else
{
lean_object* v___x_368_; 
v___x_368_ = lean_unsigned_to_nat(0u);
v___y_351_ = v___x_365_;
v___y_352_ = v___x_366_;
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
v___x_492_ = lean_nat_add(v___y_489_, v___y_491_);
lean_dec(v___y_491_);
lean_dec(v___y_489_);
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
lean_ctor_set(v___x_472_, 3, v___y_490_);
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
lean_ctor_set(v_reuseFailAlloc_497_, 3, v___y_490_);
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
v___y_489_ = v___x_505_;
v___y_490_ = v___x_504_;
v___y_491_ = v_size_506_;
goto v___jp_488_;
}
else
{
lean_object* v___x_507_; 
v___x_507_ = lean_unsigned_to_nat(0u);
v___y_489_ = v___x_505_;
v___y_490_ = v___x_504_;
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
lean_object* v_changesBefore_665_; lean_object* v_changesAfter_666_; uint8_t v___y_668_; 
v_changesBefore_665_ = lean_ctor_get(v_d_664_, 0);
v_changesAfter_666_ = lean_ctor_get(v_d_664_, 1);
if (lean_obj_tag(v_changesAfter_666_) == 0)
{
uint8_t v___x_670_; 
v___x_670_ = 0;
v___y_668_ = v___x_670_;
goto v___jp_667_;
}
else
{
uint8_t v___x_671_; 
v___x_671_ = 1;
v___y_668_ = v___x_671_;
goto v___jp_667_;
}
v___jp_667_:
{
if (lean_obj_tag(v_changesBefore_665_) == 0)
{
if (v___y_668_ == 0)
{
return v___y_668_;
}
else
{
uint8_t v___x_669_; 
v___x_669_ = 0;
return v___x_669_;
}
}
else
{
return v___y_668_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty___boxed(lean_object* v_d_672_){
_start:
{
uint8_t v_res_673_; lean_object* v_r_674_; 
v_res_673_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_d_672_);
lean_dec_ref(v_d_672_);
v_r_674_ = lean_box(v_res_673_);
return v_r_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0(lean_object* v_k_675_, lean_object* v_b_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v___x_682_; 
lean_inc(v___y_680_);
lean_inc_ref(v___y_679_);
lean_inc(v___y_678_);
lean_inc_ref(v___y_677_);
v___x_682_ = lean_apply_6(v_k_675_, v_b_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, lean_box(0));
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0___boxed(lean_object* v_k_683_, lean_object* v_b_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0(v_k_683_, v_b_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(lean_object* v_name_691_, uint8_t v_bi_692_, lean_object* v_type_693_, lean_object* v_k_694_, uint8_t v_kind_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v___f_701_; lean_object* v___x_702_; 
v___f_701_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_701_, 0, v_k_694_);
v___x_702_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_691_, v_bi_692_, v_type_693_, v___f_701_, v_kind_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_702_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_702_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
v_a_711_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_702_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_702_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___boxed(lean_object* v_name_719_, lean_object* v_bi_720_, lean_object* v_type_721_, lean_object* v_k_722_, lean_object* v_kind_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
uint8_t v_bi_boxed_729_; uint8_t v_kind_boxed_730_; lean_object* v_res_731_; 
v_bi_boxed_729_ = lean_unbox(v_bi_720_);
v_kind_boxed_730_ = lean_unbox(v_kind_723_);
v_res_731_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_name_719_, v_bi_boxed_729_, v_type_721_, v_k_722_, v_kind_boxed_730_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6(lean_object* v_00_u03b1_732_, lean_object* v_name_733_, uint8_t v_bi_734_, lean_object* v_type_735_, lean_object* v_k_736_, uint8_t v_kind_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_name_733_, v_bi_734_, v_type_735_, v_k_736_, v_kind_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___boxed(lean_object* v_00_u03b1_744_, lean_object* v_name_745_, lean_object* v_bi_746_, lean_object* v_type_747_, lean_object* v_k_748_, lean_object* v_kind_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
uint8_t v_bi_boxed_755_; uint8_t v_kind_boxed_756_; lean_object* v_res_757_; 
v_bi_boxed_755_ = lean_unbox(v_bi_746_);
v_kind_boxed_756_ = lean_unbox(v_kind_749_);
v_res_757_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6(v_00_u03b1_744_, v_name_745_, v_bi_boxed_755_, v_type_747_, v_k_748_, v_kind_boxed_756_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(lean_object* v_msgData_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v___x_764_; lean_object* v_env_765_; lean_object* v___x_766_; lean_object* v_mctx_767_; lean_object* v_lctx_768_; lean_object* v_options_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_764_ = lean_st_ref_get(v___y_762_);
v_env_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc_ref(v_env_765_);
lean_dec(v___x_764_);
v___x_766_ = lean_st_ref_get(v___y_760_);
v_mctx_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc_ref(v_mctx_767_);
lean_dec(v___x_766_);
v_lctx_768_ = lean_ctor_get(v___y_759_, 2);
v_options_769_ = lean_ctor_get(v___y_761_, 1);
lean_inc_ref(v_options_769_);
lean_inc_ref(v_lctx_768_);
v___x_770_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_770_, 0, v_env_765_);
lean_ctor_set(v___x_770_, 1, v_mctx_767_);
lean_ctor_set(v___x_770_, 2, v_lctx_768_);
lean_ctor_set(v___x_770_, 3, v_options_769_);
v___x_771_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
lean_ctor_set(v___x_771_, 1, v_msgData_758_);
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
v_ref_786_ = lean_ctor_get(v___y_783_, 4);
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
lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v_a_1043_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; uint8_t v___y_1054_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v_a_1073_; lean_object* v_expr_1076_; lean_object* v_pos_1077_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; 
v_expr_1076_ = lean_ctor_get(v_before_1030_, 0);
v_pos_1077_ = lean_ctor_get(v_before_1030_, 1);
if (lean_obj_tag(v_expr_1076_) == 7)
{
lean_object* v_binderName_1114_; lean_object* v_binderType_1115_; lean_object* v_body_1116_; uint8_t v_binderInfo_1117_; lean_object* v_expr_1118_; lean_object* v_pos_1119_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; 
v_binderName_1114_ = lean_ctor_get(v_expr_1076_, 0);
v_binderType_1115_ = lean_ctor_get(v_expr_1076_, 1);
v_body_1116_ = lean_ctor_get(v_expr_1076_, 2);
v_binderInfo_1117_ = lean_ctor_get_uint8(v_expr_1076_, sizeof(void*)*3 + 8);
v_expr_1118_ = lean_ctor_get(v_after_1031_, 0);
v_pos_1119_ = lean_ctor_get(v_after_1031_, 1);
if (lean_obj_tag(v_expr_1118_) == 7)
{
lean_object* v_binderName_1145_; lean_object* v_binderType_1146_; lean_object* v_body_1147_; uint8_t v_binderInfo_1148_; lean_object* v___f_1149_; uint8_t v___y_1151_; uint8_t v___x_1201_; 
v_binderName_1145_ = lean_ctor_get(v_expr_1118_, 0);
v_binderType_1146_ = lean_ctor_get(v_expr_1118_, 1);
v_body_1147_ = lean_ctor_get(v_expr_1118_, 2);
v_binderInfo_1148_ = lean_ctor_get_uint8(v_expr_1118_, sizeof(void*)*3 + 8);
lean_inc(v_pos_1119_);
lean_inc_ref(v_body_1147_);
lean_inc(v_pos_1077_);
lean_inc_ref(v_body_1116_);
v___f_1149_ = lean_alloc_closure((void*)(l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1149_, 0, v_body_1116_);
lean_closure_set(v___f_1149_, 1, v_pos_1077_);
lean_closure_set(v___f_1149_, 2, v_body_1147_);
lean_closure_set(v___f_1149_, 3, v_pos_1119_);
v___x_1201_ = lean_name_eq(v_binderName_1114_, v_binderName_1145_);
if (v___x_1201_ == 0)
{
v___y_1151_ = v___x_1201_;
goto v___jp_1150_;
}
else
{
uint8_t v___x_1202_; 
v___x_1202_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1117_, v_binderInfo_1148_);
v___y_1151_ = v___x_1202_;
goto v___jp_1150_;
}
v___jp_1150_:
{
if (v___y_1151_ == 0)
{
lean_dec_ref(v___f_1149_);
v___y_1121_ = v_a_1032_;
v___y_1122_ = v_a_1033_;
v___y_1123_ = v_a_1034_;
v___y_1124_ = v_a_1035_;
goto v___jp_1120_;
}
else
{
lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1198_; 
lean_inc_ref(v_binderType_1146_);
lean_inc(v_pos_1119_);
lean_inc_ref(v_binderType_1115_);
lean_inc(v_binderName_1114_);
lean_inc(v_pos_1077_);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_before_1030_);
if (v_isSharedCheck_1198_ == 0)
{
lean_object* v_unused_1199_; lean_object* v_unused_1200_; 
v_unused_1199_ = lean_ctor_get(v_before_1030_, 1);
lean_dec(v_unused_1199_);
v_unused_1200_ = lean_ctor_get(v_before_1030_, 0);
lean_dec(v_unused_1200_);
v___x_1153_ = v_before_1030_;
v_isShared_1154_ = v_isSharedCheck_1198_;
goto v_resetjp_1152_;
}
else
{
lean_dec(v_before_1030_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1198_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1195_; 
v_isSharedCheck_1195_ = !lean_is_exclusive(v_after_1031_);
if (v_isSharedCheck_1195_ == 0)
{
lean_object* v_unused_1196_; lean_object* v_unused_1197_; 
v_unused_1196_ = lean_ctor_get(v_after_1031_, 1);
lean_dec(v_unused_1196_);
v_unused_1197_ = lean_ctor_get(v_after_1031_, 0);
lean_dec(v_unused_1197_);
v___x_1156_ = v_after_1031_;
v_isShared_1157_ = v_isSharedCheck_1195_;
goto v_resetjp_1155_;
}
else
{
lean_dec(v_after_1031_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1195_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1158_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1077_);
lean_inc_ref(v_binderType_1115_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 1, v___x_1158_);
lean_ctor_set(v___x_1156_, 0, v_binderType_1115_);
v___x_1160_ = v___x_1156_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_binderType_1115_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
lean_object* v___x_1161_; lean_object* v___x_1163_; 
v___x_1161_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1119_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 1, v___x_1161_);
lean_ctor_set(v___x_1153_, 0, v_binderType_1146_);
v___x_1163_ = v___x_1153_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_binderType_1146_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v___x_1161_);
v___x_1163_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1164_; 
v___x_1164_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1160_, v___x_1163_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1192_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1167_ = v___x_1164_;
v_isShared_1168_ = v_isSharedCheck_1192_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1192_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
uint8_t v___x_1169_; 
v___x_1169_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_a_1165_);
if (v___x_1169_ == 0)
{
lean_object* v_changesBefore_1170_; lean_object* v_changesAfter_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; uint8_t v___x_1174_; lean_object* v___x_1175_; lean_object* v_changesBefore_1176_; lean_object* v_changesAfter_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1189_; 
lean_dec_ref(v___f_1149_);
lean_dec_ref(v_binderType_1115_);
lean_dec(v_binderName_1114_);
v_changesBefore_1170_ = lean_ctor_get(v_a_1165_, 0);
lean_inc(v_changesBefore_1170_);
v_changesAfter_1171_ = lean_ctor_get(v_a_1165_, 1);
lean_inc(v_changesAfter_1171_);
lean_dec(v_a_1165_);
v___x_1172_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1077_);
lean_dec(v_pos_1077_);
v___x_1173_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1119_);
lean_dec(v_pos_1119_);
v___x_1174_ = 0;
v___x_1175_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v___x_1172_, v___x_1173_, v___x_1174_);
v_changesBefore_1176_ = lean_ctor_get(v___x_1175_, 0);
v_changesAfter_1177_ = lean_ctor_get(v___x_1175_, 1);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1179_ = v___x_1175_;
v_isShared_1180_ = v_isSharedCheck_1189_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_changesAfter_1177_);
lean_inc(v_changesBefore_1176_);
lean_dec(v___x_1175_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1189_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1184_; 
v___x_1181_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesBefore_1170_, v_changesBefore_1176_);
v___x_1182_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesAfter_1171_, v_changesAfter_1177_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 1, v___x_1182_);
lean_ctor_set(v___x_1179_, 0, v___x_1181_);
v___x_1184_ = v___x_1179_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1181_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
lean_object* v___x_1186_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v___x_1184_);
v___x_1186_ = v___x_1167_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
else
{
uint8_t v___x_1190_; lean_object* v___x_1191_; 
lean_del_object(v___x_1167_);
lean_dec(v_a_1165_);
lean_dec(v_pos_1119_);
lean_dec(v_pos_1077_);
v___x_1190_ = 0;
v___x_1191_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_binderName_1114_, v_binderInfo_1117_, v_binderType_1115_, v___f_1149_, v___x_1190_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
return v___x_1191_;
}
}
}
else
{
lean_dec_ref(v___f_1149_);
lean_dec(v_pos_1119_);
lean_dec_ref(v_binderType_1115_);
lean_dec(v_binderName_1114_);
lean_dec(v_pos_1077_);
return v___x_1164_;
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
v___y_1121_ = v_a_1032_;
v___y_1122_ = v_a_1033_;
v___y_1123_ = v_a_1034_;
v___y_1124_ = v_a_1035_;
goto v___jp_1120_;
}
v___jp_1120_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1125_ = l_Lean_Expr_getForallBinderNames(v_expr_1118_);
v___x_1126_ = l_Lean_Expr_getForallBinderNames(v_expr_1076_);
v___x_1127_ = l_List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0(v___x_1125_, v___x_1126_);
if (lean_obj_tag(v___x_1127_) == 1)
{
lean_object* v_val_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; 
v_val_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_val_1128_);
lean_dec_ref_known(v___x_1127_, 1);
v___x_1129_ = l_List_lengthTR___redArg(v_val_1128_);
v___x_1130_ = lean_unsigned_to_nat(0u);
v___x_1131_ = lean_nat_dec_eq(v___x_1129_, v___x_1130_);
lean_dec(v___x_1129_);
if (v___x_1131_ == 0)
{
v___y_1079_ = v_val_1128_;
v___y_1080_ = v___y_1121_;
v___y_1081_ = v___y_1122_;
v___y_1082_ = v___y_1123_;
v___y_1083_ = v___y_1124_;
goto v___jp_1078_;
}
else
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1, &l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1);
v___x_1133_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_1132_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_dec_ref_known(v___x_1133_, 1);
v___y_1079_ = v_val_1128_;
v___y_1080_ = v___y_1121_;
v___y_1081_ = v___y_1122_;
v___y_1082_ = v___y_1123_;
v___y_1083_ = v___y_1124_;
goto v___jp_1078_;
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec(v_val_1128_);
lean_dec_ref(v_after_1031_);
lean_dec_ref(v_before_1030_);
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1133_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1133_);
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
else
{
uint8_t v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
lean_dec(v___x_1127_);
v___x_1142_ = 0;
v___x_1143_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1030_, v_after_1031_, v___x_1142_);
v___x_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
return v___x_1144_;
}
}
}
else
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
lean_dec_ref(v_after_1031_);
lean_dec_ref(v_before_1030_);
v___x_1203_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___x_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
return v___x_1204_;
}
v___jp_1037_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = lean_unsigned_to_nat(0u);
v___x_1045_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v___y_1041_, v_before_1030_, v___x_1044_, v_a_1043_);
lean_dec(v___y_1041_);
return v___x_1045_;
}
v___jp_1046_:
{
if (v___y_1054_ == 0)
{
lean_object* v___x_1055_; 
lean_dec_ref(v___y_1047_);
v___x_1055_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1051_, v___y_1053_, v___y_1049_);
lean_dec_ref(v___y_1051_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v___x_1056_; 
lean_dec_ref_known(v___x_1055_, 1);
v___x_1056_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___y_1038_ = v___y_1048_;
v___y_1039_ = v___y_1049_;
v___y_1040_ = v___y_1050_;
v___y_1041_ = v___y_1052_;
v___y_1042_ = v___y_1053_;
v_a_1043_ = v___x_1056_;
goto v___jp_1037_;
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
lean_dec(v___y_1052_);
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
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
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
v___y_1050_ = v___y_1069_;
v___y_1051_ = v___y_1068_;
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
v___y_1050_ = v___y_1069_;
v___y_1051_ = v___y_1068_;
v___y_1052_ = v___y_1070_;
v___y_1053_ = v___y_1071_;
v___y_1054_ = v___x_1074_;
goto v___jp_1046_;
}
}
v___jp_1078_:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_Meta_saveState___redArg(v___y_1081_, v___y_1083_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref_known(v___x_1084_, 1);
v___x_1086_ = l_List_lengthTR___redArg(v___y_1079_);
v___x_1087_ = lean_box(0);
v___x_1088_ = l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(v___y_1079_, v___x_1087_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; lean_object* v_body_u2080_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1089_);
lean_dec_ref_known(v___x_1088_, 1);
lean_inc_n(v___x_1086_, 2);
v_body_u2080_1090_ = l_Lean_Expr_getForallBodyMaxDepth(v___x_1086_, v_expr_1076_);
v___x_1091_ = lean_array_mk(v_a_1089_);
v___x_1092_ = lean_expr_instantiate_rev(v_body_u2080_1090_, v___x_1091_);
lean_dec_ref(v___x_1091_);
lean_dec_ref(v_body_u2080_1090_);
lean_inc(v_pos_1077_);
v___x_1093_ = l_Lean_SubExpr_Pos_pushNthBindingBody(v___x_1086_, v_pos_1077_);
v___x_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1092_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1094_, v_after_1031_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; 
lean_dec(v_a_1085_);
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v___x_1095_, 1);
v___y_1038_ = v___y_1080_;
v___y_1039_ = v___y_1083_;
v___y_1040_ = v___y_1082_;
v___y_1041_ = v___x_1086_;
v___y_1042_ = v___y_1081_;
v_a_1043_ = v_a_1096_;
goto v___jp_1037_;
}
else
{
lean_object* v_a_1097_; 
v_a_1097_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1097_);
v___y_1066_ = v___y_1080_;
v___y_1067_ = v___y_1083_;
v___y_1068_ = v_a_1085_;
v___y_1069_ = v___y_1082_;
v___y_1070_ = v___x_1086_;
v___y_1071_ = v___y_1081_;
v___y_1072_ = v___x_1095_;
v_a_1073_ = v_a_1097_;
goto v___jp_1065_;
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec_ref(v_after_1031_);
v_a_1098_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1088_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1088_);
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
v___y_1066_ = v___y_1080_;
v___y_1067_ = v___y_1083_;
v___y_1068_ = v_a_1085_;
v___y_1069_ = v___y_1082_;
v___y_1070_ = v___x_1086_;
v___y_1071_ = v___y_1081_;
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
lean_dec(v___y_1079_);
lean_dec_ref(v_after_1031_);
lean_dec_ref(v_before_1030_);
v_a_1106_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1084_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1084_);
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
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(lean_object* v_before_1205_, lean_object* v_after_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_){
_start:
{
lean_object* v_expr_1228_; lean_object* v_pos_1229_; lean_object* v_expr_1230_; lean_object* v_pos_1231_; lean_object* v_e_u2081_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; uint8_t v___x_1240_; 
v_expr_1228_ = lean_ctor_get(v_before_1205_, 0);
v_pos_1229_ = lean_ctor_get(v_before_1205_, 1);
v_expr_1230_ = lean_ctor_get(v_after_1206_, 0);
v_pos_1231_ = lean_ctor_get(v_after_1206_, 1);
v___x_1240_ = lean_expr_eqv(v_expr_1228_, v_expr_1230_);
if (v___x_1240_ == 0)
{
switch(lean_obj_tag(v_expr_1228_))
{
case 10:
{
lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1249_; 
lean_inc_ref(v_expr_1228_);
lean_inc(v_pos_1229_);
v_isSharedCheck_1249_ = !lean_is_exclusive(v_before_1205_);
if (v_isSharedCheck_1249_ == 0)
{
lean_object* v_unused_1250_; lean_object* v_unused_1251_; 
v_unused_1250_ = lean_ctor_get(v_before_1205_, 1);
lean_dec(v_unused_1250_);
v_unused_1251_ = lean_ctor_get(v_before_1205_, 0);
lean_dec(v_unused_1251_);
v___x_1242_ = v_before_1205_;
v_isShared_1243_ = v_isSharedCheck_1249_;
goto v_resetjp_1241_;
}
else
{
lean_dec(v_before_1205_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1249_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v_expr_1244_; lean_object* v___x_1246_; 
v_expr_1244_ = lean_ctor_get(v_expr_1228_, 1);
lean_inc_ref(v_expr_1244_);
lean_dec_ref_known(v_expr_1228_, 2);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v_expr_1244_);
v___x_1246_ = v___x_1242_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_expr_1244_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_pos_1229_);
v___x_1246_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
v_before_1205_ = v___x_1246_;
goto _start;
}
}
}
case 5:
{
switch(lean_obj_tag(v_expr_1230_))
{
case 10:
{
lean_object* v_expr_1252_; 
lean_inc_ref(v_expr_1230_);
lean_inc(v_pos_1231_);
lean_dec_ref(v_after_1206_);
v_expr_1252_ = lean_ctor_get(v_expr_1230_, 1);
lean_inc_ref(v_expr_1252_);
lean_dec_ref_known(v_expr_1230_, 2);
v_e_u2081_1233_ = v_expr_1252_;
v___y_1234_ = v_a_1207_;
v___y_1235_ = v_a_1208_;
v___y_1236_ = v_a_1209_;
v___y_1237_ = v_a_1210_;
goto v___jp_1232_;
}
case 5:
{
lean_object* v_dummy_1253_; lean_object* v_nargs_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v_fst_1259_; lean_object* v_snd_1260_; lean_object* v_nargs_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v_fst_1265_; lean_object* v_snd_1266_; uint8_t v___x_1267_; 
v_dummy_1253_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0, &l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0);
v_nargs_1254_ = l_Lean_Expr_getAppNumArgs(v_expr_1230_);
lean_inc(v_nargs_1254_);
v___x_1255_ = lean_mk_array(v_nargs_1254_, v_dummy_1253_);
v___x_1256_ = lean_unsigned_to_nat(1u);
v___x_1257_ = lean_nat_sub(v_nargs_1254_, v___x_1256_);
lean_dec(v_nargs_1254_);
lean_inc_ref(v_expr_1230_);
v___x_1258_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(v_expr_1230_, v___x_1255_, v___x_1257_);
v_fst_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_fst_1259_);
v_snd_1260_ = lean_ctor_get(v___x_1258_, 1);
lean_inc(v_snd_1260_);
lean_dec_ref(v___x_1258_);
v_nargs_1261_ = l_Lean_Expr_getAppNumArgs(v_expr_1228_);
lean_inc(v_nargs_1261_);
v___x_1262_ = lean_mk_array(v_nargs_1261_, v_dummy_1253_);
v___x_1263_ = lean_nat_sub(v_nargs_1261_, v___x_1256_);
lean_dec(v_nargs_1261_);
lean_inc_ref(v_expr_1228_);
v___x_1264_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(v_expr_1228_, v___x_1262_, v___x_1263_);
v_fst_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_fst_1265_);
v_snd_1266_ = lean_ctor_get(v___x_1264_, 1);
lean_inc(v_snd_1266_);
lean_dec_ref(v___x_1264_);
v___x_1267_ = lean_expr_eqv(v_fst_1259_, v_fst_1265_);
lean_dec(v_fst_1265_);
lean_dec(v_fst_1259_);
if (v___x_1267_ == 0)
{
lean_dec(v_snd_1266_);
lean_dec(v_snd_1260_);
goto v___jp_1220_;
}
else
{
if (v___x_1240_ == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1268_ = lean_array_get_size(v_snd_1260_);
v___x_1269_ = lean_array_get_size(v_snd_1266_);
v___x_1270_ = lean_nat_dec_eq(v___x_1268_, v___x_1269_);
if (v___x_1270_ == 0)
{
lean_dec(v_snd_1266_);
lean_dec(v_snd_1260_);
goto v___jp_1220_;
}
else
{
if (v___x_1240_ == 0)
{
lean_object* v_args_1271_; size_t v_sz_1272_; size_t v___x_1273_; lean_object* v___x_1274_; 
v_args_1271_ = l_Array_zip___redArg(v_snd_1260_, v_snd_1266_);
lean_dec(v_snd_1266_);
v_sz_1272_ = lean_array_size(v_args_1271_);
v___x_1273_ = ((size_t)0ULL);
v___x_1274_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_1260_, v_before_1205_, v_after_1206_, v_sz_1272_, v___x_1273_, v_args_1271_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
lean_dec_ref(v_after_1206_);
lean_dec_ref(v_before_1205_);
lean_dec(v_snd_1260_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1300_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1277_ = v___x_1274_;
v_isShared_1278_ = v_isSharedCheck_1300_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1274_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1300_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1279_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___x_1280_ = lean_unsigned_to_nat(0u);
v___x_1281_ = lean_array_get_size(v_a_1275_);
v___x_1282_ = lean_nat_dec_lt(v___x_1280_, v___x_1281_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1284_; 
lean_dec(v_a_1275_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v___x_1279_);
v___x_1284_ = v___x_1277_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1279_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
else
{
uint8_t v___x_1286_; 
v___x_1286_ = lean_nat_dec_le(v___x_1281_, v___x_1281_);
if (v___x_1286_ == 0)
{
if (v___x_1282_ == 0)
{
lean_object* v___x_1288_; 
lean_dec(v_a_1275_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v___x_1279_);
v___x_1288_ = v___x_1277_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1279_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
else
{
size_t v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
v___x_1290_ = lean_usize_of_nat(v___x_1281_);
v___x_1291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_a_1275_, v___x_1273_, v___x_1290_, v___x_1279_);
lean_dec(v_a_1275_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v___x_1291_);
v___x_1293_ = v___x_1277_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
else
{
size_t v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1298_; 
v___x_1295_ = lean_usize_of_nat(v___x_1281_);
v___x_1296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_a_1275_, v___x_1273_, v___x_1295_, v___x_1279_);
lean_dec(v_a_1275_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v___x_1296_);
v___x_1298_ = v___x_1277_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1296_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
v_a_1301_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1274_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1274_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1301_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
else
{
lean_dec(v_snd_1266_);
lean_dec(v_snd_1260_);
goto v___jp_1220_;
}
}
}
else
{
lean_dec(v_snd_1266_);
lean_dec(v_snd_1260_);
goto v___jp_1220_;
}
}
}
default: 
{
goto v___jp_1224_;
}
}
}
case 7:
{
if (lean_obj_tag(v_expr_1230_) == 10)
{
lean_object* v_expr_1309_; 
lean_inc_ref(v_expr_1230_);
lean_inc(v_pos_1231_);
lean_dec_ref(v_after_1206_);
v_expr_1309_ = lean_ctor_get(v_expr_1230_, 1);
lean_inc_ref(v_expr_1309_);
lean_dec_ref_known(v_expr_1230_, 2);
v_e_u2081_1233_ = v_expr_1309_;
v___y_1234_ = v_a_1207_;
v___y_1235_ = v_a_1208_;
v___y_1236_ = v_a_1209_;
v___y_1237_ = v_a_1210_;
goto v___jp_1232_;
}
else
{
lean_object* v___x_1310_; 
v___x_1310_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(v_before_1205_, v_after_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
return v___x_1310_;
}
}
case 6:
{
switch(lean_obj_tag(v_expr_1230_))
{
case 10:
{
lean_object* v_expr_1311_; 
lean_inc_ref(v_expr_1230_);
lean_inc(v_pos_1231_);
lean_dec_ref(v_after_1206_);
v_expr_1311_ = lean_ctor_get(v_expr_1230_, 1);
lean_inc_ref(v_expr_1311_);
lean_dec_ref_known(v_expr_1230_, 2);
v_e_u2081_1233_ = v_expr_1311_;
v___y_1234_ = v_a_1207_;
v___y_1235_ = v_a_1208_;
v___y_1236_ = v_a_1209_;
v___y_1237_ = v_a_1210_;
goto v___jp_1232_;
}
case 6:
{
lean_object* v_binderName_1312_; lean_object* v_binderType_1313_; lean_object* v_body_1314_; uint8_t v_binderInfo_1315_; lean_object* v_binderName_1316_; lean_object* v_binderType_1317_; lean_object* v_body_1318_; uint8_t v_binderInfo_1319_; uint8_t v___x_1320_; 
v_binderName_1312_ = lean_ctor_get(v_expr_1228_, 0);
v_binderType_1313_ = lean_ctor_get(v_expr_1228_, 1);
v_body_1314_ = lean_ctor_get(v_expr_1228_, 2);
v_binderInfo_1315_ = lean_ctor_get_uint8(v_expr_1228_, sizeof(void*)*3 + 8);
v_binderName_1316_ = lean_ctor_get(v_expr_1230_, 0);
v_binderType_1317_ = lean_ctor_get(v_expr_1230_, 1);
v_body_1318_ = lean_ctor_get(v_expr_1230_, 2);
v_binderInfo_1319_ = lean_ctor_get_uint8(v_expr_1230_, sizeof(void*)*3 + 8);
v___x_1320_ = lean_name_eq(v_binderName_1312_, v_binderName_1316_);
if (v___x_1320_ == 0)
{
goto v___jp_1216_;
}
else
{
if (v___x_1240_ == 0)
{
uint8_t v___x_1321_; 
v___x_1321_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1315_, v_binderInfo_1319_);
if (v___x_1321_ == 0)
{
goto v___jp_1216_;
}
else
{
if (v___x_1240_ == 0)
{
lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1371_; 
lean_inc_ref(v_body_1318_);
lean_inc_ref(v_binderType_1317_);
lean_inc_ref(v_body_1314_);
lean_inc_ref(v_binderType_1313_);
lean_inc(v_pos_1231_);
lean_inc(v_pos_1229_);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_before_1205_);
if (v_isSharedCheck_1371_ == 0)
{
lean_object* v_unused_1372_; lean_object* v_unused_1373_; 
v_unused_1372_ = lean_ctor_get(v_before_1205_, 1);
lean_dec(v_unused_1372_);
v_unused_1373_ = lean_ctor_get(v_before_1205_, 0);
lean_dec(v_unused_1373_);
v___x_1323_ = v_before_1205_;
v_isShared_1324_ = v_isSharedCheck_1371_;
goto v_resetjp_1322_;
}
else
{
lean_dec(v_before_1205_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1371_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1368_; 
v_isSharedCheck_1368_ = !lean_is_exclusive(v_after_1206_);
if (v_isSharedCheck_1368_ == 0)
{
lean_object* v_unused_1369_; lean_object* v_unused_1370_; 
v_unused_1369_ = lean_ctor_get(v_after_1206_, 1);
lean_dec(v_unused_1369_);
v_unused_1370_ = lean_ctor_get(v_after_1206_, 0);
lean_dec(v_unused_1370_);
v___x_1326_ = v_after_1206_;
v_isShared_1327_ = v_isSharedCheck_1368_;
goto v_resetjp_1325_;
}
else
{
lean_dec(v_after_1206_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1368_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1328_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1229_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 1, v___x_1328_);
lean_ctor_set(v___x_1326_, 0, v_binderType_1313_);
v___x_1330_ = v___x_1326_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_binderType_1313_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
lean_object* v___x_1331_; lean_object* v___x_1333_; 
v___x_1331_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1231_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 1, v___x_1331_);
lean_ctor_set(v___x_1323_, 0, v_binderType_1317_);
v___x_1333_ = v___x_1323_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_binderType_1317_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1334_; 
v___x_1334_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1330_, v___x_1333_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1365_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1337_ = v___x_1334_;
v_isShared_1338_ = v_isSharedCheck_1365_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1334_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1365_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
uint8_t v___x_1339_; 
v___x_1339_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_a_1335_);
if (v___x_1339_ == 0)
{
lean_object* v_changesBefore_1340_; lean_object* v_changesAfter_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; lean_object* v___x_1345_; lean_object* v_changesBefore_1346_; lean_object* v_changesAfter_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1359_; 
lean_dec_ref(v_body_1318_);
lean_dec_ref(v_body_1314_);
v_changesBefore_1340_ = lean_ctor_get(v_a_1335_, 0);
lean_inc(v_changesBefore_1340_);
v_changesAfter_1341_ = lean_ctor_get(v_a_1335_, 1);
lean_inc(v_changesAfter_1341_);
lean_dec(v_a_1335_);
v___x_1342_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1229_);
lean_dec(v_pos_1229_);
v___x_1343_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1231_);
lean_dec(v_pos_1231_);
v___x_1344_ = 0;
v___x_1345_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v___x_1342_, v___x_1343_, v___x_1344_);
v_changesBefore_1346_ = lean_ctor_get(v___x_1345_, 0);
v_changesAfter_1347_ = lean_ctor_get(v___x_1345_, 1);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1349_ = v___x_1345_;
v_isShared_1350_ = v_isSharedCheck_1359_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_changesAfter_1347_);
lean_inc(v_changesBefore_1346_);
lean_dec(v___x_1345_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1359_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1351_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesBefore_1340_, v_changesBefore_1346_);
v___x_1352_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesAfter_1341_, v_changesAfter_1347_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 1, v___x_1352_);
lean_ctor_set(v___x_1349_, 0, v___x_1351_);
v___x_1354_ = v___x_1349_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1351_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1356_; 
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v___x_1354_);
v___x_1356_ = v___x_1337_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
else
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
lean_del_object(v___x_1337_);
lean_dec(v_a_1335_);
v___x_1360_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1229_);
lean_dec(v_pos_1229_);
v___x_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1361_, 0, v_body_1314_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
v___x_1362_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1231_);
lean_dec(v_pos_1231_);
v___x_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1363_, 0, v_body_1318_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
v_before_1205_ = v___x_1361_;
v_after_1206_ = v___x_1363_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_body_1318_);
lean_dec_ref(v_body_1314_);
lean_dec(v_pos_1231_);
lean_dec(v_pos_1229_);
return v___x_1334_;
}
}
}
}
}
}
else
{
goto v___jp_1216_;
}
}
}
else
{
goto v___jp_1216_;
}
}
}
default: 
{
goto v___jp_1224_;
}
}
}
case 11:
{
switch(lean_obj_tag(v_expr_1230_))
{
case 10:
{
lean_object* v_expr_1374_; 
lean_inc_ref(v_expr_1230_);
lean_inc(v_pos_1231_);
lean_dec_ref(v_after_1206_);
v_expr_1374_ = lean_ctor_get(v_expr_1230_, 1);
lean_inc_ref(v_expr_1374_);
lean_dec_ref_known(v_expr_1230_, 2);
v_e_u2081_1233_ = v_expr_1374_;
v___y_1234_ = v_a_1207_;
v___y_1235_ = v_a_1208_;
v___y_1236_ = v_a_1209_;
v___y_1237_ = v_a_1210_;
goto v___jp_1232_;
}
case 11:
{
lean_object* v_typeName_1375_; lean_object* v_idx_1376_; lean_object* v_struct_1377_; lean_object* v_typeName_1378_; lean_object* v_idx_1379_; lean_object* v_struct_1380_; uint8_t v___x_1381_; 
v_typeName_1375_ = lean_ctor_get(v_expr_1228_, 0);
v_idx_1376_ = lean_ctor_get(v_expr_1228_, 1);
v_struct_1377_ = lean_ctor_get(v_expr_1228_, 2);
v_typeName_1378_ = lean_ctor_get(v_expr_1230_, 0);
v_idx_1379_ = lean_ctor_get(v_expr_1230_, 1);
v_struct_1380_ = lean_ctor_get(v_expr_1230_, 2);
v___x_1381_ = lean_name_eq(v_typeName_1375_, v_typeName_1378_);
if (v___x_1381_ == 0)
{
goto v___jp_1212_;
}
else
{
if (v___x_1240_ == 0)
{
uint8_t v___x_1382_; 
v___x_1382_ = lean_nat_dec_eq(v_idx_1376_, v_idx_1379_);
if (v___x_1382_ == 0)
{
goto v___jp_1212_;
}
else
{
if (v___x_1240_ == 0)
{
lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1401_; 
lean_inc_ref(v_struct_1380_);
lean_inc_ref(v_struct_1377_);
lean_inc(v_pos_1231_);
lean_inc(v_pos_1229_);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_before_1205_);
if (v_isSharedCheck_1401_ == 0)
{
lean_object* v_unused_1402_; lean_object* v_unused_1403_; 
v_unused_1402_ = lean_ctor_get(v_before_1205_, 1);
lean_dec(v_unused_1402_);
v_unused_1403_ = lean_ctor_get(v_before_1205_, 0);
lean_dec(v_unused_1403_);
v___x_1384_ = v_before_1205_;
v_isShared_1385_ = v_isSharedCheck_1401_;
goto v_resetjp_1383_;
}
else
{
lean_dec(v_before_1205_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1401_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1398_; 
v_isSharedCheck_1398_ = !lean_is_exclusive(v_after_1206_);
if (v_isSharedCheck_1398_ == 0)
{
lean_object* v_unused_1399_; lean_object* v_unused_1400_; 
v_unused_1399_ = lean_ctor_get(v_after_1206_, 1);
lean_dec(v_unused_1399_);
v_unused_1400_ = lean_ctor_get(v_after_1206_, 0);
lean_dec(v_unused_1400_);
v___x_1387_ = v_after_1206_;
v_isShared_1388_ = v_isSharedCheck_1398_;
goto v_resetjp_1386_;
}
else
{
lean_dec(v_after_1206_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1398_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v___x_1391_; 
v___x_1389_ = l_Lean_SubExpr_Pos_pushProj(v_pos_1229_);
lean_dec(v_pos_1229_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 1, v___x_1389_);
lean_ctor_set(v___x_1387_, 0, v_struct_1377_);
v___x_1391_ = v___x_1387_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_struct_1377_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1392_; lean_object* v___x_1394_; 
v___x_1392_ = l_Lean_SubExpr_Pos_pushProj(v_pos_1231_);
lean_dec(v_pos_1231_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 1, v___x_1392_);
lean_ctor_set(v___x_1384_, 0, v_struct_1380_);
v___x_1394_ = v___x_1384_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_struct_1380_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v___x_1392_);
v___x_1394_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
v_before_1205_ = v___x_1391_;
v_after_1206_ = v___x_1394_;
goto _start;
}
}
}
}
}
else
{
goto v___jp_1212_;
}
}
}
else
{
goto v___jp_1212_;
}
}
}
default: 
{
goto v___jp_1224_;
}
}
}
default: 
{
if (lean_obj_tag(v_expr_1230_) == 10)
{
lean_object* v_expr_1404_; 
lean_inc_ref(v_expr_1230_);
lean_inc(v_pos_1231_);
lean_dec_ref(v_after_1206_);
v_expr_1404_ = lean_ctor_get(v_expr_1230_, 1);
lean_inc_ref(v_expr_1404_);
lean_dec_ref_known(v_expr_1230_, 2);
v_e_u2081_1233_ = v_expr_1404_;
v___y_1234_ = v_a_1207_;
v___y_1235_ = v_a_1208_;
v___y_1236_ = v_a_1209_;
v___y_1237_ = v_a_1210_;
goto v___jp_1232_;
}
else
{
goto v___jp_1224_;
}
}
}
}
else
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
lean_dec_ref(v_after_1206_);
lean_dec_ref(v_before_1205_);
v___x_1405_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___x_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
return v___x_1406_;
}
v___jp_1212_:
{
uint8_t v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1213_ = 0;
v___x_1214_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1205_, v_after_1206_, v___x_1213_);
v___x_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
return v___x_1215_;
}
v___jp_1216_:
{
uint8_t v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1217_ = 0;
v___x_1218_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1205_, v_after_1206_, v___x_1217_);
v___x_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
return v___x_1219_;
}
v___jp_1220_:
{
uint8_t v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1221_ = 0;
v___x_1222_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1205_, v_after_1206_, v___x_1221_);
v___x_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
return v___x_1223_;
}
v___jp_1224_:
{
uint8_t v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1225_ = 0;
v___x_1226_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1205_, v_after_1206_, v___x_1225_);
v___x_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
return v___x_1227_;
}
v___jp_1232_:
{
lean_object* v___x_1238_; 
v___x_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1238_, 0, v_e_u2081_1233_);
lean_ctor_set(v___x_1238_, 1, v_pos_1231_);
v_after_1206_ = v___x_1238_;
v_a_1207_ = v___y_1234_;
v_a_1208_ = v___y_1235_;
v_a_1209_ = v___y_1236_;
v_a_1210_ = v___y_1237_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0(lean_object* v_body_1407_, lean_object* v_pos_1408_, lean_object* v_body_1409_, lean_object* v_pos_1410_, lean_object* v_x_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1417_ = lean_expr_instantiate1(v_body_1407_, v_x_1411_);
v___x_1418_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1408_);
v___x_1419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1417_);
lean_ctor_set(v___x_1419_, 1, v___x_1418_);
v___x_1420_ = lean_expr_instantiate1(v_body_1409_, v_x_1411_);
v___x_1421_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1410_);
v___x_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1420_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
v___x_1423_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1419_, v___x_1422_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg___boxed(lean_object* v_snd_1424_, lean_object* v_before_1425_, lean_object* v_after_1426_, lean_object* v_sz_1427_, lean_object* v_i_1428_, lean_object* v_bs_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
size_t v_sz_boxed_1435_; size_t v_i_boxed_1436_; lean_object* v_res_1437_; 
v_sz_boxed_1435_ = lean_unbox_usize(v_sz_1427_);
lean_dec(v_sz_1427_);
v_i_boxed_1436_ = lean_unbox_usize(v_i_1428_);
lean_dec(v_i_1428_);
v_res_1437_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_1424_, v_before_1425_, v_after_1426_, v_sz_boxed_1435_, v_i_boxed_1436_, v_bs_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec_ref(v_after_1426_);
lean_dec_ref(v_before_1425_);
lean_dec_ref(v_snd_1424_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___boxed(lean_object* v_before_1438_, lean_object* v_after_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(v_before_1438_, v_after_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_);
lean_dec(v_a_1443_);
lean_dec_ref(v_a_1442_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___boxed(lean_object* v_before_1446_, lean_object* v_after_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v_before_1446_, v_after_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_);
lean_dec(v_a_1451_);
lean_dec_ref(v_a_1450_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1(lean_object* v_upperBound_1454_, lean_object* v_before_1455_, lean_object* v_inst_1456_, lean_object* v_R_1457_, lean_object* v_a_1458_, lean_object* v_b_1459_, lean_object* v_c_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v_upperBound_1454_, v_before_1455_, v_a_1458_, v_b_1459_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___boxed(lean_object* v_upperBound_1467_, lean_object* v_before_1468_, lean_object* v_inst_1469_, lean_object* v_R_1470_, lean_object* v_a_1471_, lean_object* v_b_1472_, lean_object* v_c_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1(v_upperBound_1467_, v_before_1468_, v_inst_1469_, v_R_1470_, v_a_1471_, v_b_1472_, v_c_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v_upperBound_1467_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3(lean_object* v_00_u03b1_1480_, lean_object* v_msg_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v_msg_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___boxed(lean_object* v_00_u03b1_1488_, lean_object* v_msg_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3(v_00_u03b1_1488_, v_msg_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4(uint8_t v_b_u2082_1496_, lean_object* v_k_1497_, lean_object* v_t_1498_, lean_object* v_hl_1499_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_1496_, v_k_1497_, v_t_1498_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___boxed(lean_object* v_b_u2082_1501_, lean_object* v_k_1502_, lean_object* v_t_1503_, lean_object* v_hl_1504_){
_start:
{
uint8_t v_b_u2082_boxed_1505_; lean_object* v_res_1506_; 
v_b_u2082_boxed_1505_ = lean_unbox(v_b_u2082_1501_);
v_res_1506_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4(v_b_u2082_boxed_1505_, v_k_1502_, v_t_1503_, v_hl_1504_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5(lean_object* v_init_1507_, lean_object* v_t_1508_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_init_1507_, v_t_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9(lean_object* v_snd_1510_, lean_object* v_before_1511_, lean_object* v_after_1512_, lean_object* v_as_1513_, size_t v_sz_1514_, size_t v_i_1515_, lean_object* v_bs_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_1510_, v_before_1511_, v_after_1512_, v_sz_1514_, v_i_1515_, v_bs_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___boxed(lean_object* v_snd_1523_, lean_object* v_before_1524_, lean_object* v_after_1525_, lean_object* v_as_1526_, lean_object* v_sz_1527_, lean_object* v_i_1528_, lean_object* v_bs_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
size_t v_sz_boxed_1535_; size_t v_i_boxed_1536_; lean_object* v_res_1537_; 
v_sz_boxed_1535_ = lean_unbox_usize(v_sz_1527_);
lean_dec(v_sz_1527_);
v_i_boxed_1536_ = lean_unbox_usize(v_i_1528_);
lean_dec(v_i_1528_);
v_res_1537_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9(v_snd_1523_, v_before_1524_, v_after_1525_, v_as_1526_, v_sz_boxed_1535_, v_i_boxed_1536_, v_bs_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec_ref(v_as_1526_);
lean_dec_ref(v_after_1525_);
lean_dec_ref(v_before_1524_);
lean_dec_ref(v_snd_1523_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(lean_object* v_e_u2080_1538_, lean_object* v_e_u2081_1539_, uint8_t v_useAfter_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v___x_1546_; lean_object* v_s_u2080_1547_; lean_object* v_s_u2081_1548_; 
v___x_1546_ = l_Lean_SubExpr_Pos_root;
v_s_u2080_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_u2080_1547_, 0, v_e_u2080_1538_);
lean_ctor_set(v_s_u2080_1547_, 1, v___x_1546_);
v_s_u2081_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_u2081_1548_, 0, v_e_u2081_1539_);
lean_ctor_set(v_s_u2081_1548_, 1, v___x_1546_);
if (v_useAfter_1540_ == 0)
{
lean_object* v___x_1549_; 
v___x_1549_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v_s_u2081_1548_, v_s_u2080_1547_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_);
return v___x_1549_;
}
else
{
lean_object* v___x_1550_; 
v___x_1550_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v_s_u2080_1547_, v_s_u2081_1548_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_);
return v___x_1550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff___boxed(lean_object* v_e_u2080_1551_, lean_object* v_e_u2081_1552_, lean_object* v_useAfter_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
uint8_t v_useAfter_boxed_1559_; lean_object* v_res_1560_; 
v_useAfter_boxed_1559_ = lean_unbox(v_useAfter_1553_);
v_res_1560_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(v_e_u2080_1551_, v_e_u2081_1552_, v_useAfter_boxed_1559_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
lean_dec(v_a_1555_);
lean_dec_ref(v_a_1554_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0(uint8_t v_useAfter_1561_, lean_object* v_info_1562_, uint8_t v_d_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
uint8_t v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1569_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag(v_useAfter_1561_, v_d_1563_);
v___x_1570_ = l_Lean_Widget_SubexprInfo_withDiffTag(v___x_1569_, v_info_1562_);
v___x_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0___boxed(lean_object* v_useAfter_1572_, lean_object* v_info_1573_, lean_object* v_d_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
uint8_t v_useAfter_boxed_1580_; uint8_t v_d_boxed_1581_; lean_object* v_res_1582_; 
v_useAfter_boxed_1580_ = lean_unbox(v_useAfter_1572_);
v_d_boxed_1581_ = lean_unbox(v_d_1574_);
v_res_1582_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0(v_useAfter_boxed_1580_, v_info_1573_, v_d_boxed_1581_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(lean_object* v_f_1583_, lean_object* v_x_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
switch(lean_obj_tag(v_x_1584_))
{
case 0:
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1598_; 
lean_dec_ref(v_f_1583_);
v_a_1590_ = lean_ctor_get(v_x_1584_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v_x_1584_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1592_ = v_x_1584_;
v_isShared_1593_ = v_isSharedCheck_1598_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v_x_1584_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1598_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1596_; 
v___x_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
return v___x_1596_;
}
}
}
case 1:
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1625_; 
v_a_1599_ = lean_ctor_get(v_x_1584_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v_x_1584_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1601_ = v_x_1584_;
v_isShared_1602_ = v_isSharedCheck_1625_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v_x_1584_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1625_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
size_t v_sz_1603_; size_t v___x_1604_; lean_object* v___x_1605_; 
v_sz_1603_ = lean_array_size(v_a_1599_);
v___x_1604_ = ((size_t)0ULL);
v___x_1605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_1583_, v_sz_1603_, v___x_1604_, v_a_1599_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1616_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1608_ = v___x_1605_;
v_isShared_1609_ = v_isSharedCheck_1616_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1605_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1616_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v_a_1606_);
v___x_1611_ = v___x_1601_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1606_);
v___x_1611_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1613_; 
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 0, v___x_1611_);
v___x_1613_ = v___x_1608_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1611_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
lean_del_object(v___x_1601_);
v_a_1617_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1605_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1605_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
}
default: 
{
lean_object* v_a_1626_; lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1653_; 
v_a_1626_ = lean_ctor_get(v_x_1584_, 0);
v_a_1627_ = lean_ctor_get(v_x_1584_, 1);
v_isSharedCheck_1653_ = !lean_is_exclusive(v_x_1584_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1629_ = v_x_1584_;
v_isShared_1630_ = v_isSharedCheck_1653_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_inc(v_a_1626_);
lean_dec(v_x_1584_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1653_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1631_; 
lean_inc_ref(v_f_1583_);
lean_inc(v___y_1588_);
lean_inc_ref(v___y_1587_);
lean_inc(v___y_1586_);
lean_inc_ref(v___y_1585_);
v___x_1631_ = lean_apply_6(v_f_1583_, v_a_1626_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, lean_box(0));
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v___x_1633_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_a_1632_);
lean_dec_ref_known(v___x_1631_, 1);
v___x_1633_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1583_, v_a_1627_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1644_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1636_ = v___x_1633_;
v_isShared_1637_ = v_isSharedCheck_1644_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1633_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1644_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 1, v_a_1634_);
lean_ctor_set(v___x_1629_, 0, v_a_1632_);
v___x_1639_ = v___x_1629_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1632_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_a_1634_);
v___x_1639_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
lean_object* v___x_1641_; 
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v___x_1639_);
v___x_1641_ = v___x_1636_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
else
{
lean_dec(v_a_1632_);
lean_del_object(v___x_1629_);
return v___x_1633_;
}
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
lean_del_object(v___x_1629_);
lean_dec_ref(v_a_1627_);
lean_dec_ref(v_f_1583_);
v_a_1645_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1631_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1631_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(lean_object* v_f_1654_, size_t v_sz_1655_, size_t v_i_1656_, lean_object* v_bs_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
uint8_t v___x_1663_; 
v___x_1663_ = lean_usize_dec_lt(v_i_1656_, v_sz_1655_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; 
lean_dec_ref(v_f_1654_);
v___x_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1664_, 0, v_bs_1657_);
return v___x_1664_;
}
else
{
lean_object* v_v_1665_; lean_object* v___x_1666_; 
v_v_1665_ = lean_array_uget_borrowed(v_bs_1657_, v_i_1656_);
lean_inc(v_v_1665_);
lean_inc_ref(v_f_1654_);
v___x_1666_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1654_, v_v_1665_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v___x_1668_; lean_object* v_bs_x27_1669_; size_t v___x_1670_; size_t v___x_1671_; lean_object* v___x_1672_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_a_1667_);
lean_dec_ref_known(v___x_1666_, 1);
v___x_1668_ = lean_unsigned_to_nat(0u);
v_bs_x27_1669_ = lean_array_uset(v_bs_1657_, v_i_1656_, v___x_1668_);
v___x_1670_ = ((size_t)1ULL);
v___x_1671_ = lean_usize_add(v_i_1656_, v___x_1670_);
v___x_1672_ = lean_array_uset(v_bs_x27_1669_, v_i_1656_, v_a_1667_);
v_i_1656_ = v___x_1671_;
v_bs_1657_ = v___x_1672_;
goto _start;
}
else
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
lean_dec_ref(v_bs_1657_);
lean_dec_ref(v_f_1654_);
v_a_1674_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1666_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1666_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_1682_, lean_object* v_sz_1683_, lean_object* v_i_1684_, lean_object* v_bs_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
size_t v_sz_boxed_1691_; size_t v_i_boxed_1692_; lean_object* v_res_1693_; 
v_sz_boxed_1691_ = lean_unbox_usize(v_sz_1683_);
lean_dec(v_sz_1683_);
v_i_boxed_1692_ = lean_unbox_usize(v_i_1684_);
lean_dec(v_i_1684_);
v_res_1693_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_1682_, v_sz_boxed_1691_, v_i_boxed_1692_, v_bs_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg___boxed(lean_object* v_f_1694_, lean_object* v_x_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1694_, v_x_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(lean_object* v_t_1702_, lean_object* v_k_1703_){
_start:
{
if (lean_obj_tag(v_t_1702_) == 0)
{
lean_object* v_k_1704_; lean_object* v_v_1705_; lean_object* v_l_1706_; lean_object* v_r_1707_; uint8_t v___x_1708_; 
v_k_1704_ = lean_ctor_get(v_t_1702_, 1);
v_v_1705_ = lean_ctor_get(v_t_1702_, 2);
v_l_1706_ = lean_ctor_get(v_t_1702_, 3);
v_r_1707_ = lean_ctor_get(v_t_1702_, 4);
v___x_1708_ = lean_nat_dec_lt(v_k_1703_, v_k_1704_);
if (v___x_1708_ == 0)
{
uint8_t v___x_1709_; 
v___x_1709_ = lean_nat_dec_eq(v_k_1703_, v_k_1704_);
if (v___x_1709_ == 0)
{
v_t_1702_ = v_r_1707_;
goto _start;
}
else
{
lean_object* v___x_1711_; 
lean_inc(v_v_1705_);
v___x_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1711_, 0, v_v_1705_);
return v___x_1711_;
}
}
else
{
v_t_1702_ = v_l_1706_;
goto _start;
}
}
else
{
lean_object* v___x_1713_; 
v___x_1713_ = lean_box(0);
return v___x_1713_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg___boxed(lean_object* v_t_1714_, lean_object* v_k_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_t_1714_, v_k_1715_);
lean_dec(v_k_1715_);
lean_dec(v_t_1714_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0(lean_object* v_pm_1717_, lean_object* v_merger_1718_, lean_object* v_info_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_subexprPos_1725_; lean_object* v___x_1726_; 
v_subexprPos_1725_ = lean_ctor_get(v_info_1719_, 1);
v___x_1726_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_pm_1717_, v_subexprPos_1725_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v___x_1727_; 
lean_dec_ref(v_merger_1718_);
v___x_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1727_, 0, v_info_1719_);
return v___x_1727_;
}
else
{
lean_object* v_val_1728_; lean_object* v___x_1729_; 
v_val_1728_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_val_1728_);
lean_dec_ref_known(v___x_1726_, 1);
lean_inc(v___y_1723_);
lean_inc_ref(v___y_1722_);
lean_inc(v___y_1721_);
lean_inc_ref(v___y_1720_);
v___x_1729_ = lean_apply_7(v_merger_1718_, v_info_1719_, v_val_1728_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, lean_box(0));
return v___x_1729_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0___boxed(lean_object* v_pm_1730_, lean_object* v_merger_1731_, lean_object* v_info_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0(v_pm_1730_, v_merger_1731_, v_info_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v_pm_1730_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(lean_object* v_merger_1739_, lean_object* v_pm_1740_, lean_object* v_tt_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
if (lean_obj_tag(v_pm_1740_) == 0)
{
lean_object* v___f_1747_; lean_object* v___x_1748_; 
v___f_1747_ = lean_alloc_closure((void*)(l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1747_, 0, v_pm_1740_);
lean_closure_set(v___f_1747_, 1, v_merger_1739_);
v___x_1748_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v___f_1747_, v_tt_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
return v___x_1748_;
}
else
{
lean_object* v___x_1749_; 
lean_dec_ref(v_merger_1739_);
v___x_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1749_, 0, v_tt_1741_);
return v___x_1749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___boxed(lean_object* v_merger_1750_, lean_object* v_pm_1751_, lean_object* v_tt_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v_merger_1750_, v_pm_1751_, v_tt_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(uint8_t v_useAfter_1759_, lean_object* v_diff_1760_, lean_object* v_info_u2081_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_){
_start:
{
lean_object* v___x_1767_; lean_object* v___f_1768_; 
v___x_1767_ = lean_box(v_useAfter_1759_);
v___f_1768_ = lean_alloc_closure((void*)(l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1768_, 0, v___x_1767_);
if (v_useAfter_1759_ == 0)
{
lean_object* v_changesBefore_1769_; lean_object* v___x_1770_; 
v_changesBefore_1769_ = lean_ctor_get(v_diff_1760_, 0);
lean_inc(v_changesBefore_1769_);
lean_dec_ref(v_diff_1760_);
v___x_1770_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v___f_1768_, v_changesBefore_1769_, v_info_u2081_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_);
return v___x_1770_;
}
else
{
lean_object* v_changesAfter_1771_; lean_object* v___x_1772_; 
v_changesAfter_1771_ = lean_ctor_get(v_diff_1760_, 1);
lean_inc(v_changesAfter_1771_);
lean_dec_ref(v_diff_1760_);
v___x_1772_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v___f_1768_, v_changesAfter_1771_, v_info_u2081_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_);
return v___x_1772_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___boxed(lean_object* v_useAfter_1773_, lean_object* v_diff_1774_, lean_object* v_info_u2081_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_){
_start:
{
uint8_t v_useAfter_boxed_1781_; lean_object* v_res_1782_; 
v_useAfter_boxed_1781_ = lean_unbox(v_useAfter_1773_);
v_res_1782_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(v_useAfter_boxed_1781_, v_diff_1774_, v_info_u2081_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_);
lean_dec(v_a_1779_);
lean_dec_ref(v_a_1778_);
lean_dec(v_a_1777_);
lean_dec_ref(v_a_1776_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0(lean_object* v_00_u03b1_1783_, lean_object* v_merger_1784_, lean_object* v_pm_1785_, lean_object* v_tt_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v_merger_1784_, v_pm_1785_, v_tt_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___boxed(lean_object* v_00_u03b1_1793_, lean_object* v_merger_1794_, lean_object* v_pm_1795_, lean_object* v_tt_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0(v_00_u03b1_1793_, v_merger_1794_, v_pm_1795_, v_tt_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0(lean_object* v_00_u03b4_1803_, lean_object* v_t_1804_, lean_object* v_k_1805_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_t_1804_, v_k_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___boxed(lean_object* v_00_u03b4_1807_, lean_object* v_t_1808_, lean_object* v_k_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0(v_00_u03b4_1807_, v_t_1808_, v_k_1809_);
lean_dec(v_k_1809_);
lean_dec(v_t_1808_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1(lean_object* v_00_u03b1_1811_, lean_object* v_00_u03b2_1812_, lean_object* v_f_1813_, lean_object* v_x_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1813_, v_x_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1821_, lean_object* v_00_u03b2_1822_, lean_object* v_f_1823_, lean_object* v_x_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1(v_00_u03b1_1821_, v_00_u03b2_1822_, v_f_1823_, v_x_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1831_, lean_object* v_00_u03b2_1832_, lean_object* v_f_1833_, size_t v_sz_1834_, size_t v_i_1835_, lean_object* v_bs_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v___x_1842_; 
v___x_1842_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_1833_, v_sz_1834_, v_i_1835_, v_bs_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1843_, lean_object* v_00_u03b2_1844_, lean_object* v_f_1845_, lean_object* v_sz_1846_, lean_object* v_i_1847_, lean_object* v_bs_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
size_t v_sz_boxed_1854_; size_t v_i_boxed_1855_; lean_object* v_res_1856_; 
v_sz_boxed_1854_ = lean_unbox_usize(v_sz_1846_);
lean_dec(v_sz_1846_);
v_i_boxed_1855_ = lean_unbox_usize(v_i_1847_);
lean_dec(v_i_1847_);
v_res_1856_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2(v_00_u03b1_1843_, v_00_u03b2_1844_, v_f_1845_, v_sz_boxed_1854_, v_i_boxed_1855_, v_bs_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(lean_object* v_e_1857_, lean_object* v___y_1858_){
_start:
{
uint8_t v___x_1860_; 
v___x_1860_ = l_Lean_Expr_hasMVar(v_e_1857_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1861_; 
v___x_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1861_, 0, v_e_1857_);
return v___x_1861_;
}
else
{
lean_object* v___x_1862_; lean_object* v_mctx_1863_; lean_object* v___x_1864_; lean_object* v_fst_1865_; lean_object* v_snd_1866_; lean_object* v___x_1867_; lean_object* v_cache_1868_; lean_object* v_zetaDeltaFVarIds_1869_; lean_object* v_postponed_1870_; lean_object* v_diag_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1880_; 
v___x_1862_ = lean_st_ref_get(v___y_1858_);
v_mctx_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc_ref(v_mctx_1863_);
lean_dec(v___x_1862_);
v___x_1864_ = l_Lean_instantiateMVarsCore(v_mctx_1863_, v_e_1857_);
v_fst_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_fst_1865_);
v_snd_1866_ = lean_ctor_get(v___x_1864_, 1);
lean_inc(v_snd_1866_);
lean_dec_ref(v___x_1864_);
v___x_1867_ = lean_st_ref_take(v___y_1858_);
v_cache_1868_ = lean_ctor_get(v___x_1867_, 1);
v_zetaDeltaFVarIds_1869_ = lean_ctor_get(v___x_1867_, 2);
v_postponed_1870_ = lean_ctor_get(v___x_1867_, 3);
v_diag_1871_ = lean_ctor_get(v___x_1867_, 4);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1880_ == 0)
{
lean_object* v_unused_1881_; 
v_unused_1881_ = lean_ctor_get(v___x_1867_, 0);
lean_dec(v_unused_1881_);
v___x_1873_ = v___x_1867_;
v_isShared_1874_ = v_isSharedCheck_1880_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_diag_1871_);
lean_inc(v_postponed_1870_);
lean_inc(v_zetaDeltaFVarIds_1869_);
lean_inc(v_cache_1868_);
lean_dec(v___x_1867_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1880_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v_snd_1866_);
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_snd_1866_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v_cache_1868_);
lean_ctor_set(v_reuseFailAlloc_1879_, 2, v_zetaDeltaFVarIds_1869_);
lean_ctor_set(v_reuseFailAlloc_1879_, 3, v_postponed_1870_);
lean_ctor_set(v_reuseFailAlloc_1879_, 4, v_diag_1871_);
v___x_1876_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = lean_st_ref_put(v___y_1858_, v___x_1876_);
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v_fst_1865_);
return v___x_1878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg___boxed(lean_object* v_e_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_e_1882_, v___y_1883_);
lean_dec(v___y_1883_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0(lean_object* v_e_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_e_1886_, v___y_1888_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___boxed(lean_object* v_e_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0(v_e_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
return v_res_1899_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1(void){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__0));
v___x_1902_ = l_Lean_stringToMessageData(v___x_1901_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(uint8_t v_useAfter_1903_, lean_object* v_t_u2080_1904_, lean_object* v_h_u2081_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_){
_start:
{
lean_object* v_names_1911_; lean_object* v_fvarIds_1912_; lean_object* v_type_1913_; lean_object* v_val_x3f_1914_; lean_object* v_isInstance_x3f_1915_; lean_object* v_isType_x3f_1916_; lean_object* v_isInserted_x3f_1917_; lean_object* v_isRemoved_x3f_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1973_; 
v_names_1911_ = lean_ctor_get(v_h_u2081_1905_, 0);
v_fvarIds_1912_ = lean_ctor_get(v_h_u2081_1905_, 1);
v_type_1913_ = lean_ctor_get(v_h_u2081_1905_, 2);
v_val_x3f_1914_ = lean_ctor_get(v_h_u2081_1905_, 3);
v_isInstance_x3f_1915_ = lean_ctor_get(v_h_u2081_1905_, 4);
v_isType_x3f_1916_ = lean_ctor_get(v_h_u2081_1905_, 5);
v_isInserted_x3f_1917_ = lean_ctor_get(v_h_u2081_1905_, 6);
v_isRemoved_x3f_1918_ = lean_ctor_get(v_h_u2081_1905_, 7);
v_isSharedCheck_1973_ = !lean_is_exclusive(v_h_u2081_1905_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1920_ = v_h_u2081_1905_;
v_isShared_1921_ = v_isSharedCheck_1973_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_isRemoved_x3f_1918_);
lean_inc(v_isInserted_x3f_1917_);
lean_inc(v_isType_x3f_1916_);
lean_inc(v_isInstance_x3f_1915_);
lean_inc(v_val_x3f_1914_);
lean_inc(v_type_1913_);
lean_inc(v_fvarIds_1912_);
lean_inc(v_names_1911_);
lean_dec(v_h_u2081_1905_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1973_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___y_1923_; lean_object* v___x_1963_; lean_object* v___x_1964_; uint8_t v___x_1965_; 
v___x_1963_ = lean_unsigned_to_nat(0u);
v___x_1964_ = lean_array_get_size(v_fvarIds_1912_);
v___x_1965_ = lean_nat_dec_lt(v___x_1963_, v___x_1964_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; lean_object* v___x_1967_; 
lean_del_object(v___x_1920_);
lean_dec(v_isRemoved_x3f_1918_);
lean_dec(v_isInserted_x3f_1917_);
lean_dec(v_isType_x3f_1916_);
lean_dec(v_isInstance_x3f_1915_);
lean_dec(v_val_x3f_1914_);
lean_dec_ref(v_type_1913_);
lean_dec_ref(v_fvarIds_1912_);
lean_dec_ref(v_names_1911_);
lean_dec_ref(v_t_u2080_1904_);
v___x_1966_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1);
v___x_1967_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_1966_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_);
return v___x_1967_;
}
else
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1968_ = lean_array_fget_borrowed(v_fvarIds_1912_, v___x_1963_);
lean_inc(v___x_1968_);
v___x_1969_ = l_Lean_Expr_fvar___override(v___x_1968_);
lean_inc(v_a_1909_);
lean_inc_ref(v_a_1908_);
lean_inc(v_a_1907_);
lean_inc_ref(v_a_1906_);
v___x_1970_ = lean_infer_type(v___x_1969_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v___x_1972_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_a_1971_);
lean_dec_ref_known(v___x_1970_, 1);
v___x_1972_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_a_1971_, v_a_1907_);
v___y_1923_ = v___x_1972_;
goto v___jp_1922_;
}
else
{
v___y_1923_ = v___x_1970_;
goto v___jp_1922_;
}
}
v___jp_1922_:
{
if (lean_obj_tag(v___y_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1925_; 
v_a_1924_ = lean_ctor_get(v___y_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___y_1923_, 1);
v___x_1925_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(v_t_u2080_1904_, v_a_1924_, v_useAfter_1903_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1927_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1926_);
lean_dec_ref_known(v___x_1925_, 1);
v___x_1927_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(v_useAfter_1903_, v_a_1926_, v_type_1913_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1938_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1930_ = v___x_1927_;
v_isShared_1931_ = v_isSharedCheck_1938_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1927_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1938_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 2, v_a_1928_);
v___x_1933_ = v___x_1920_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_names_1911_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v_fvarIds_1912_);
lean_ctor_set(v_reuseFailAlloc_1937_, 2, v_a_1928_);
lean_ctor_set(v_reuseFailAlloc_1937_, 3, v_val_x3f_1914_);
lean_ctor_set(v_reuseFailAlloc_1937_, 4, v_isInstance_x3f_1915_);
lean_ctor_set(v_reuseFailAlloc_1937_, 5, v_isType_x3f_1916_);
lean_ctor_set(v_reuseFailAlloc_1937_, 6, v_isInserted_x3f_1917_);
lean_ctor_set(v_reuseFailAlloc_1937_, 7, v_isRemoved_x3f_1918_);
v___x_1933_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
lean_object* v___x_1935_; 
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v___x_1933_);
v___x_1935_ = v___x_1930_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1933_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_del_object(v___x_1920_);
lean_dec(v_isRemoved_x3f_1918_);
lean_dec(v_isInserted_x3f_1917_);
lean_dec(v_isType_x3f_1916_);
lean_dec(v_isInstance_x3f_1915_);
lean_dec(v_val_x3f_1914_);
lean_dec_ref(v_fvarIds_1912_);
lean_dec_ref(v_names_1911_);
v_a_1939_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1927_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1927_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_del_object(v___x_1920_);
lean_dec(v_isRemoved_x3f_1918_);
lean_dec(v_isInserted_x3f_1917_);
lean_dec(v_isType_x3f_1916_);
lean_dec(v_isInstance_x3f_1915_);
lean_dec(v_val_x3f_1914_);
lean_dec_ref(v_type_1913_);
lean_dec_ref(v_fvarIds_1912_);
lean_dec_ref(v_names_1911_);
v_a_1947_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1925_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1925_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
lean_del_object(v___x_1920_);
lean_dec(v_isRemoved_x3f_1918_);
lean_dec(v_isInserted_x3f_1917_);
lean_dec(v_isType_x3f_1916_);
lean_dec(v_isInstance_x3f_1915_);
lean_dec(v_val_x3f_1914_);
lean_dec_ref(v_type_1913_);
lean_dec_ref(v_fvarIds_1912_);
lean_dec_ref(v_names_1911_);
lean_dec_ref(v_t_u2080_1904_);
v_a_1955_ = lean_ctor_get(v___y_1923_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___y_1923_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___y_1923_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___y_1923_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___boxed(lean_object* v_useAfter_1974_, lean_object* v_t_u2080_1975_, lean_object* v_h_u2081_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_){
_start:
{
uint8_t v_useAfter_boxed_1982_; lean_object* v_res_1983_; 
v_useAfter_boxed_1982_ = lean_unbox(v_useAfter_1974_);
v_res_1983_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(v_useAfter_boxed_1982_, v_t_u2080_1975_, v_h_u2081_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_);
lean_dec(v_a_1980_);
lean_dec_ref(v_a_1979_);
lean_dec(v_a_1978_);
lean_dec_ref(v_a_1977_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(lean_object* v_ctx_u2080_1987_, uint8_t v_useAfter_1988_, lean_object* v_h_u2081_1989_, lean_object* v___x_1990_, lean_object* v___x_1991_, lean_object* v_as_1992_, size_t v_sz_1993_, size_t v_i_1994_, lean_object* v_b_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
uint8_t v___x_2001_; 
v___x_2001_ = lean_usize_dec_lt(v_i_1994_, v_sz_1993_);
if (v___x_2001_ == 0)
{
lean_object* v___x_2002_; 
lean_dec_ref(v___x_1991_);
lean_dec_ref(v___x_1990_);
lean_dec_ref(v_h_u2081_1989_);
v___x_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2002_, 0, v_b_1995_);
return v___x_2002_;
}
else
{
lean_object* v_a_2003_; lean_object* v_fst_2004_; lean_object* v_snd_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2101_; 
lean_dec_ref(v_b_1995_);
v_a_2003_ = lean_array_uget(v_as_1992_, v_i_1994_);
v_fst_2004_ = lean_ctor_get(v_a_2003_, 0);
v_snd_2005_ = lean_ctor_get(v_a_2003_, 1);
v_isSharedCheck_2101_ = !lean_is_exclusive(v_a_2003_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2007_ = v_a_2003_;
v_isShared_2008_ = v_isSharedCheck_2101_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_snd_2005_);
lean_inc(v_fst_2004_);
lean_dec(v_a_2003_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2101_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2009_; uint8_t v___x_2010_; 
v___x_2009_ = lean_box(0);
v___x_2010_ = l_Lean_LocalContext_contains(v_ctx_u2080_1987_, v_snd_2005_);
lean_dec(v_snd_2005_);
if (v___x_2010_ == 0)
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2011_ = lean_box(0);
v___x_2012_ = l_Lean_Name_str___override(v___x_2011_, v_fst_2004_);
v___x_2013_ = l_Lean_LocalContext_findFromUserName_x3f(v_ctx_u2080_1987_, v___x_2012_);
lean_dec(v___x_2012_);
if (lean_obj_tag(v___x_2013_) == 1)
{
lean_object* v_val_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2052_; 
lean_dec_ref(v___x_1991_);
lean_dec_ref(v___x_1990_);
v_val_2014_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2016_ = v___x_2013_;
v_isShared_2017_ = v_isSharedCheck_2052_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_val_2014_);
lean_dec(v___x_2013_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2052_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = l_Lean_LocalDecl_type(v_val_2014_);
lean_dec(v_val_2014_);
v___x_2019_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v___x_2018_, v___y_1997_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2021_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2020_);
lean_dec_ref_known(v___x_2019_, 1);
v___x_2021_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(v_useAfter_1988_, v_a_2020_, v_h_u2081_1989_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2035_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2024_ = v___x_2021_;
v_isShared_2025_ = v_isSharedCheck_2035_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2021_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2035_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 0, v_a_2022_);
v___x_2027_ = v___x_2016_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
lean_object* v___x_2029_; 
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 1, v___x_2009_);
lean_ctor_set(v___x_2007_, 0, v___x_2027_);
v___x_2029_ = v___x_2007_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2027_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v___x_2009_);
v___x_2029_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
lean_object* v___x_2031_; 
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 0, v___x_2029_);
v___x_2031_ = v___x_2024_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2029_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
lean_del_object(v___x_2016_);
lean_del_object(v___x_2007_);
v_a_2036_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_2021_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2021_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
lean_del_object(v___x_2016_);
lean_del_object(v___x_2007_);
lean_dec_ref(v_h_u2081_1989_);
v_a_2044_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2046_ = v___x_2019_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2019_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2044_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
}
else
{
lean_dec(v___x_2013_);
if (v_useAfter_1988_ == 0)
{
lean_object* v_type_2053_; lean_object* v_val_x3f_2054_; lean_object* v_isInstance_x3f_2055_; lean_object* v_isType_x3f_2056_; lean_object* v_isInserted_x3f_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2071_; 
v_type_2053_ = lean_ctor_get(v_h_u2081_1989_, 2);
v_val_x3f_2054_ = lean_ctor_get(v_h_u2081_1989_, 3);
v_isInstance_x3f_2055_ = lean_ctor_get(v_h_u2081_1989_, 4);
v_isType_x3f_2056_ = lean_ctor_get(v_h_u2081_1989_, 5);
v_isInserted_x3f_2057_ = lean_ctor_get(v_h_u2081_1989_, 6);
v_isSharedCheck_2071_ = !lean_is_exclusive(v_h_u2081_1989_);
if (v_isSharedCheck_2071_ == 0)
{
lean_object* v_unused_2072_; lean_object* v_unused_2073_; lean_object* v_unused_2074_; 
v_unused_2072_ = lean_ctor_get(v_h_u2081_1989_, 7);
lean_dec(v_unused_2072_);
v_unused_2073_ = lean_ctor_get(v_h_u2081_1989_, 1);
lean_dec(v_unused_2073_);
v_unused_2074_ = lean_ctor_get(v_h_u2081_1989_, 0);
lean_dec(v_unused_2074_);
v___x_2059_ = v_h_u2081_1989_;
v_isShared_2060_ = v_isSharedCheck_2071_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_isInserted_x3f_2057_);
lean_inc(v_isType_x3f_2056_);
lean_inc(v_isInstance_x3f_2055_);
lean_inc(v_val_x3f_2054_);
lean_inc(v_type_2053_);
lean_dec(v_h_u2081_1989_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2071_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2064_; 
v___x_2061_ = lean_box(v___x_2001_);
v___x_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 7, v___x_2062_);
lean_ctor_set(v___x_2059_, 1, v___x_1991_);
lean_ctor_set(v___x_2059_, 0, v___x_1990_);
v___x_2064_ = v___x_2059_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_1990_);
lean_ctor_set(v_reuseFailAlloc_2070_, 1, v___x_1991_);
lean_ctor_set(v_reuseFailAlloc_2070_, 2, v_type_2053_);
lean_ctor_set(v_reuseFailAlloc_2070_, 3, v_val_x3f_2054_);
lean_ctor_set(v_reuseFailAlloc_2070_, 4, v_isInstance_x3f_2055_);
lean_ctor_set(v_reuseFailAlloc_2070_, 5, v_isType_x3f_2056_);
lean_ctor_set(v_reuseFailAlloc_2070_, 6, v_isInserted_x3f_2057_);
lean_ctor_set(v_reuseFailAlloc_2070_, 7, v___x_2062_);
v___x_2064_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
lean_object* v___x_2065_; lean_object* v___x_2067_; 
v___x_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2064_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 1, v___x_2009_);
lean_ctor_set(v___x_2007_, 0, v___x_2065_);
v___x_2067_ = v___x_2007_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2065_);
lean_ctor_set(v_reuseFailAlloc_2069_, 1, v___x_2009_);
v___x_2067_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
lean_object* v___x_2068_; 
v___x_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
return v___x_2068_;
}
}
}
}
else
{
lean_object* v_type_2075_; lean_object* v_val_x3f_2076_; lean_object* v_isInstance_x3f_2077_; lean_object* v_isType_x3f_2078_; lean_object* v_isRemoved_x3f_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2093_; 
v_type_2075_ = lean_ctor_get(v_h_u2081_1989_, 2);
v_val_x3f_2076_ = lean_ctor_get(v_h_u2081_1989_, 3);
v_isInstance_x3f_2077_ = lean_ctor_get(v_h_u2081_1989_, 4);
v_isType_x3f_2078_ = lean_ctor_get(v_h_u2081_1989_, 5);
v_isRemoved_x3f_2079_ = lean_ctor_get(v_h_u2081_1989_, 7);
v_isSharedCheck_2093_ = !lean_is_exclusive(v_h_u2081_1989_);
if (v_isSharedCheck_2093_ == 0)
{
lean_object* v_unused_2094_; lean_object* v_unused_2095_; lean_object* v_unused_2096_; 
v_unused_2094_ = lean_ctor_get(v_h_u2081_1989_, 6);
lean_dec(v_unused_2094_);
v_unused_2095_ = lean_ctor_get(v_h_u2081_1989_, 1);
lean_dec(v_unused_2095_);
v_unused_2096_ = lean_ctor_get(v_h_u2081_1989_, 0);
lean_dec(v_unused_2096_);
v___x_2081_ = v_h_u2081_1989_;
v_isShared_2082_ = v_isSharedCheck_2093_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_isRemoved_x3f_2079_);
lean_inc(v_isType_x3f_2078_);
lean_inc(v_isInstance_x3f_2077_);
lean_inc(v_val_x3f_2076_);
lean_inc(v_type_2075_);
lean_dec(v_h_u2081_1989_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2093_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2086_; 
v___x_2083_ = lean_box(v___x_2001_);
v___x_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 6, v___x_2084_);
lean_ctor_set(v___x_2081_, 1, v___x_1991_);
lean_ctor_set(v___x_2081_, 0, v___x_1990_);
v___x_2086_ = v___x_2081_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_1990_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v___x_1991_);
lean_ctor_set(v_reuseFailAlloc_2092_, 2, v_type_2075_);
lean_ctor_set(v_reuseFailAlloc_2092_, 3, v_val_x3f_2076_);
lean_ctor_set(v_reuseFailAlloc_2092_, 4, v_isInstance_x3f_2077_);
lean_ctor_set(v_reuseFailAlloc_2092_, 5, v_isType_x3f_2078_);
lean_ctor_set(v_reuseFailAlloc_2092_, 6, v___x_2084_);
lean_ctor_set(v_reuseFailAlloc_2092_, 7, v_isRemoved_x3f_2079_);
v___x_2086_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
lean_object* v___x_2087_; lean_object* v___x_2089_; 
v___x_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 1, v___x_2009_);
lean_ctor_set(v___x_2007_, 0, v___x_2087_);
v___x_2089_ = v___x_2007_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v___x_2087_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v___x_2009_);
v___x_2089_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
lean_object* v___x_2090_; 
v___x_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
return v___x_2090_;
}
}
}
}
}
}
else
{
lean_object* v___x_2097_; size_t v___x_2098_; size_t v___x_2099_; 
lean_del_object(v___x_2007_);
lean_dec(v_fst_2004_);
v___x_2097_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___closed__0));
v___x_2098_ = ((size_t)1ULL);
v___x_2099_ = lean_usize_add(v_i_1994_, v___x_2098_);
v_i_1994_ = v___x_2099_;
v_b_1995_ = v___x_2097_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___boxed(lean_object* v_ctx_u2080_2102_, lean_object* v_useAfter_2103_, lean_object* v_h_u2081_2104_, lean_object* v___x_2105_, lean_object* v___x_2106_, lean_object* v_as_2107_, lean_object* v_sz_2108_, lean_object* v_i_2109_, lean_object* v_b_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
uint8_t v_useAfter_boxed_2116_; size_t v_sz_boxed_2117_; size_t v_i_boxed_2118_; lean_object* v_res_2119_; 
v_useAfter_boxed_2116_ = lean_unbox(v_useAfter_2103_);
v_sz_boxed_2117_ = lean_unbox_usize(v_sz_2108_);
lean_dec(v_sz_2108_);
v_i_boxed_2118_ = lean_unbox_usize(v_i_2109_);
lean_dec(v_i_2109_);
v_res_2119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(v_ctx_u2080_2102_, v_useAfter_boxed_2116_, v_h_u2081_2104_, v___x_2105_, v___x_2106_, v_as_2107_, v_sz_boxed_2117_, v_i_boxed_2118_, v_b_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec_ref(v_as_2107_);
lean_dec_ref(v_ctx_u2080_2102_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(uint8_t v_useAfter_2120_, lean_object* v_ctx_u2080_2121_, lean_object* v_h_u2081_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_){
_start:
{
lean_object* v_names_2128_; lean_object* v_fvarIds_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; size_t v_sz_2132_; size_t v___x_2133_; lean_object* v___x_2134_; 
v_names_2128_ = lean_ctor_get(v_h_u2081_2122_, 0);
v_fvarIds_2129_ = lean_ctor_get(v_h_u2081_2122_, 1);
v___x_2130_ = l_Array_zip___redArg(v_names_2128_, v_fvarIds_2129_);
v___x_2131_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___closed__0));
v_sz_2132_ = lean_array_size(v___x_2130_);
v___x_2133_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_2129_);
lean_inc_ref(v_names_2128_);
lean_inc_ref(v_h_u2081_2122_);
v___x_2134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(v_ctx_u2080_2121_, v_useAfter_2120_, v_h_u2081_2122_, v_names_2128_, v_fvarIds_2129_, v___x_2130_, v_sz_2132_, v___x_2133_, v___x_2131_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
lean_dec_ref(v___x_2130_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2147_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2137_ = v___x_2134_;
v_isShared_2138_ = v_isSharedCheck_2147_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2134_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2147_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v_fst_2139_; 
v_fst_2139_ = lean_ctor_get(v_a_2135_, 0);
lean_inc(v_fst_2139_);
lean_dec(v_a_2135_);
if (lean_obj_tag(v_fst_2139_) == 0)
{
lean_object* v___x_2141_; 
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v_h_u2081_2122_);
v___x_2141_ = v___x_2137_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_h_u2081_2122_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
else
{
lean_object* v_val_2143_; lean_object* v___x_2145_; 
lean_dec_ref(v_h_u2081_2122_);
v_val_2143_ = lean_ctor_get(v_fst_2139_, 0);
lean_inc(v_val_2143_);
lean_dec_ref_known(v_fst_2139_, 1);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v_val_2143_);
v___x_2145_ = v___x_2137_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_val_2143_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec_ref(v_h_u2081_2122_);
v_a_2148_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2134_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2134_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle___boxed(lean_object* v_useAfter_2156_, lean_object* v_ctx_u2080_2157_, lean_object* v_h_u2081_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_){
_start:
{
uint8_t v_useAfter_boxed_2164_; lean_object* v_res_2165_; 
v_useAfter_boxed_2164_ = lean_unbox(v_useAfter_2156_);
v_res_2165_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(v_useAfter_boxed_2164_, v_ctx_u2080_2157_, v_h_u2081_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
lean_dec(v_a_2162_);
lean_dec_ref(v_a_2161_);
lean_dec(v_a_2160_);
lean_dec_ref(v_a_2159_);
lean_dec_ref(v_ctx_u2080_2157_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(uint8_t v_useAfter_2166_, lean_object* v_lctx_u2080_2167_, size_t v_sz_2168_, size_t v_i_2169_, lean_object* v_bs_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
uint8_t v___x_2176_; 
v___x_2176_ = lean_usize_dec_lt(v_i_2169_, v_sz_2168_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; 
v___x_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2177_, 0, v_bs_2170_);
return v___x_2177_;
}
else
{
lean_object* v_v_2178_; lean_object* v___x_2179_; 
v_v_2178_ = lean_array_uget_borrowed(v_bs_2170_, v_i_2169_);
lean_inc(v_v_2178_);
v___x_2179_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(v_useAfter_2166_, v_lctx_u2080_2167_, v_v_2178_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v___x_2181_; lean_object* v_bs_x27_2182_; size_t v___x_2183_; size_t v___x_2184_; lean_object* v___x_2185_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2180_);
lean_dec_ref_known(v___x_2179_, 1);
v___x_2181_ = lean_unsigned_to_nat(0u);
v_bs_x27_2182_ = lean_array_uset(v_bs_2170_, v_i_2169_, v___x_2181_);
v___x_2183_ = ((size_t)1ULL);
v___x_2184_ = lean_usize_add(v_i_2169_, v___x_2183_);
v___x_2185_ = lean_array_uset(v_bs_x27_2182_, v_i_2169_, v_a_2180_);
v_i_2169_ = v___x_2184_;
v_bs_2170_ = v___x_2185_;
goto _start;
}
else
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2194_; 
lean_dec_ref(v_bs_2170_);
v_a_2187_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2189_ = v___x_2179_;
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2179_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2192_; 
if (v_isShared_2190_ == 0)
{
v___x_2192_ = v___x_2189_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2187_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0___boxed(lean_object* v_useAfter_2195_, lean_object* v_lctx_u2080_2196_, lean_object* v_sz_2197_, lean_object* v_i_2198_, lean_object* v_bs_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
uint8_t v_useAfter_boxed_2205_; size_t v_sz_boxed_2206_; size_t v_i_boxed_2207_; lean_object* v_res_2208_; 
v_useAfter_boxed_2205_ = lean_unbox(v_useAfter_2195_);
v_sz_boxed_2206_ = lean_unbox_usize(v_sz_2197_);
lean_dec(v_sz_2197_);
v_i_boxed_2207_ = lean_unbox_usize(v_i_2198_);
lean_dec(v_i_2198_);
v_res_2208_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(v_useAfter_boxed_2205_, v_lctx_u2080_2196_, v_sz_boxed_2206_, v_i_boxed_2207_, v_bs_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec_ref(v_lctx_u2080_2196_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(uint8_t v_useAfter_2209_, lean_object* v_lctx_u2080_2210_, lean_object* v_hs_u2081_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_){
_start:
{
size_t v_sz_2217_; size_t v___x_2218_; lean_object* v___x_2219_; 
v_sz_2217_ = lean_array_size(v_hs_u2081_2211_);
v___x_2218_ = ((size_t)0ULL);
v___x_2219_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(v_useAfter_2209_, v_lctx_u2080_2210_, v_sz_2217_, v___x_2218_, v_hs_u2081_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses___boxed(lean_object* v_useAfter_2220_, lean_object* v_lctx_u2080_2221_, lean_object* v_hs_u2081_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_){
_start:
{
uint8_t v_useAfter_boxed_2228_; lean_object* v_res_2229_; 
v_useAfter_boxed_2228_ = lean_unbox(v_useAfter_2220_);
v_res_2229_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(v_useAfter_boxed_2228_, v_lctx_u2080_2221_, v_hs_u2081_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_);
lean_dec(v_a_2226_);
lean_dec_ref(v_a_2225_);
lean_dec(v_a_2224_);
lean_dec_ref(v_a_2223_);
lean_dec_ref(v_lctx_u2080_2221_);
return v_res_2229_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2(void){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__1));
v___x_2235_ = l_Lean_stringToMessageData(v___x_2234_);
return v___x_2235_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4(void){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__3));
v___x_2238_ = l_Lean_stringToMessageData(v___x_2237_);
return v___x_2238_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6(void){
_start:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2240_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__5));
v___x_2241_ = l_Lean_stringToMessageData(v___x_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(uint8_t v_useAfter_2242_, lean_object* v_g_u2080_2243_, lean_object* v_i_u2081_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_){
_start:
{
lean_object* v___x_2250_; lean_object* v_mctx_2251_; lean_object* v___x_2252_; 
v___x_2250_ = lean_st_ref_get(v_a_2246_);
v_mctx_2251_ = lean_ctor_get(v___x_2250_, 0);
lean_inc_ref(v_mctx_2251_);
lean_dec(v___x_2250_);
v___x_2252_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2251_, v_g_u2080_2243_);
lean_dec_ref(v_mctx_2251_);
if (lean_obj_tag(v___x_2252_) == 1)
{
lean_object* v_val_2253_; lean_object* v_options_2254_; lean_object* v_lctx_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v_toInteractiveGoalCore_2259_; lean_object* v_fst_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2357_; 
v_val_2253_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_val_2253_);
lean_dec_ref_known(v___x_2252_, 1);
v_options_2254_ = lean_ctor_get(v_a_2247_, 1);
v_lctx_2255_ = lean_ctor_get(v_val_2253_, 1);
lean_inc_ref(v_lctx_2255_);
lean_dec(v_val_2253_);
v___x_2256_ = lean_box(1);
lean_inc_ref(v_options_2254_);
v___x_2257_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2257_, 0, v_options_2254_);
lean_ctor_set(v___x_2257_, 1, v___x_2256_);
lean_ctor_set(v___x_2257_, 2, v___x_2256_);
v___x_2258_ = l_Lean_LocalContext_sanitizeNames(v_lctx_2255_, v___x_2257_);
v_toInteractiveGoalCore_2259_ = lean_ctor_get(v_i_u2081_2244_, 0);
lean_inc_ref(v_toInteractiveGoalCore_2259_);
v_fst_2260_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2357_ == 0)
{
lean_object* v_unused_2358_; 
v_unused_2358_ = lean_ctor_get(v___x_2258_, 1);
lean_dec(v_unused_2358_);
v___x_2262_ = v___x_2258_;
v_isShared_2263_ = v_isSharedCheck_2357_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_fst_2260_);
lean_dec(v___x_2258_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2357_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v_userName_x3f_2264_; lean_object* v_goalPrefix_2265_; lean_object* v_mvarId_2266_; lean_object* v_isRemoved_x3f_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2354_; 
v_userName_x3f_2264_ = lean_ctor_get(v_i_u2081_2244_, 1);
v_goalPrefix_2265_ = lean_ctor_get(v_i_u2081_2244_, 2);
v_mvarId_2266_ = lean_ctor_get(v_i_u2081_2244_, 3);
v_isRemoved_x3f_2267_ = lean_ctor_get(v_i_u2081_2244_, 5);
v_isSharedCheck_2354_ = !lean_is_exclusive(v_i_u2081_2244_);
if (v_isSharedCheck_2354_ == 0)
{
lean_object* v_unused_2355_; lean_object* v_unused_2356_; 
v_unused_2355_ = lean_ctor_get(v_i_u2081_2244_, 4);
lean_dec(v_unused_2355_);
v_unused_2356_ = lean_ctor_get(v_i_u2081_2244_, 0);
lean_dec(v_unused_2356_);
v___x_2269_ = v_i_u2081_2244_;
v_isShared_2270_ = v_isSharedCheck_2354_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_isRemoved_x3f_2267_);
lean_inc(v_mvarId_2266_);
lean_inc(v_goalPrefix_2265_);
lean_inc(v_userName_x3f_2264_);
lean_dec(v_i_u2081_2244_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2354_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v_hyps_2271_; lean_object* v_type_2272_; lean_object* v_ctx_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2353_; 
v_hyps_2271_ = lean_ctor_get(v_toInteractiveGoalCore_2259_, 0);
v_type_2272_ = lean_ctor_get(v_toInteractiveGoalCore_2259_, 1);
v_ctx_2273_ = lean_ctor_get(v_toInteractiveGoalCore_2259_, 2);
v_isSharedCheck_2353_ = !lean_is_exclusive(v_toInteractiveGoalCore_2259_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2275_ = v_toInteractiveGoalCore_2259_;
v_isShared_2276_ = v_isSharedCheck_2353_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_ctx_2273_);
lean_inc(v_type_2272_);
lean_inc(v_hyps_2271_);
lean_dec(v_toInteractiveGoalCore_2259_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2353_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2277_; 
v___x_2277_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(v_useAfter_2242_, v_fst_2260_, v_hyps_2271_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_);
lean_dec(v_fst_2260_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v_a_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_a_2278_);
lean_dec_ref_known(v___x_2277_, 1);
v___x_2279_ = l_Lean_Expr_mvar___override(v_g_u2080_2243_);
lean_inc(v_a_2248_);
lean_inc_ref(v_a_2247_);
lean_inc(v_a_2246_);
lean_inc_ref(v_a_2245_);
v___x_2280_ = lean_infer_type(v___x_2279_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; lean_object* v___x_2282_; lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2336_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_a_2281_);
lean_dec_ref_known(v___x_2280_, 1);
v___x_2282_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_a_2281_, v_a_2246_);
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2285_ = v___x_2282_;
v_isShared_2286_ = v_isSharedCheck_2336_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2282_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2336_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2287_; lean_object* v_mctx_2288_; lean_object* v___x_2289_; 
v___x_2287_ = lean_st_ref_get(v_a_2246_);
v_mctx_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc_ref(v_mctx_2288_);
lean_dec(v___x_2287_);
v___x_2289_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2288_, v_mvarId_2266_);
lean_dec_ref(v_mctx_2288_);
if (lean_obj_tag(v___x_2289_) == 1)
{
lean_object* v_val_2290_; lean_object* v_type_2291_; lean_object* v___x_2292_; lean_object* v_a_2293_; lean_object* v___x_2294_; 
lean_del_object(v___x_2285_);
lean_del_object(v___x_2262_);
v_val_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_val_2290_);
lean_dec_ref_known(v___x_2289_, 1);
v_type_2291_ = lean_ctor_get(v_val_2290_, 2);
lean_inc_ref(v_type_2291_);
lean_dec(v_val_2290_);
v___x_2292_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_type_2291_, v_a_2246_);
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2293_);
lean_dec_ref(v___x_2292_);
v___x_2294_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(v_a_2283_, v_a_2293_, v_useAfter_2242_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2296_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
lean_dec_ref_known(v___x_2294_, 1);
v___x_2296_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(v_useAfter_2242_, v_a_2295_, v_type_2272_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2311_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2299_ = v___x_2296_;
v_isShared_2300_ = v_isSharedCheck_2311_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2296_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2311_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2302_; 
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 1, v_a_2297_);
lean_ctor_set(v___x_2275_, 0, v_a_2278_);
v___x_2302_ = v___x_2275_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2278_);
lean_ctor_set(v_reuseFailAlloc_2310_, 1, v_a_2297_);
lean_ctor_set(v_reuseFailAlloc_2310_, 2, v_ctx_2273_);
v___x_2302_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
lean_object* v___x_2303_; lean_object* v___x_2305_; 
v___x_2303_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__0));
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 4, v___x_2303_);
lean_ctor_set(v___x_2269_, 0, v___x_2302_);
v___x_2305_ = v___x_2269_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2302_);
lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_userName_x3f_2264_);
lean_ctor_set(v_reuseFailAlloc_2309_, 2, v_goalPrefix_2265_);
lean_ctor_set(v_reuseFailAlloc_2309_, 3, v_mvarId_2266_);
lean_ctor_set(v_reuseFailAlloc_2309_, 4, v___x_2303_);
lean_ctor_set(v_reuseFailAlloc_2309_, 5, v_isRemoved_x3f_2267_);
v___x_2305_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
lean_object* v___x_2307_; 
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 0, v___x_2305_);
v___x_2307_ = v___x_2299_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2305_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
}
else
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
lean_dec(v_a_2278_);
lean_del_object(v___x_2275_);
lean_dec_ref(v_ctx_2273_);
lean_del_object(v___x_2269_);
lean_dec(v_isRemoved_x3f_2267_);
lean_dec(v_mvarId_2266_);
lean_dec_ref(v_goalPrefix_2265_);
lean_dec(v_userName_x3f_2264_);
v_a_2312_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___x_2296_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2296_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
else
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2327_; 
lean_dec(v_a_2278_);
lean_del_object(v___x_2275_);
lean_dec_ref(v_ctx_2273_);
lean_dec_ref(v_type_2272_);
lean_del_object(v___x_2269_);
lean_dec(v_isRemoved_x3f_2267_);
lean_dec(v_mvarId_2266_);
lean_dec_ref(v_goalPrefix_2265_);
lean_dec(v_userName_x3f_2264_);
v_a_2320_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2322_ = v___x_2294_;
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2294_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2325_; 
if (v_isShared_2323_ == 0)
{
v___x_2325_ = v___x_2322_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2320_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
else
{
lean_object* v___x_2328_; lean_object* v___x_2330_; 
lean_dec(v___x_2289_);
lean_dec(v_a_2283_);
lean_dec(v_a_2278_);
lean_del_object(v___x_2275_);
lean_dec_ref(v_ctx_2273_);
lean_dec_ref(v_type_2272_);
lean_del_object(v___x_2269_);
lean_dec(v_isRemoved_x3f_2267_);
lean_dec_ref(v_goalPrefix_2265_);
lean_dec(v_userName_x3f_2264_);
v___x_2328_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2);
if (v_isShared_2286_ == 0)
{
lean_ctor_set_tag(v___x_2285_, 1);
lean_ctor_set(v___x_2285_, 0, v_mvarId_2266_);
v___x_2330_ = v___x_2285_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_mvarId_2266_);
v___x_2330_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
lean_object* v___x_2332_; 
if (v_isShared_2263_ == 0)
{
lean_ctor_set_tag(v___x_2262_, 7);
lean_ctor_set(v___x_2262_, 1, v___x_2330_);
lean_ctor_set(v___x_2262_, 0, v___x_2328_);
v___x_2332_ = v___x_2262_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2328_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v___x_2330_);
v___x_2332_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
lean_object* v___x_2333_; 
v___x_2333_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_2332_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_);
return v___x_2333_;
}
}
}
}
}
else
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
lean_dec(v_a_2278_);
lean_del_object(v___x_2275_);
lean_dec_ref(v_ctx_2273_);
lean_dec_ref(v_type_2272_);
lean_del_object(v___x_2269_);
lean_dec(v_isRemoved_x3f_2267_);
lean_dec(v_mvarId_2266_);
lean_dec_ref(v_goalPrefix_2265_);
lean_dec(v_userName_x3f_2264_);
lean_del_object(v___x_2262_);
v_a_2337_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2280_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2280_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
else
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
lean_del_object(v___x_2275_);
lean_dec_ref(v_ctx_2273_);
lean_dec_ref(v_type_2272_);
lean_del_object(v___x_2269_);
lean_dec(v_isRemoved_x3f_2267_);
lean_dec(v_mvarId_2266_);
lean_dec_ref(v_goalPrefix_2265_);
lean_dec(v_userName_x3f_2264_);
lean_del_object(v___x_2262_);
lean_dec(v_g_u2080_2243_);
v_a_2345_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2277_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2277_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
lean_dec(v___x_2252_);
lean_dec_ref(v_i_u2081_2244_);
v___x_2359_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4);
v___x_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2360_, 0, v_g_u2080_2243_);
v___x_2361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2359_);
lean_ctor_set(v___x_2361_, 1, v___x_2360_);
v___x_2362_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6);
v___x_2363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2361_);
lean_ctor_set(v___x_2363_, 1, v___x_2362_);
v___x_2364_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_2363_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_);
return v___x_2364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___boxed(lean_object* v_useAfter_2365_, lean_object* v_g_u2080_2366_, lean_object* v_i_u2081_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_){
_start:
{
uint8_t v_useAfter_boxed_2373_; lean_object* v_res_2374_; 
v_useAfter_boxed_2373_ = lean_unbox(v_useAfter_2365_);
v_res_2374_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(v_useAfter_boxed_2373_, v_g_u2080_2366_, v_i_u2081_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v_a_2371_);
lean_dec_ref(v_a_2370_);
lean_dec(v_a_2369_);
lean_dec_ref(v_a_2368_);
return v_res_2374_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(lean_object* v_opts_2375_, lean_object* v_opt_2376_){
_start:
{
lean_object* v_name_2377_; lean_object* v_defValue_2378_; lean_object* v_map_2379_; lean_object* v___x_2380_; 
v_name_2377_ = lean_ctor_get(v_opt_2376_, 0);
v_defValue_2378_ = lean_ctor_get(v_opt_2376_, 1);
v_map_2379_ = lean_ctor_get(v_opts_2375_, 0);
v___x_2380_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2379_, v_name_2377_);
if (lean_obj_tag(v___x_2380_) == 0)
{
uint8_t v___x_2381_; 
v___x_2381_ = lean_unbox(v_defValue_2378_);
return v___x_2381_;
}
else
{
lean_object* v_val_2382_; 
v_val_2382_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_val_2382_);
lean_dec_ref_known(v___x_2380_, 1);
if (lean_obj_tag(v_val_2382_) == 1)
{
uint8_t v_v_2383_; 
v_v_2383_ = lean_ctor_get_uint8(v_val_2382_, 0);
lean_dec_ref_known(v_val_2382_, 0);
return v_v_2383_;
}
else
{
uint8_t v___x_2384_; 
lean_dec(v_val_2382_);
v___x_2384_ = lean_unbox(v_defValue_2378_);
return v___x_2384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0___boxed(lean_object* v_opts_2385_, lean_object* v_opt_2386_){
_start:
{
uint8_t v_res_2387_; lean_object* v_r_2388_; 
v_res_2387_ = l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(v_opts_2385_, v_opt_2386_);
lean_dec_ref(v_opt_2386_);
lean_dec_ref(v_opts_2385_);
v_r_2388_ = lean_box(v_res_2387_);
return v_r_2388_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(lean_object* v_x_2389_, lean_object* v_x_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
if (lean_obj_tag(v_x_2390_) == 0)
{
lean_object* v___x_2396_; 
v___x_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2396_, 0, v_x_2389_);
return v___x_2396_;
}
else
{
lean_object* v_head_2397_; lean_object* v_tail_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v_head_2397_ = lean_ctor_get(v_x_2390_, 0);
lean_inc_n(v_head_2397_, 2);
v_tail_2398_ = lean_ctor_get(v_x_2390_, 1);
lean_inc(v_tail_2398_);
lean_dec_ref_known(v_x_2390_, 2);
v___x_2399_ = l_Lean_Expr_mvar___override(v_head_2397_);
v___x_2400_ = l_Lean_Meta_getMVars(v___x_2399_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_a_2401_);
lean_dec_ref_known(v___x_2400_, 1);
v___x_2402_ = l_Lean_MVarIdSet_ofArray(v_a_2401_);
lean_dec(v_a_2401_);
v___x_2403_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_head_2397_, v___x_2402_, v_x_2389_);
v_x_2389_ = v___x_2403_;
v_x_2390_ = v_tail_2398_;
goto _start;
}
else
{
lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2412_; 
lean_dec(v_tail_2398_);
lean_dec(v_head_2397_);
lean_dec(v_x_2389_);
v_a_2405_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2407_ = v___x_2400_;
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2400_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2410_; 
if (v_isShared_2408_ == 0)
{
v___x_2410_ = v___x_2407_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_a_2405_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1___boxed(lean_object* v_x_2413_, lean_object* v_x_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(v_x_2413_, v_x_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(lean_object* v_lctx_2421_, lean_object* v_localInsts_2422_, lean_object* v_x_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2421_, v_localInsts_2422_, v_x_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2429_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2429_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
else
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2445_; 
v_a_2438_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2440_ = v___x_2429_;
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2429_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2443_; 
if (v_isShared_2441_ == 0)
{
v___x_2443_ = v___x_2440_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_a_2438_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg___boxed(lean_object* v_lctx_2446_, lean_object* v_localInsts_2447_, lean_object* v_x_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(v_lctx_2446_, v_localInsts_2447_, v_x_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
return v_res_2454_;
}
}
static lean_object* _init_l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2456_ = ((lean_object*)(l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__0));
v___x_2457_ = l_Lean_stringToMessageData(v___x_2456_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(lean_object* v_goal_2458_, lean_object* v_action_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
lean_object* v___x_2465_; lean_object* v_mctx_2466_; lean_object* v___x_2467_; 
v___x_2465_ = lean_st_ref_get(v___y_2461_);
v_mctx_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc_ref(v_mctx_2466_);
lean_dec(v___x_2465_);
v___x_2467_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2466_, v_goal_2458_);
lean_dec_ref(v_mctx_2466_);
if (lean_obj_tag(v___x_2467_) == 1)
{
lean_object* v_val_2468_; lean_object* v_options_2469_; lean_object* v_lctx_2470_; lean_object* v_localInstances_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v_fst_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
lean_dec(v_goal_2458_);
v_val_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_val_2468_);
lean_dec_ref_known(v___x_2467_, 1);
v_options_2469_ = lean_ctor_get(v___y_2462_, 1);
v_lctx_2470_ = lean_ctor_get(v_val_2468_, 1);
v_localInstances_2471_ = lean_ctor_get(v_val_2468_, 4);
lean_inc_ref(v_localInstances_2471_);
v___x_2472_ = lean_box(1);
lean_inc_ref(v_options_2469_);
v___x_2473_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2473_, 0, v_options_2469_);
lean_ctor_set(v___x_2473_, 1, v___x_2472_);
lean_ctor_set(v___x_2473_, 2, v___x_2472_);
lean_inc_ref(v_lctx_2470_);
v___x_2474_ = l_Lean_LocalContext_sanitizeNames(v_lctx_2470_, v___x_2473_);
v_fst_2475_ = lean_ctor_get(v___x_2474_, 0);
lean_inc_n(v_fst_2475_, 2);
lean_dec_ref(v___x_2474_);
v___x_2476_ = lean_apply_2(v_action_2459_, v_fst_2475_, v_val_2468_);
v___x_2477_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(v_fst_2475_, v_localInstances_2471_, v___x_2476_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
return v___x_2477_;
}
else
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
lean_dec(v___x_2467_);
lean_dec_ref(v_action_2459_);
v___x_2478_ = lean_obj_once(&l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1, &l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1_once, _init_l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1);
v___x_2479_ = l_Lean_MessageData_ofName(v_goal_2458_);
v___x_2480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2478_);
lean_ctor_set(v___x_2480_, 1, v___x_2479_);
v___x_2481_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_2480_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
return v___x_2481_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___boxed(lean_object* v_goal_2482_, lean_object* v_action_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(v_goal_2482_, v_action_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
return v_res_2489_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4(lean_object* v___x_2490_, lean_object* v_x_2491_){
_start:
{
if (lean_obj_tag(v_x_2491_) == 0)
{
uint8_t v___x_2492_; 
v___x_2492_ = 0;
return v___x_2492_;
}
else
{
lean_object* v_head_2493_; lean_object* v_tail_2494_; uint8_t v___x_2495_; 
v_head_2493_ = lean_ctor_get(v_x_2491_, 0);
v_tail_2494_ = lean_ctor_get(v_x_2491_, 1);
v___x_2495_ = l_Lean_instBEqMVarId_beq(v_head_2493_, v___x_2490_);
if (v___x_2495_ == 0)
{
v_x_2491_ = v_tail_2494_;
goto _start;
}
else
{
return v___x_2495_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4___boxed(lean_object* v___x_2497_, lean_object* v_x_2498_){
_start:
{
uint8_t v_res_2499_; lean_object* v_r_2500_; 
v_res_2499_ = l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4(v___x_2497_, v_x_2498_);
lean_dec(v_x_2498_);
lean_dec(v___x_2497_);
v_r_2500_ = lean_box(v_res_2499_);
return v_r_2500_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(lean_object* v_t_2501_, lean_object* v_k_2502_){
_start:
{
if (lean_obj_tag(v_t_2501_) == 0)
{
lean_object* v_k_2503_; lean_object* v_v_2504_; lean_object* v_l_2505_; lean_object* v_r_2506_; uint8_t v___x_2507_; 
v_k_2503_ = lean_ctor_get(v_t_2501_, 1);
v_v_2504_ = lean_ctor_get(v_t_2501_, 2);
v_l_2505_ = lean_ctor_get(v_t_2501_, 3);
v_r_2506_ = lean_ctor_get(v_t_2501_, 4);
v___x_2507_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2502_, v_k_2503_);
switch(v___x_2507_)
{
case 0:
{
v_t_2501_ = v_l_2505_;
goto _start;
}
case 1:
{
lean_object* v___x_2509_; 
lean_inc(v_v_2504_);
v___x_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2509_, 0, v_v_2504_);
return v___x_2509_;
}
default: 
{
v_t_2501_ = v_r_2506_;
goto _start;
}
}
}
else
{
lean_object* v___x_2511_; 
v___x_2511_ = lean_box(0);
return v___x_2511_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg___boxed(lean_object* v_t_2512_, lean_object* v_k_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(v_t_2512_, v_k_2513_);
lean_dec(v_k_2513_);
lean_dec(v_t_2512_);
return v_res_2514_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(lean_object* v_k_2515_, lean_object* v_t_2516_){
_start:
{
if (lean_obj_tag(v_t_2516_) == 0)
{
lean_object* v_k_2517_; lean_object* v_l_2518_; lean_object* v_r_2519_; uint8_t v___x_2520_; 
v_k_2517_ = lean_ctor_get(v_t_2516_, 1);
v_l_2518_ = lean_ctor_get(v_t_2516_, 3);
v_r_2519_ = lean_ctor_get(v_t_2516_, 4);
v___x_2520_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2515_, v_k_2517_);
switch(v___x_2520_)
{
case 0:
{
v_t_2516_ = v_l_2518_;
goto _start;
}
case 1:
{
uint8_t v___x_2522_; 
v___x_2522_ = 1;
return v___x_2522_;
}
default: 
{
v_t_2516_ = v_r_2519_;
goto _start;
}
}
}
else
{
uint8_t v___x_2524_; 
v___x_2524_ = 0;
return v___x_2524_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg___boxed(lean_object* v_k_2525_, lean_object* v_t_2526_){
_start:
{
uint8_t v_res_2527_; lean_object* v_r_2528_; 
v_res_2527_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_k_2525_, v_t_2526_);
lean_dec(v_t_2526_);
lean_dec(v_k_2525_);
v_r_2528_ = lean_box(v_res_2527_);
return v_r_2528_;
}
}
LEAN_EXPORT uint8_t l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(lean_object* v_a_2529_, uint8_t v___x_2530_, lean_object* v_before_2531_, lean_object* v_after_2532_){
_start:
{
lean_object* v___x_2533_; 
v___x_2533_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(v_a_2529_, v_before_2531_);
if (lean_obj_tag(v___x_2533_) == 0)
{
return v___x_2530_;
}
else
{
lean_object* v_val_2534_; uint8_t v___x_2535_; 
v_val_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_val_2534_);
lean_dec_ref_known(v___x_2533_, 1);
v___x_2535_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_after_2532_, v_val_2534_);
lean_dec(v_val_2534_);
return v___x_2535_;
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0___boxed(lean_object* v_a_2536_, lean_object* v___x_2537_, lean_object* v_before_2538_, lean_object* v_after_2539_){
_start:
{
uint8_t v___x_3249__boxed_2540_; uint8_t v_res_2541_; lean_object* v_r_2542_; 
v___x_3249__boxed_2540_ = lean_unbox(v___x_2537_);
v_res_2541_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(v_a_2536_, v___x_3249__boxed_2540_, v_before_2538_, v_after_2539_);
lean_dec(v_after_2539_);
lean_dec(v_before_2538_);
lean_dec(v_a_2536_);
v_r_2542_ = lean_box(v_res_2541_);
return v_r_2542_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5(uint8_t v_useAfter_2543_, lean_object* v_a_2544_, lean_object* v___x_2545_, lean_object* v_x_2546_){
_start:
{
if (lean_obj_tag(v_x_2546_) == 0)
{
lean_object* v___x_2547_; 
v___x_2547_ = lean_box(0);
return v___x_2547_;
}
else
{
lean_object* v_head_2548_; lean_object* v_tail_2549_; uint8_t v___y_2551_; uint8_t v___x_2554_; 
v_head_2548_ = lean_ctor_get(v_x_2546_, 0);
v_tail_2549_ = lean_ctor_get(v_x_2546_, 1);
v___x_2554_ = 0;
if (v_useAfter_2543_ == 0)
{
uint8_t v___x_2555_; 
v___x_2555_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(v_a_2544_, v___x_2554_, v___x_2545_, v_head_2548_);
v___y_2551_ = v___x_2555_;
goto v___jp_2550_;
}
else
{
uint8_t v___x_2556_; 
v___x_2556_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(v_a_2544_, v___x_2554_, v_head_2548_, v___x_2545_);
v___y_2551_ = v___x_2556_;
goto v___jp_2550_;
}
v___jp_2550_:
{
if (v___y_2551_ == 0)
{
v_x_2546_ = v_tail_2549_;
goto _start;
}
else
{
lean_object* v___x_2553_; 
lean_inc(v_head_2548_);
v___x_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2553_, 0, v_head_2548_);
return v___x_2553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___boxed(lean_object* v_useAfter_2557_, lean_object* v_a_2558_, lean_object* v___x_2559_, lean_object* v_x_2560_){
_start:
{
uint8_t v_useAfter_boxed_2561_; lean_object* v_res_2562_; 
v_useAfter_boxed_2561_ = lean_unbox(v_useAfter_2557_);
v_res_2562_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5(v_useAfter_boxed_2561_, v_a_2558_, v___x_2559_, v_x_2560_);
lean_dec(v_x_2560_);
lean_dec(v___x_2559_);
lean_dec(v_a_2558_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0(lean_object* v_mvarId_2563_, lean_object* v___y_2564_, uint8_t v_useAfter_2565_, lean_object* v_a_2566_, lean_object* v_v_2567_, uint8_t v___x_2568_, lean_object* v_toInteractiveGoalCore_2569_, lean_object* v_userName_x3f_2570_, lean_object* v_goalPrefix_2571_, lean_object* v_isInserted_x3f_2572_, lean_object* v_isRemoved_x3f_2573_, lean_object* v___lctx_u2081_2574_, lean_object* v___md_u2081_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
uint8_t v___x_2581_; 
v___x_2581_ = l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4(v_mvarId_2563_, v___y_2564_);
if (v___x_2581_ == 0)
{
lean_object* v___x_2582_; 
v___x_2582_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5(v_useAfter_2565_, v_a_2566_, v_mvarId_2563_, v___y_2564_);
if (lean_obj_tag(v___x_2582_) == 1)
{
lean_object* v_val_2583_; lean_object* v___x_2584_; 
lean_dec(v_isRemoved_x3f_2573_);
lean_dec(v_isInserted_x3f_2572_);
lean_dec_ref(v_goalPrefix_2571_);
lean_dec(v_userName_x3f_2570_);
lean_dec_ref(v_toInteractiveGoalCore_2569_);
lean_dec(v_mvarId_2563_);
v_val_2583_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_val_2583_);
lean_dec_ref_known(v___x_2582_, 1);
v___x_2584_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(v_useAfter_2565_, v_val_2583_, v_v_2567_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
return v___x_2584_;
}
else
{
lean_dec(v___x_2582_);
lean_dec(v_v_2567_);
if (v_useAfter_2565_ == 0)
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
lean_dec(v_isRemoved_x3f_2573_);
v___x_2585_ = lean_box(v___x_2568_);
v___x_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2585_);
v___x_2587_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2587_, 0, v_toInteractiveGoalCore_2569_);
lean_ctor_set(v___x_2587_, 1, v_userName_x3f_2570_);
lean_ctor_set(v___x_2587_, 2, v_goalPrefix_2571_);
lean_ctor_set(v___x_2587_, 3, v_mvarId_2563_);
lean_ctor_set(v___x_2587_, 4, v_isInserted_x3f_2572_);
lean_ctor_set(v___x_2587_, 5, v___x_2586_);
v___x_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
return v___x_2588_;
}
else
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
lean_dec(v_isInserted_x3f_2572_);
v___x_2589_ = lean_box(v___x_2568_);
v___x_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
v___x_2591_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2591_, 0, v_toInteractiveGoalCore_2569_);
lean_ctor_set(v___x_2591_, 1, v_userName_x3f_2570_);
lean_ctor_set(v___x_2591_, 2, v_goalPrefix_2571_);
lean_ctor_set(v___x_2591_, 3, v_mvarId_2563_);
lean_ctor_set(v___x_2591_, 4, v___x_2590_);
lean_ctor_set(v___x_2591_, 5, v_isRemoved_x3f_2573_);
v___x_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
return v___x_2592_;
}
}
}
else
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
lean_dec(v_isInserted_x3f_2572_);
lean_dec(v_v_2567_);
v___x_2593_ = lean_box(0);
v___x_2594_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2594_, 0, v_toInteractiveGoalCore_2569_);
lean_ctor_set(v___x_2594_, 1, v_userName_x3f_2570_);
lean_ctor_set(v___x_2594_, 2, v_goalPrefix_2571_);
lean_ctor_set(v___x_2594_, 3, v_mvarId_2563_);
lean_ctor_set(v___x_2594_, 4, v___x_2593_);
lean_ctor_set(v___x_2594_, 5, v_isRemoved_x3f_2573_);
v___x_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
return v___x_2595_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0___boxed(lean_object** _args){
lean_object* v_mvarId_2596_ = _args[0];
lean_object* v___y_2597_ = _args[1];
lean_object* v_useAfter_2598_ = _args[2];
lean_object* v_a_2599_ = _args[3];
lean_object* v_v_2600_ = _args[4];
lean_object* v___x_2601_ = _args[5];
lean_object* v_toInteractiveGoalCore_2602_ = _args[6];
lean_object* v_userName_x3f_2603_ = _args[7];
lean_object* v_goalPrefix_2604_ = _args[8];
lean_object* v_isInserted_x3f_2605_ = _args[9];
lean_object* v_isRemoved_x3f_2606_ = _args[10];
lean_object* v___lctx_u2081_2607_ = _args[11];
lean_object* v___md_u2081_2608_ = _args[12];
lean_object* v___y_2609_ = _args[13];
lean_object* v___y_2610_ = _args[14];
lean_object* v___y_2611_ = _args[15];
lean_object* v___y_2612_ = _args[16];
lean_object* v___y_2613_ = _args[17];
_start:
{
uint8_t v_useAfter_boxed_2614_; uint8_t v___x_3291__boxed_2615_; lean_object* v_res_2616_; 
v_useAfter_boxed_2614_ = lean_unbox(v_useAfter_2598_);
v___x_3291__boxed_2615_ = lean_unbox(v___x_2601_);
v_res_2616_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0(v_mvarId_2596_, v___y_2597_, v_useAfter_boxed_2614_, v_a_2599_, v_v_2600_, v___x_3291__boxed_2615_, v_toInteractiveGoalCore_2602_, v_userName_x3f_2603_, v_goalPrefix_2604_, v_isInserted_x3f_2605_, v_isRemoved_x3f_2606_, v___lctx_u2081_2607_, v___md_u2081_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec_ref(v___md_u2081_2608_);
lean_dec_ref(v___lctx_u2081_2607_);
lean_dec(v_a_2599_);
lean_dec(v___y_2597_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8(lean_object* v___y_2617_, uint8_t v_useAfter_2618_, lean_object* v_a_2619_, uint8_t v___x_2620_, size_t v_sz_2621_, size_t v_i_2622_, lean_object* v_bs_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
uint8_t v___x_2629_; 
v___x_2629_ = lean_usize_dec_lt(v_i_2622_, v_sz_2621_);
if (v___x_2629_ == 0)
{
lean_object* v___x_2630_; 
lean_dec(v_a_2619_);
lean_dec(v___y_2617_);
v___x_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2630_, 0, v_bs_2623_);
return v___x_2630_;
}
else
{
lean_object* v_v_2631_; lean_object* v_toInteractiveGoalCore_2632_; lean_object* v_userName_x3f_2633_; lean_object* v_goalPrefix_2634_; lean_object* v_mvarId_2635_; lean_object* v_isInserted_x3f_2636_; lean_object* v_isRemoved_x3f_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___f_2640_; lean_object* v___x_2641_; 
v_v_2631_ = lean_array_uget_borrowed(v_bs_2623_, v_i_2622_);
v_toInteractiveGoalCore_2632_ = lean_ctor_get(v_v_2631_, 0);
v_userName_x3f_2633_ = lean_ctor_get(v_v_2631_, 1);
v_goalPrefix_2634_ = lean_ctor_get(v_v_2631_, 2);
v_mvarId_2635_ = lean_ctor_get(v_v_2631_, 3);
v_isInserted_x3f_2636_ = lean_ctor_get(v_v_2631_, 4);
v_isRemoved_x3f_2637_ = lean_ctor_get(v_v_2631_, 5);
v___x_2638_ = lean_box(v_useAfter_2618_);
v___x_2639_ = lean_box(v___x_2620_);
lean_inc(v_isRemoved_x3f_2637_);
lean_inc(v_isInserted_x3f_2636_);
lean_inc_ref(v_goalPrefix_2634_);
lean_inc(v_userName_x3f_2633_);
lean_inc_ref(v_toInteractiveGoalCore_2632_);
lean_inc(v_v_2631_);
lean_inc(v_a_2619_);
lean_inc(v___y_2617_);
lean_inc_n(v_mvarId_2635_, 2);
v___f_2640_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0___boxed), 18, 11);
lean_closure_set(v___f_2640_, 0, v_mvarId_2635_);
lean_closure_set(v___f_2640_, 1, v___y_2617_);
lean_closure_set(v___f_2640_, 2, v___x_2638_);
lean_closure_set(v___f_2640_, 3, v_a_2619_);
lean_closure_set(v___f_2640_, 4, v_v_2631_);
lean_closure_set(v___f_2640_, 5, v___x_2639_);
lean_closure_set(v___f_2640_, 6, v_toInteractiveGoalCore_2632_);
lean_closure_set(v___f_2640_, 7, v_userName_x3f_2633_);
lean_closure_set(v___f_2640_, 8, v_goalPrefix_2634_);
lean_closure_set(v___f_2640_, 9, v_isInserted_x3f_2636_);
lean_closure_set(v___f_2640_, 10, v_isRemoved_x3f_2637_);
v___x_2641_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(v_mvarId_2635_, v___f_2640_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; lean_object* v___x_2643_; lean_object* v_bs_x27_2644_; size_t v___x_2645_; size_t v___x_2646_; lean_object* v___x_2647_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_a_2642_);
lean_dec_ref_known(v___x_2641_, 1);
v___x_2643_ = lean_unsigned_to_nat(0u);
v_bs_x27_2644_ = lean_array_uset(v_bs_2623_, v_i_2622_, v___x_2643_);
v___x_2645_ = ((size_t)1ULL);
v___x_2646_ = lean_usize_add(v_i_2622_, v___x_2645_);
v___x_2647_ = lean_array_uset(v_bs_x27_2644_, v_i_2622_, v_a_2642_);
v_i_2622_ = v___x_2646_;
v_bs_2623_ = v___x_2647_;
goto _start;
}
else
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
lean_dec_ref(v_bs_2623_);
lean_dec(v_a_2619_);
lean_dec(v___y_2617_);
v_a_2649_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2651_ = v___x_2641_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2641_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2654_; 
if (v_isShared_2652_ == 0)
{
v___x_2654_ = v___x_2651_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2649_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8___boxed(lean_object* v___y_2657_, lean_object* v_useAfter_2658_, lean_object* v_a_2659_, lean_object* v___x_2660_, lean_object* v_sz_2661_, lean_object* v_i_2662_, lean_object* v_bs_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
uint8_t v_useAfter_boxed_2669_; uint8_t v___x_3345__boxed_2670_; size_t v_sz_boxed_2671_; size_t v_i_boxed_2672_; lean_object* v_res_2673_; 
v_useAfter_boxed_2669_ = lean_unbox(v_useAfter_2658_);
v___x_3345__boxed_2670_ = lean_unbox(v___x_2660_);
v_sz_boxed_2671_ = lean_unbox_usize(v_sz_2661_);
lean_dec(v_sz_2661_);
v_i_boxed_2672_ = lean_unbox_usize(v_i_2662_);
lean_dec(v_i_2662_);
v_res_2673_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8(v___y_2657_, v_useAfter_boxed_2669_, v_a_2659_, v___x_3345__boxed_2670_, v_sz_boxed_2671_, v_i_boxed_2672_, v_bs_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7(uint8_t v_useAfter_2674_, lean_object* v_a_2675_, lean_object* v___y_2676_, uint8_t v___x_2677_, size_t v_sz_2678_, size_t v_i_2679_, lean_object* v_bs_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
uint8_t v___x_2686_; 
v___x_2686_ = lean_usize_dec_lt(v_i_2679_, v_sz_2678_);
if (v___x_2686_ == 0)
{
lean_object* v___x_2687_; 
lean_dec(v___y_2676_);
lean_dec(v_a_2675_);
v___x_2687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2687_, 0, v_bs_2680_);
return v___x_2687_;
}
else
{
lean_object* v_v_2688_; lean_object* v_toInteractiveGoalCore_2689_; lean_object* v_userName_x3f_2690_; lean_object* v_goalPrefix_2691_; lean_object* v_mvarId_2692_; lean_object* v_isInserted_x3f_2693_; lean_object* v_isRemoved_x3f_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___f_2697_; lean_object* v___x_2698_; 
v_v_2688_ = lean_array_uget_borrowed(v_bs_2680_, v_i_2679_);
v_toInteractiveGoalCore_2689_ = lean_ctor_get(v_v_2688_, 0);
v_userName_x3f_2690_ = lean_ctor_get(v_v_2688_, 1);
v_goalPrefix_2691_ = lean_ctor_get(v_v_2688_, 2);
v_mvarId_2692_ = lean_ctor_get(v_v_2688_, 3);
v_isInserted_x3f_2693_ = lean_ctor_get(v_v_2688_, 4);
v_isRemoved_x3f_2694_ = lean_ctor_get(v_v_2688_, 5);
v___x_2695_ = lean_box(v_useAfter_2674_);
v___x_2696_ = lean_box(v___x_2677_);
lean_inc(v_isRemoved_x3f_2694_);
lean_inc(v_isInserted_x3f_2693_);
lean_inc_ref(v_goalPrefix_2691_);
lean_inc(v_userName_x3f_2690_);
lean_inc_ref(v_toInteractiveGoalCore_2689_);
lean_inc(v_v_2688_);
lean_inc(v_a_2675_);
lean_inc(v___y_2676_);
lean_inc_n(v_mvarId_2692_, 2);
v___f_2697_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0___boxed), 18, 11);
lean_closure_set(v___f_2697_, 0, v_mvarId_2692_);
lean_closure_set(v___f_2697_, 1, v___y_2676_);
lean_closure_set(v___f_2697_, 2, v___x_2695_);
lean_closure_set(v___f_2697_, 3, v_a_2675_);
lean_closure_set(v___f_2697_, 4, v_v_2688_);
lean_closure_set(v___f_2697_, 5, v___x_2696_);
lean_closure_set(v___f_2697_, 6, v_toInteractiveGoalCore_2689_);
lean_closure_set(v___f_2697_, 7, v_userName_x3f_2690_);
lean_closure_set(v___f_2697_, 8, v_goalPrefix_2691_);
lean_closure_set(v___f_2697_, 9, v_isInserted_x3f_2693_);
lean_closure_set(v___f_2697_, 10, v_isRemoved_x3f_2694_);
v___x_2698_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(v_mvarId_2692_, v___f_2697_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; lean_object* v___x_2700_; lean_object* v_bs_x27_2701_; size_t v___x_2702_; size_t v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2699_);
lean_dec_ref_known(v___x_2698_, 1);
v___x_2700_ = lean_unsigned_to_nat(0u);
v_bs_x27_2701_ = lean_array_uset(v_bs_2680_, v_i_2679_, v___x_2700_);
v___x_2702_ = ((size_t)1ULL);
v___x_2703_ = lean_usize_add(v_i_2679_, v___x_2702_);
v___x_2704_ = lean_array_uset(v_bs_x27_2701_, v_i_2679_, v_a_2699_);
v___x_2705_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8(v___y_2676_, v_useAfter_2674_, v_a_2675_, v___x_2677_, v_sz_2678_, v___x_2703_, v___x_2704_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
return v___x_2705_;
}
else
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
lean_dec_ref(v_bs_2680_);
lean_dec(v___y_2676_);
lean_dec(v_a_2675_);
v_a_2706_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2698_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2698_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___boxed(lean_object* v_useAfter_2714_, lean_object* v_a_2715_, lean_object* v___y_2716_, lean_object* v___x_2717_, lean_object* v_sz_2718_, lean_object* v_i_2719_, lean_object* v_bs_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
uint8_t v_useAfter_boxed_2726_; uint8_t v___x_3409__boxed_2727_; size_t v_sz_boxed_2728_; size_t v_i_boxed_2729_; lean_object* v_res_2730_; 
v_useAfter_boxed_2726_ = lean_unbox(v_useAfter_2714_);
v___x_3409__boxed_2727_ = lean_unbox(v___x_2717_);
v_sz_boxed_2728_ = lean_unbox_usize(v_sz_2718_);
lean_dec(v_sz_2718_);
v_i_boxed_2729_ = lean_unbox_usize(v_i_2719_);
lean_dec(v_i_2719_);
v_res_2730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7(v_useAfter_boxed_2726_, v_a_2715_, v___y_2716_, v___x_3409__boxed_2727_, v_sz_boxed_2728_, v_i_boxed_2729_, v_bs_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_diffInteractiveGoals(uint8_t v_useAfter_2731_, lean_object* v_info_2732_, lean_object* v_igs_u2081_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_){
_start:
{
lean_object* v_options_2739_; lean_object* v___x_2740_; uint8_t v___x_2741_; lean_object* v___y_2743_; 
v_options_2739_ = lean_ctor_get(v_a_2736_, 1);
v___x_2740_ = l___private_Lean_Widget_Diff_0__Lean_Widget_showTacticDiff;
v___x_2741_ = l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(v_options_2739_, v___x_2740_);
if (v___x_2741_ == 0)
{
lean_object* v___x_2775_; 
lean_dec_ref(v_info_2732_);
v___x_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2775_, 0, v_igs_u2081_2733_);
return v___x_2775_;
}
else
{
if (v_useAfter_2731_ == 0)
{
lean_object* v_goalsAfter_2776_; 
v_goalsAfter_2776_ = lean_ctor_get(v_info_2732_, 4);
lean_inc(v_goalsAfter_2776_);
v___y_2743_ = v_goalsAfter_2776_;
goto v___jp_2742_;
}
else
{
lean_object* v_goalsBefore_2777_; 
v_goalsBefore_2777_ = lean_ctor_get(v_info_2732_, 2);
lean_inc(v_goalsBefore_2777_);
v___y_2743_ = v_goalsBefore_2777_;
goto v___jp_2742_;
}
}
v___jp_2742_:
{
lean_object* v_goalsBefore_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v_goalsBefore_2744_ = lean_ctor_get(v_info_2732_, 2);
lean_inc(v_goalsBefore_2744_);
lean_dec_ref(v_info_2732_);
v___x_2745_ = lean_box(1);
v___x_2746_ = l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(v___x_2745_, v_goalsBefore_2744_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; size_t v_sz_2748_; size_t v___x_2749_; lean_object* v___x_2750_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2747_);
lean_dec_ref_known(v___x_2746_, 1);
v_sz_2748_ = lean_array_size(v_igs_u2081_2733_);
v___x_2749_ = ((size_t)0ULL);
v___x_2750_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7(v_useAfter_2731_, v_a_2747_, v___y_2743_, v___x_2741_, v_sz_2748_, v___x_2749_, v_igs_u2081_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2750_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2750_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
else
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2766_; 
v_a_2759_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2761_ = v___x_2750_;
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2750_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2764_; 
if (v_isShared_2762_ == 0)
{
v___x_2764_ = v___x_2761_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_a_2759_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
lean_dec(v___y_2743_);
lean_dec_ref(v_igs_u2081_2733_);
v_a_2767_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2746_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2746_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
if (v_isShared_2770_ == 0)
{
v___x_2772_ = v___x_2769_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_diffInteractiveGoals___boxed(lean_object* v_useAfter_2778_, lean_object* v_info_2779_, lean_object* v_igs_u2081_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_){
_start:
{
uint8_t v_useAfter_boxed_2786_; lean_object* v_res_2787_; 
v_useAfter_boxed_2786_ = lean_unbox(v_useAfter_2778_);
v_res_2787_ = l_Lean_Widget_diffInteractiveGoals(v_useAfter_boxed_2786_, v_info_2779_, v_igs_u2081_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_);
lean_dec(v_a_2784_);
lean_dec_ref(v_a_2783_);
lean_dec(v_a_2782_);
lean_dec_ref(v_a_2781_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2(lean_object* v_00_u03b4_2788_, lean_object* v_t_2789_, lean_object* v_k_2790_){
_start:
{
lean_object* v___x_2791_; 
v___x_2791_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(v_t_2789_, v_k_2790_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___boxed(lean_object* v_00_u03b4_2792_, lean_object* v_t_2793_, lean_object* v_k_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2(v_00_u03b4_2792_, v_t_2793_, v_k_2794_);
lean_dec(v_k_2794_);
lean_dec(v_t_2793_);
return v_res_2795_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3(lean_object* v_00_u03b2_2796_, lean_object* v_k_2797_, lean_object* v_t_2798_){
_start:
{
uint8_t v___x_2799_; 
v___x_2799_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_k_2797_, v_t_2798_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___boxed(lean_object* v_00_u03b2_2800_, lean_object* v_k_2801_, lean_object* v_t_2802_){
_start:
{
uint8_t v_res_2803_; lean_object* v_r_2804_; 
v_res_2803_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3(v_00_u03b2_2800_, v_k_2801_, v_t_2802_);
lean_dec(v_t_2802_);
lean_dec(v_k_2801_);
v_r_2804_ = lean_box(v_res_2803_);
return v_r_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6(lean_object* v_00_u03b1_2805_, lean_object* v_lctx_2806_, lean_object* v_localInsts_2807_, lean_object* v_x_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
lean_object* v___x_2814_; 
v___x_2814_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(v_lctx_2806_, v_localInsts_2807_, v_x_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___boxed(lean_object* v_00_u03b1_2815_, lean_object* v_lctx_2816_, lean_object* v_localInsts_2817_, lean_object* v_x_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6(v_00_u03b1_2815_, v_lctx_2816_, v_localInsts_2817_, v_x_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6(lean_object* v_00_u03b1_2825_, lean_object* v_goal_2826_, lean_object* v_action_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v___x_2833_; 
v___x_2833_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(v_goal_2826_, v_action_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___boxed(lean_object* v_00_u03b1_2834_, lean_object* v_goal_2835_, lean_object* v_action_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_){
_start:
{
lean_object* v_res_2842_; 
v_res_2842_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6(v_00_u03b1_2834_, v_goal_2835_, v_action_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
return v_res_2842_;
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
