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
lean_object* v___x_764_; lean_object* v_env_765_; lean_object* v___x_766_; lean_object* v_toCold_767_; lean_object* v_mctx_768_; lean_object* v_lctx_769_; lean_object* v_options_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_764_ = lean_st_ref_get(v___y_762_);
v_env_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc_ref(v_env_765_);
lean_dec(v___x_764_);
v___x_766_ = lean_st_ref_get(v___y_760_);
v_toCold_767_ = lean_ctor_get(v___y_761_, 0);
v_mctx_768_ = lean_ctor_get(v___x_766_, 0);
lean_inc_ref(v_mctx_768_);
lean_dec(v___x_766_);
v_lctx_769_ = lean_ctor_get(v___y_759_, 2);
v_options_770_ = lean_ctor_get(v_toCold_767_, 2);
lean_inc_ref(v_options_770_);
lean_inc_ref(v_lctx_769_);
v___x_771_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_771_, 0, v_env_765_);
lean_ctor_set(v___x_771_, 1, v_mctx_768_);
lean_ctor_set(v___x_771_, 2, v_lctx_769_);
lean_ctor_set(v___x_771_, 3, v_options_770_);
v___x_772_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
lean_ctor_set(v___x_772_, 1, v_msgData_758_);
v___x_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4___boxed(lean_object* v_msgData_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(v_msgData_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(lean_object* v_msg_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_ref_787_; lean_object* v___x_788_; lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_797_; 
v_ref_787_ = lean_ctor_get(v___y_784_, 2);
v___x_788_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(v_msg_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_797_ == 0)
{
v___x_791_ = v___x_788_;
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_795_; 
lean_inc(v_ref_787_);
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v_ref_787_);
lean_ctor_set(v___x_793_, 1, v_a_789_);
if (v_isShared_792_ == 0)
{
lean_ctor_set_tag(v___x_791_, 1);
lean_ctor_set(v___x_791_, 0, v___x_793_);
v___x_795_ = v___x_791_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg___boxed(lean_object* v_msg_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v_msg_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(lean_object* v_x_805_, lean_object* v_x_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
if (lean_obj_tag(v_x_805_) == 0)
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = l_List_reverse___redArg(v_x_806_);
v___x_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
return v___x_813_;
}
else
{
lean_object* v_head_814_; lean_object* v_tail_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_833_; 
v_head_814_ = lean_ctor_get(v_x_805_, 0);
v_tail_815_ = lean_ctor_get(v_x_805_, 1);
v_isSharedCheck_833_ = !lean_is_exclusive(v_x_805_);
if (v_isSharedCheck_833_ == 0)
{
v___x_817_ = v_x_805_;
v_isShared_818_ = v_isSharedCheck_833_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_tail_815_);
lean_inc(v_head_814_);
lean_dec(v_x_805_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_833_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_819_; 
v___x_819_ = l_Lean_Meta_getFVarFromUserName(v_head_814_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v___x_822_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_a_820_);
lean_dec_ref_known(v___x_819_, 1);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 1, v_x_806_);
lean_ctor_set(v___x_817_, 0, v_a_820_);
v___x_822_ = v___x_817_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_820_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v_x_806_);
v___x_822_ = v_reuseFailAlloc_824_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
v_x_805_ = v_tail_815_;
v_x_806_ = v___x_822_;
goto _start;
}
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_del_object(v___x_817_);
lean_dec(v_tail_815_);
lean_dec(v_x_806_);
v_a_825_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_819_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_819_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2___boxed(lean_object* v_x_834_, lean_object* v_x_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(v_x_834_, v_x_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(lean_object* v_upperBound_842_, lean_object* v_before_843_, lean_object* v_a_844_, lean_object* v_b_845_){
_start:
{
uint8_t v___x_847_; 
v___x_847_ = lean_nat_dec_lt(v_a_844_, v_upperBound_842_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; 
lean_dec(v_a_844_);
lean_dec_ref(v_before_843_);
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v_b_845_);
return v___x_848_;
}
else
{
lean_object* v_pos_849_; lean_object* v___x_850_; uint8_t v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v_pos_849_ = lean_ctor_get(v_before_843_, 1);
lean_inc(v_pos_849_);
lean_inc(v_a_844_);
v___x_850_ = l_Lean_SubExpr_Pos_pushNthBindingDomain(v_a_844_, v_pos_849_);
v___x_851_ = 1;
v___x_852_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange(v___x_850_, v___x_851_, v_b_845_);
v___x_853_ = lean_unsigned_to_nat(1u);
v___x_854_ = lean_nat_add(v_a_844_, v___x_853_);
lean_dec(v_a_844_);
v_a_844_ = v___x_854_;
v_b_845_ = v___x_852_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg___boxed(lean_object* v_upperBound_856_, lean_object* v_before_857_, lean_object* v_a_858_, lean_object* v_b_859_, lean_object* v___y_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v_upperBound_856_, v_before_857_, v_a_858_, v_b_859_);
lean_dec(v_upperBound_856_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0(lean_object* v_x_862_, lean_object* v_x_863_){
_start:
{
if (lean_obj_tag(v_x_862_) == 0)
{
lean_object* v___x_864_; 
v___x_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_864_, 0, v_x_863_);
return v___x_864_;
}
else
{
if (lean_obj_tag(v_x_863_) == 0)
{
lean_object* v___x_865_; 
v___x_865_ = lean_box(0);
return v___x_865_;
}
else
{
lean_object* v_head_866_; lean_object* v_tail_867_; lean_object* v_head_868_; lean_object* v_tail_869_; uint8_t v___x_870_; 
v_head_866_ = lean_ctor_get(v_x_862_, 0);
v_tail_867_ = lean_ctor_get(v_x_862_, 1);
v_head_868_ = lean_ctor_get(v_x_863_, 0);
lean_inc(v_head_868_);
v_tail_869_ = lean_ctor_get(v_x_863_, 1);
lean_inc(v_tail_869_);
lean_dec_ref_known(v_x_863_, 2);
v___x_870_ = lean_name_eq(v_head_866_, v_head_868_);
lean_dec(v_head_868_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; 
lean_dec(v_tail_869_);
v___x_871_ = lean_box(0);
return v___x_871_;
}
else
{
v_x_862_ = v_tail_867_;
v_x_863_ = v_tail_869_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0___boxed(lean_object* v_x_873_, lean_object* v_x_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0(v_x_873_, v_x_874_);
lean_dec(v_x_873_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0(lean_object* v_l_u2081_876_, lean_object* v_l_u2082_877_){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_878_ = l_List_reverse___redArg(v_l_u2081_876_);
v___x_879_ = l_List_reverse___redArg(v_l_u2082_877_);
v___x_880_ = l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0(v___x_878_, v___x_879_);
lean_dec(v___x_878_);
if (lean_obj_tag(v___x_880_) == 0)
{
return v___x_880_;
}
else
{
lean_object* v_val_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_889_; 
v_val_881_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_889_ == 0)
{
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_889_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_val_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_889_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_885_ = l_List_reverse___redArg(v_val_881_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_885_);
v___x_887_ = v___x_883_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(uint8_t v_b_u2082_890_, lean_object* v_k_891_, lean_object* v_t_892_){
_start:
{
if (lean_obj_tag(v_t_892_) == 0)
{
lean_object* v_size_893_; lean_object* v_k_894_; lean_object* v_v_895_; lean_object* v_l_896_; lean_object* v_r_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_911_; 
v_size_893_ = lean_ctor_get(v_t_892_, 0);
v_k_894_ = lean_ctor_get(v_t_892_, 1);
v_v_895_ = lean_ctor_get(v_t_892_, 2);
v_l_896_ = lean_ctor_get(v_t_892_, 3);
v_r_897_ = lean_ctor_get(v_t_892_, 4);
v_isSharedCheck_911_ = !lean_is_exclusive(v_t_892_);
if (v_isSharedCheck_911_ == 0)
{
v___x_899_ = v_t_892_;
v_isShared_900_ = v_isSharedCheck_911_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_r_897_);
lean_inc(v_l_896_);
lean_inc(v_v_895_);
lean_inc(v_k_894_);
lean_inc(v_size_893_);
lean_dec(v_t_892_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_911_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
uint8_t v___x_901_; 
v___x_901_ = lean_nat_dec_lt(v_k_891_, v_k_894_);
if (v___x_901_ == 0)
{
uint8_t v___x_902_; 
v___x_902_ = lean_nat_dec_eq(v_k_891_, v_k_894_);
if (v___x_902_ == 0)
{
lean_object* v_impl_903_; lean_object* v___x_904_; 
lean_del_object(v___x_899_);
lean_dec(v_size_893_);
v_impl_903_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_890_, v_k_891_, v_r_897_);
v___x_904_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_894_, v_v_895_, v_l_896_, v_impl_903_);
return v___x_904_;
}
else
{
lean_object* v___x_905_; lean_object* v___x_907_; 
lean_dec(v_v_895_);
lean_dec(v_k_894_);
v___x_905_ = lean_box(v_b_u2082_890_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 2, v___x_905_);
lean_ctor_set(v___x_899_, 1, v_k_891_);
v___x_907_ = v___x_899_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_size_893_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_k_891_);
lean_ctor_set(v_reuseFailAlloc_908_, 2, v___x_905_);
lean_ctor_set(v_reuseFailAlloc_908_, 3, v_l_896_);
lean_ctor_set(v_reuseFailAlloc_908_, 4, v_r_897_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
else
{
lean_object* v_impl_909_; lean_object* v___x_910_; 
lean_del_object(v___x_899_);
lean_dec(v_size_893_);
v_impl_909_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_890_, v_k_891_, v_l_896_);
v___x_910_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_894_, v_v_895_, v_impl_909_, v_r_897_);
return v___x_910_;
}
}
}
else
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_912_ = lean_unsigned_to_nat(1u);
v___x_913_ = lean_box(v_b_u2082_890_);
v___x_914_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_914_, 0, v___x_912_);
lean_ctor_set(v___x_914_, 1, v_k_891_);
lean_ctor_set(v___x_914_, 2, v___x_913_);
lean_ctor_set(v___x_914_, 3, v_t_892_);
lean_ctor_set(v___x_914_, 4, v_t_892_);
return v___x_914_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg___boxed(lean_object* v_b_u2082_915_, lean_object* v_k_916_, lean_object* v_t_917_){
_start:
{
uint8_t v_b_u2082_boxed_918_; lean_object* v_res_919_; 
v_b_u2082_boxed_918_ = lean_unbox(v_b_u2082_915_);
v_res_919_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_boxed_918_, v_k_916_, v_t_917_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(lean_object* v_init_920_, lean_object* v_x_921_){
_start:
{
if (lean_obj_tag(v_x_921_) == 0)
{
lean_object* v_k_922_; lean_object* v_v_923_; lean_object* v_l_924_; lean_object* v_r_925_; lean_object* v___x_926_; uint8_t v___x_927_; lean_object* v___x_928_; 
v_k_922_ = lean_ctor_get(v_x_921_, 1);
lean_inc(v_k_922_);
v_v_923_ = lean_ctor_get(v_x_921_, 2);
lean_inc(v_v_923_);
v_l_924_ = lean_ctor_get(v_x_921_, 3);
lean_inc(v_l_924_);
v_r_925_ = lean_ctor_get(v_x_921_, 4);
lean_inc(v_r_925_);
lean_dec_ref_known(v_x_921_, 5);
v___x_926_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_init_920_, v_l_924_);
v___x_927_ = lean_unbox(v_v_923_);
lean_dec(v_v_923_);
v___x_928_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v___x_927_, v_k_922_, v___x_926_);
v_init_920_ = v___x_928_;
v_x_921_ = v_r_925_;
goto _start;
}
else
{
return v_init_920_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(lean_object* v_as_930_, size_t v_i_931_, size_t v_stop_932_, lean_object* v_b_933_){
_start:
{
uint8_t v___x_934_; 
v___x_934_ = lean_usize_dec_eq(v_i_931_, v_stop_932_);
if (v___x_934_ == 0)
{
lean_object* v_changesBefore_935_; lean_object* v_changesAfter_936_; lean_object* v___x_937_; lean_object* v_changesBefore_938_; lean_object* v_changesAfter_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_951_; 
v_changesBefore_935_ = lean_ctor_get(v_b_933_, 0);
lean_inc(v_changesBefore_935_);
v_changesAfter_936_ = lean_ctor_get(v_b_933_, 1);
lean_inc(v_changesAfter_936_);
lean_dec_ref(v_b_933_);
v___x_937_ = lean_array_uget(v_as_930_, v_i_931_);
v_changesBefore_938_ = lean_ctor_get(v___x_937_, 0);
v_changesAfter_939_ = lean_ctor_get(v___x_937_, 1);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_951_ == 0)
{
v___x_941_ = v___x_937_;
v_isShared_942_ = v_isSharedCheck_951_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_changesAfter_939_);
lean_inc(v_changesBefore_938_);
lean_dec(v___x_937_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_951_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_943_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesBefore_935_, v_changesBefore_938_);
v___x_944_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesAfter_936_, v_changesAfter_939_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 1, v___x_944_);
lean_ctor_set(v___x_941_, 0, v___x_943_);
v___x_946_ = v___x_941_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v___x_944_);
v___x_946_ = v_reuseFailAlloc_950_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
size_t v___x_947_; size_t v___x_948_; 
v___x_947_ = ((size_t)1ULL);
v___x_948_ = lean_usize_add(v_i_931_, v___x_947_);
v_i_931_ = v___x_948_;
v_b_933_ = v___x_946_;
goto _start;
}
}
}
else
{
return v_b_933_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10___boxed(lean_object* v_as_952_, lean_object* v_i_953_, lean_object* v_stop_954_, lean_object* v_b_955_){
_start:
{
size_t v_i_boxed_956_; size_t v_stop_boxed_957_; lean_object* v_res_958_; 
v_i_boxed_956_ = lean_unbox_usize(v_i_953_);
lean_dec(v_i_953_);
v_stop_boxed_957_ = lean_unbox_usize(v_stop_954_);
lean_dec(v_stop_954_);
v_res_958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_as_952_, v_i_boxed_956_, v_stop_boxed_957_, v_b_955_);
lean_dec_ref(v_as_952_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(lean_object* v_x_959_, lean_object* v_x_960_, lean_object* v_x_961_){
_start:
{
if (lean_obj_tag(v_x_959_) == 5)
{
lean_object* v_fn_962_; lean_object* v_arg_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v_fn_962_ = lean_ctor_get(v_x_959_, 0);
lean_inc_ref(v_fn_962_);
v_arg_963_ = lean_ctor_get(v_x_959_, 1);
lean_inc_ref(v_arg_963_);
lean_dec_ref_known(v_x_959_, 2);
v___x_964_ = lean_array_set(v_x_960_, v_x_961_, v_arg_963_);
v___x_965_ = lean_unsigned_to_nat(1u);
v___x_966_ = lean_nat_sub(v_x_961_, v___x_965_);
lean_dec(v_x_961_);
v_x_959_ = v_fn_962_;
v_x_960_ = v___x_964_;
v_x_961_ = v___x_966_;
goto _start;
}
else
{
lean_object* v___x_968_; 
lean_dec(v_x_961_);
v___x_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_968_, 0, v_x_959_);
lean_ctor_set(v___x_968_, 1, v_x_960_);
return v___x_968_;
}
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0(void){
_start:
{
lean_object* v___x_969_; lean_object* v_dummy_970_; 
v___x_969_ = lean_box(0);
v_dummy_970_ = l_Lean_Expr_sort___override(v___x_969_);
return v_dummy_970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(lean_object* v_snd_971_, lean_object* v_before_972_, lean_object* v_after_973_, size_t v_sz_974_, size_t v_i_975_, lean_object* v_bs_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
uint8_t v___x_982_; 
v___x_982_ = lean_usize_dec_lt(v_i_975_, v_sz_974_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; 
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v_bs_976_);
return v___x_983_;
}
else
{
lean_object* v_v_984_; lean_object* v_fst_985_; lean_object* v_snd_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1016_; 
v_v_984_ = lean_array_uget(v_bs_976_, v_i_975_);
v_fst_985_ = lean_ctor_get(v_v_984_, 0);
v_snd_986_ = lean_ctor_get(v_v_984_, 1);
v_isSharedCheck_1016_ = !lean_is_exclusive(v_v_984_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_988_ = v_v_984_;
v_isShared_989_ = v_isSharedCheck_1016_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_snd_986_);
lean_inc(v_fst_985_);
lean_dec(v_v_984_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1016_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v_pos_990_; lean_object* v_pos_991_; lean_object* v___x_992_; lean_object* v_bs_x27_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_998_; 
v_pos_990_ = lean_ctor_get(v_before_972_, 1);
v_pos_991_ = lean_ctor_get(v_after_973_, 1);
v___x_992_ = lean_unsigned_to_nat(0u);
v_bs_x27_993_ = lean_array_uset(v_bs_976_, v_i_975_, v___x_992_);
v___x_994_ = lean_usize_to_nat(v_i_975_);
v___x_995_ = lean_array_get_size(v_snd_971_);
v___x_996_ = l_Lean_SubExpr_Pos_pushNaryArg(v___x_995_, v___x_994_, v_pos_990_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 1, v___x_996_);
v___x_998_ = v___x_988_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_fst_985_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v___x_996_);
v___x_998_ = v_reuseFailAlloc_1015_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = l_Lean_SubExpr_Pos_pushNaryArg(v___x_995_, v___x_994_, v_pos_991_);
lean_dec(v___x_994_);
v___x_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1000_, 0, v_snd_986_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_998_, v___x_1000_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; size_t v___x_1003_; size_t v___x_1004_; lean_object* v___x_1005_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref_known(v___x_1001_, 1);
v___x_1003_ = ((size_t)1ULL);
v___x_1004_ = lean_usize_add(v_i_975_, v___x_1003_);
v___x_1005_ = lean_array_uset(v_bs_x27_993_, v_i_975_, v_a_1002_);
v_i_975_ = v___x_1004_;
v_bs_976_ = v___x_1005_;
goto _start;
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec_ref(v_bs_x27_993_);
v_a_1007_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_1001_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1001_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
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
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__0));
v___x_1019_ = l_Lean_stringToMessageData(v___x_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0___boxed(lean_object* v_body_1020_, lean_object* v_pos_1021_, lean_object* v_body_1022_, lean_object* v_pos_1023_, lean_object* v_x_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0(v_body_1020_, v_pos_1021_, v_body_1022_, v_pos_1023_, v_x_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec_ref(v_x_1024_);
lean_dec(v_pos_1023_);
lean_dec_ref(v_body_1022_);
lean_dec(v_pos_1021_);
lean_dec_ref(v_body_1020_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(lean_object* v_before_1031_, lean_object* v_after_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v_a_1044_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; uint8_t v___y_1055_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v_a_1074_; lean_object* v_expr_1077_; lean_object* v_pos_1078_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; 
v_expr_1077_ = lean_ctor_get(v_before_1031_, 0);
v_pos_1078_ = lean_ctor_get(v_before_1031_, 1);
if (lean_obj_tag(v_expr_1077_) == 7)
{
lean_object* v_binderName_1115_; lean_object* v_binderType_1116_; lean_object* v_body_1117_; uint8_t v_binderInfo_1118_; lean_object* v_expr_1119_; lean_object* v_pos_1120_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; 
v_binderName_1115_ = lean_ctor_get(v_expr_1077_, 0);
v_binderType_1116_ = lean_ctor_get(v_expr_1077_, 1);
v_body_1117_ = lean_ctor_get(v_expr_1077_, 2);
v_binderInfo_1118_ = lean_ctor_get_uint8(v_expr_1077_, sizeof(void*)*3 + 8);
v_expr_1119_ = lean_ctor_get(v_after_1032_, 0);
v_pos_1120_ = lean_ctor_get(v_after_1032_, 1);
if (lean_obj_tag(v_expr_1119_) == 7)
{
lean_object* v_binderName_1146_; lean_object* v_binderType_1147_; lean_object* v_body_1148_; uint8_t v_binderInfo_1149_; lean_object* v___f_1150_; uint8_t v___y_1152_; uint8_t v___x_1202_; 
v_binderName_1146_ = lean_ctor_get(v_expr_1119_, 0);
v_binderType_1147_ = lean_ctor_get(v_expr_1119_, 1);
v_body_1148_ = lean_ctor_get(v_expr_1119_, 2);
v_binderInfo_1149_ = lean_ctor_get_uint8(v_expr_1119_, sizeof(void*)*3 + 8);
lean_inc(v_pos_1120_);
lean_inc_ref(v_body_1148_);
lean_inc(v_pos_1078_);
lean_inc_ref(v_body_1117_);
v___f_1150_ = lean_alloc_closure((void*)(l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1150_, 0, v_body_1117_);
lean_closure_set(v___f_1150_, 1, v_pos_1078_);
lean_closure_set(v___f_1150_, 2, v_body_1148_);
lean_closure_set(v___f_1150_, 3, v_pos_1120_);
v___x_1202_ = lean_name_eq(v_binderName_1115_, v_binderName_1146_);
if (v___x_1202_ == 0)
{
v___y_1152_ = v___x_1202_;
goto v___jp_1151_;
}
else
{
uint8_t v___x_1203_; 
v___x_1203_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1118_, v_binderInfo_1149_);
v___y_1152_ = v___x_1203_;
goto v___jp_1151_;
}
v___jp_1151_:
{
if (v___y_1152_ == 0)
{
lean_dec_ref(v___f_1150_);
v___y_1122_ = v_a_1033_;
v___y_1123_ = v_a_1034_;
v___y_1124_ = v_a_1035_;
v___y_1125_ = v_a_1036_;
goto v___jp_1121_;
}
else
{
lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1199_; 
lean_inc_ref(v_binderType_1147_);
lean_inc(v_pos_1120_);
lean_inc_ref(v_binderType_1116_);
lean_inc(v_binderName_1115_);
lean_inc(v_pos_1078_);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_before_1031_);
if (v_isSharedCheck_1199_ == 0)
{
lean_object* v_unused_1200_; lean_object* v_unused_1201_; 
v_unused_1200_ = lean_ctor_get(v_before_1031_, 1);
lean_dec(v_unused_1200_);
v_unused_1201_ = lean_ctor_get(v_before_1031_, 0);
lean_dec(v_unused_1201_);
v___x_1154_ = v_before_1031_;
v_isShared_1155_ = v_isSharedCheck_1199_;
goto v_resetjp_1153_;
}
else
{
lean_dec(v_before_1031_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1199_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1196_; 
v_isSharedCheck_1196_ = !lean_is_exclusive(v_after_1032_);
if (v_isSharedCheck_1196_ == 0)
{
lean_object* v_unused_1197_; lean_object* v_unused_1198_; 
v_unused_1197_ = lean_ctor_get(v_after_1032_, 1);
lean_dec(v_unused_1197_);
v_unused_1198_ = lean_ctor_get(v_after_1032_, 0);
lean_dec(v_unused_1198_);
v___x_1157_ = v_after_1032_;
v_isShared_1158_ = v_isSharedCheck_1196_;
goto v_resetjp_1156_;
}
else
{
lean_dec(v_after_1032_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1196_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1159_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1078_);
lean_inc_ref(v_binderType_1116_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 1, v___x_1159_);
lean_ctor_set(v___x_1157_, 0, v_binderType_1116_);
v___x_1161_ = v___x_1157_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_binderType_1116_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1162_; lean_object* v___x_1164_; 
v___x_1162_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1120_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 1, v___x_1162_);
lean_ctor_set(v___x_1154_, 0, v_binderType_1147_);
v___x_1164_ = v___x_1154_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_binderType_1147_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v___x_1162_);
v___x_1164_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
lean_object* v___x_1165_; 
v___x_1165_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1161_, v___x_1164_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1193_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1168_ = v___x_1165_;
v_isShared_1169_ = v_isSharedCheck_1193_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1165_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1193_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
uint8_t v___x_1170_; 
v___x_1170_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_a_1166_);
if (v___x_1170_ == 0)
{
lean_object* v_changesBefore_1171_; lean_object* v_changesAfter_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; uint8_t v___x_1175_; lean_object* v___x_1176_; lean_object* v_changesBefore_1177_; lean_object* v_changesAfter_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1190_; 
lean_dec_ref(v___f_1150_);
lean_dec_ref(v_binderType_1116_);
lean_dec(v_binderName_1115_);
v_changesBefore_1171_ = lean_ctor_get(v_a_1166_, 0);
lean_inc(v_changesBefore_1171_);
v_changesAfter_1172_ = lean_ctor_get(v_a_1166_, 1);
lean_inc(v_changesAfter_1172_);
lean_dec(v_a_1166_);
v___x_1173_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1078_);
lean_dec(v_pos_1078_);
v___x_1174_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1120_);
lean_dec(v_pos_1120_);
v___x_1175_ = 0;
v___x_1176_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v___x_1173_, v___x_1174_, v___x_1175_);
v_changesBefore_1177_ = lean_ctor_get(v___x_1176_, 0);
v_changesAfter_1178_ = lean_ctor_get(v___x_1176_, 1);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1180_ = v___x_1176_;
v_isShared_1181_ = v_isSharedCheck_1190_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_changesAfter_1178_);
lean_inc(v_changesBefore_1177_);
lean_dec(v___x_1176_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1190_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1182_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesBefore_1171_, v_changesBefore_1177_);
v___x_1183_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesAfter_1172_, v_changesAfter_1178_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 1, v___x_1183_);
lean_ctor_set(v___x_1180_, 0, v___x_1182_);
v___x_1185_ = v___x_1180_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1182_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
lean_object* v___x_1187_; 
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 0, v___x_1185_);
v___x_1187_ = v___x_1168_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
else
{
uint8_t v___x_1191_; lean_object* v___x_1192_; 
lean_del_object(v___x_1168_);
lean_dec(v_a_1166_);
lean_dec(v_pos_1120_);
lean_dec(v_pos_1078_);
v___x_1191_ = 0;
v___x_1192_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_binderName_1115_, v_binderInfo_1118_, v_binderType_1116_, v___f_1150_, v___x_1191_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_);
return v___x_1192_;
}
}
}
else
{
lean_dec_ref(v___f_1150_);
lean_dec(v_pos_1120_);
lean_dec_ref(v_binderType_1116_);
lean_dec(v_binderName_1115_);
lean_dec(v_pos_1078_);
return v___x_1165_;
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
v___y_1122_ = v_a_1033_;
v___y_1123_ = v_a_1034_;
v___y_1124_ = v_a_1035_;
v___y_1125_ = v_a_1036_;
goto v___jp_1121_;
}
v___jp_1121_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = l_Lean_Expr_getForallBinderNames(v_expr_1119_);
v___x_1127_ = l_Lean_Expr_getForallBinderNames(v_expr_1077_);
v___x_1128_ = l_List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0(v___x_1126_, v___x_1127_);
if (lean_obj_tag(v___x_1128_) == 1)
{
lean_object* v_val_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v_val_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_val_1129_);
lean_dec_ref_known(v___x_1128_, 1);
v___x_1130_ = l_List_lengthTR___redArg(v_val_1129_);
v___x_1131_ = lean_unsigned_to_nat(0u);
v___x_1132_ = lean_nat_dec_eq(v___x_1130_, v___x_1131_);
lean_dec(v___x_1130_);
if (v___x_1132_ == 0)
{
v___y_1080_ = v_val_1129_;
v___y_1081_ = v___y_1122_;
v___y_1082_ = v___y_1123_;
v___y_1083_ = v___y_1124_;
v___y_1084_ = v___y_1125_;
goto v___jp_1079_;
}
else
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1, &l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1);
v___x_1134_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_1133_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_dec_ref_known(v___x_1134_, 1);
v___y_1080_ = v_val_1129_;
v___y_1081_ = v___y_1122_;
v___y_1082_ = v___y_1123_;
v___y_1083_ = v___y_1124_;
v___y_1084_ = v___y_1125_;
goto v___jp_1079_;
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_dec(v_val_1129_);
lean_dec_ref(v_after_1032_);
lean_dec_ref(v_before_1031_);
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1134_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1134_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
else
{
uint8_t v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_dec(v___x_1128_);
v___x_1143_ = 0;
v___x_1144_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1031_, v_after_1032_, v___x_1143_);
v___x_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
return v___x_1145_;
}
}
}
else
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
lean_dec_ref(v_after_1032_);
lean_dec_ref(v_before_1031_);
v___x_1204_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
return v___x_1205_;
}
v___jp_1038_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = lean_unsigned_to_nat(0u);
v___x_1046_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v___y_1042_, v_before_1031_, v___x_1045_, v_a_1044_);
lean_dec(v___y_1042_);
return v___x_1046_;
}
v___jp_1047_:
{
if (v___y_1055_ == 0)
{
lean_object* v___x_1056_; 
lean_dec_ref(v___y_1048_);
v___x_1056_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1052_, v___y_1054_, v___y_1050_);
lean_dec_ref(v___y_1052_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v___x_1057_; 
lean_dec_ref_known(v___x_1056_, 1);
v___x_1057_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___y_1039_ = v___y_1049_;
v___y_1040_ = v___y_1050_;
v___y_1041_ = v___y_1051_;
v___y_1042_ = v___y_1053_;
v___y_1043_ = v___y_1054_;
v_a_1044_ = v___x_1057_;
goto v___jp_1038_;
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_dec(v___y_1053_);
lean_dec_ref(v_before_1031_);
v_a_1058_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1056_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1056_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
else
{
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec_ref(v_before_1031_);
return v___y_1048_;
}
}
v___jp_1066_:
{
uint8_t v___x_1075_; 
v___x_1075_ = l_Lean_Exception_isInterrupt(v_a_1074_);
if (v___x_1075_ == 0)
{
uint8_t v___x_1076_; 
v___x_1076_ = l_Lean_Exception_isRuntime(v_a_1074_);
v___y_1048_ = v___y_1073_;
v___y_1049_ = v___y_1067_;
v___y_1050_ = v___y_1068_;
v___y_1051_ = v___y_1070_;
v___y_1052_ = v___y_1069_;
v___y_1053_ = v___y_1071_;
v___y_1054_ = v___y_1072_;
v___y_1055_ = v___x_1076_;
goto v___jp_1047_;
}
else
{
lean_dec_ref(v_a_1074_);
v___y_1048_ = v___y_1073_;
v___y_1049_ = v___y_1067_;
v___y_1050_ = v___y_1068_;
v___y_1051_ = v___y_1070_;
v___y_1052_ = v___y_1069_;
v___y_1053_ = v___y_1071_;
v___y_1054_ = v___y_1072_;
v___y_1055_ = v___x_1075_;
goto v___jp_1047_;
}
}
v___jp_1079_:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lean_Meta_saveState___redArg(v___y_1082_, v___y_1084_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_a_1086_);
lean_dec_ref_known(v___x_1085_, 1);
v___x_1087_ = l_List_lengthTR___redArg(v___y_1080_);
v___x_1088_ = lean_box(0);
v___x_1089_ = l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(v___y_1080_, v___x_1088_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v_body_u2080_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_a_1090_);
lean_dec_ref_known(v___x_1089_, 1);
lean_inc_n(v___x_1087_, 2);
v_body_u2080_1091_ = l_Lean_Expr_getForallBodyMaxDepth(v___x_1087_, v_expr_1077_);
v___x_1092_ = lean_array_mk(v_a_1090_);
v___x_1093_ = lean_expr_instantiate_rev(v_body_u2080_1091_, v___x_1092_);
lean_dec_ref(v___x_1092_);
lean_dec_ref(v_body_u2080_1091_);
lean_inc(v_pos_1078_);
v___x_1094_ = l_Lean_SubExpr_Pos_pushNthBindingBody(v___x_1087_, v_pos_1078_);
v___x_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1095_, v_after_1032_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; 
lean_dec(v_a_1086_);
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_a_1097_);
lean_dec_ref_known(v___x_1096_, 1);
v___y_1039_ = v___y_1081_;
v___y_1040_ = v___y_1084_;
v___y_1041_ = v___y_1083_;
v___y_1042_ = v___x_1087_;
v___y_1043_ = v___y_1082_;
v_a_1044_ = v_a_1097_;
goto v___jp_1038_;
}
else
{
lean_object* v_a_1098_; 
v_a_1098_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_a_1098_);
v___y_1067_ = v___y_1081_;
v___y_1068_ = v___y_1084_;
v___y_1069_ = v_a_1086_;
v___y_1070_ = v___y_1083_;
v___y_1071_ = v___x_1087_;
v___y_1072_ = v___y_1082_;
v___y_1073_ = v___x_1096_;
v_a_1074_ = v_a_1098_;
goto v___jp_1066_;
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec_ref(v_after_1032_);
v_a_1099_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1089_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1089_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
lean_inc(v_a_1099_);
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
v___y_1067_ = v___y_1081_;
v___y_1068_ = v___y_1084_;
v___y_1069_ = v_a_1086_;
v___y_1070_ = v___y_1083_;
v___y_1071_ = v___x_1087_;
v___y_1072_ = v___y_1082_;
v___y_1073_ = v___x_1104_;
v_a_1074_ = v_a_1099_;
goto v___jp_1066_;
}
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_dec(v___y_1080_);
lean_dec_ref(v_after_1032_);
lean_dec_ref(v_before_1031_);
v_a_1107_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1085_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1085_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(lean_object* v_before_1206_, lean_object* v_after_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v_expr_1229_; lean_object* v_pos_1230_; lean_object* v_expr_1231_; lean_object* v_pos_1232_; lean_object* v_e_u2081_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; uint8_t v___x_1241_; 
v_expr_1229_ = lean_ctor_get(v_before_1206_, 0);
v_pos_1230_ = lean_ctor_get(v_before_1206_, 1);
v_expr_1231_ = lean_ctor_get(v_after_1207_, 0);
v_pos_1232_ = lean_ctor_get(v_after_1207_, 1);
v___x_1241_ = lean_expr_eqv(v_expr_1229_, v_expr_1231_);
if (v___x_1241_ == 0)
{
switch(lean_obj_tag(v_expr_1229_))
{
case 10:
{
lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1250_; 
lean_inc_ref(v_expr_1229_);
lean_inc(v_pos_1230_);
v_isSharedCheck_1250_ = !lean_is_exclusive(v_before_1206_);
if (v_isSharedCheck_1250_ == 0)
{
lean_object* v_unused_1251_; lean_object* v_unused_1252_; 
v_unused_1251_ = lean_ctor_get(v_before_1206_, 1);
lean_dec(v_unused_1251_);
v_unused_1252_ = lean_ctor_get(v_before_1206_, 0);
lean_dec(v_unused_1252_);
v___x_1243_ = v_before_1206_;
v_isShared_1244_ = v_isSharedCheck_1250_;
goto v_resetjp_1242_;
}
else
{
lean_dec(v_before_1206_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1250_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v_expr_1245_; lean_object* v___x_1247_; 
v_expr_1245_ = lean_ctor_get(v_expr_1229_, 1);
lean_inc_ref(v_expr_1245_);
lean_dec_ref_known(v_expr_1229_, 2);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v_expr_1245_);
v___x_1247_ = v___x_1243_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_expr_1245_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v_pos_1230_);
v___x_1247_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
v_before_1206_ = v___x_1247_;
goto _start;
}
}
}
case 5:
{
switch(lean_obj_tag(v_expr_1231_))
{
case 10:
{
lean_object* v_expr_1253_; 
lean_inc_ref(v_expr_1231_);
lean_inc(v_pos_1232_);
lean_dec_ref(v_after_1207_);
v_expr_1253_ = lean_ctor_get(v_expr_1231_, 1);
lean_inc_ref(v_expr_1253_);
lean_dec_ref_known(v_expr_1231_, 2);
v_e_u2081_1234_ = v_expr_1253_;
v___y_1235_ = v_a_1208_;
v___y_1236_ = v_a_1209_;
v___y_1237_ = v_a_1210_;
v___y_1238_ = v_a_1211_;
goto v___jp_1233_;
}
case 5:
{
lean_object* v_dummy_1254_; lean_object* v_nargs_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v_fst_1260_; lean_object* v_snd_1261_; lean_object* v_nargs_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v_fst_1266_; lean_object* v_snd_1267_; uint8_t v___x_1268_; 
v_dummy_1254_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0, &l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0);
v_nargs_1255_ = l_Lean_Expr_getAppNumArgs(v_expr_1231_);
lean_inc(v_nargs_1255_);
v___x_1256_ = lean_mk_array(v_nargs_1255_, v_dummy_1254_);
v___x_1257_ = lean_unsigned_to_nat(1u);
v___x_1258_ = lean_nat_sub(v_nargs_1255_, v___x_1257_);
lean_dec(v_nargs_1255_);
lean_inc_ref(v_expr_1231_);
v___x_1259_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(v_expr_1231_, v___x_1256_, v___x_1258_);
v_fst_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_fst_1260_);
v_snd_1261_ = lean_ctor_get(v___x_1259_, 1);
lean_inc(v_snd_1261_);
lean_dec_ref(v___x_1259_);
v_nargs_1262_ = l_Lean_Expr_getAppNumArgs(v_expr_1229_);
lean_inc(v_nargs_1262_);
v___x_1263_ = lean_mk_array(v_nargs_1262_, v_dummy_1254_);
v___x_1264_ = lean_nat_sub(v_nargs_1262_, v___x_1257_);
lean_dec(v_nargs_1262_);
lean_inc_ref(v_expr_1229_);
v___x_1265_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(v_expr_1229_, v___x_1263_, v___x_1264_);
v_fst_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_fst_1266_);
v_snd_1267_ = lean_ctor_get(v___x_1265_, 1);
lean_inc(v_snd_1267_);
lean_dec_ref(v___x_1265_);
v___x_1268_ = lean_expr_eqv(v_fst_1260_, v_fst_1266_);
lean_dec(v_fst_1266_);
lean_dec(v_fst_1260_);
if (v___x_1268_ == 0)
{
lean_dec(v_snd_1267_);
lean_dec(v_snd_1261_);
goto v___jp_1221_;
}
else
{
if (v___x_1241_ == 0)
{
lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
v___x_1269_ = lean_array_get_size(v_snd_1261_);
v___x_1270_ = lean_array_get_size(v_snd_1267_);
v___x_1271_ = lean_nat_dec_eq(v___x_1269_, v___x_1270_);
if (v___x_1271_ == 0)
{
lean_dec(v_snd_1267_);
lean_dec(v_snd_1261_);
goto v___jp_1221_;
}
else
{
if (v___x_1241_ == 0)
{
lean_object* v_args_1272_; size_t v_sz_1273_; size_t v___x_1274_; lean_object* v___x_1275_; 
v_args_1272_ = l_Array_zip___redArg(v_snd_1261_, v_snd_1267_);
lean_dec(v_snd_1267_);
v_sz_1273_ = lean_array_size(v_args_1272_);
v___x_1274_ = ((size_t)0ULL);
v___x_1275_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_1261_, v_before_1206_, v_after_1207_, v_sz_1273_, v___x_1274_, v_args_1272_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
lean_dec_ref(v_after_1207_);
lean_dec_ref(v_before_1206_);
lean_dec(v_snd_1261_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1301_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1278_ = v___x_1275_;
v_isShared_1279_ = v_isSharedCheck_1301_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1301_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1280_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___x_1281_ = lean_unsigned_to_nat(0u);
v___x_1282_ = lean_array_get_size(v_a_1276_);
v___x_1283_ = lean_nat_dec_lt(v___x_1281_, v___x_1282_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1285_; 
lean_dec(v_a_1276_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1280_);
v___x_1285_ = v___x_1278_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
else
{
uint8_t v___x_1287_; 
v___x_1287_ = lean_nat_dec_le(v___x_1282_, v___x_1282_);
if (v___x_1287_ == 0)
{
if (v___x_1283_ == 0)
{
lean_object* v___x_1289_; 
lean_dec(v_a_1276_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1280_);
v___x_1289_ = v___x_1278_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1280_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
else
{
size_t v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1294_; 
v___x_1291_ = lean_usize_of_nat(v___x_1282_);
v___x_1292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_a_1276_, v___x_1274_, v___x_1291_, v___x_1280_);
lean_dec(v_a_1276_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1292_);
v___x_1294_ = v___x_1278_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1292_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
else
{
size_t v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1299_; 
v___x_1296_ = lean_usize_of_nat(v___x_1282_);
v___x_1297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_a_1276_, v___x_1274_, v___x_1296_, v___x_1280_);
lean_dec(v_a_1276_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1297_);
v___x_1299_ = v___x_1278_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1297_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
}
else
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
v_a_1302_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1275_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1275_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
else
{
lean_dec(v_snd_1267_);
lean_dec(v_snd_1261_);
goto v___jp_1221_;
}
}
}
else
{
lean_dec(v_snd_1267_);
lean_dec(v_snd_1261_);
goto v___jp_1221_;
}
}
}
default: 
{
goto v___jp_1225_;
}
}
}
case 7:
{
if (lean_obj_tag(v_expr_1231_) == 10)
{
lean_object* v_expr_1310_; 
lean_inc_ref(v_expr_1231_);
lean_inc(v_pos_1232_);
lean_dec_ref(v_after_1207_);
v_expr_1310_ = lean_ctor_get(v_expr_1231_, 1);
lean_inc_ref(v_expr_1310_);
lean_dec_ref_known(v_expr_1231_, 2);
v_e_u2081_1234_ = v_expr_1310_;
v___y_1235_ = v_a_1208_;
v___y_1236_ = v_a_1209_;
v___y_1237_ = v_a_1210_;
v___y_1238_ = v_a_1211_;
goto v___jp_1233_;
}
else
{
lean_object* v___x_1311_; 
v___x_1311_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(v_before_1206_, v_after_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
return v___x_1311_;
}
}
case 6:
{
switch(lean_obj_tag(v_expr_1231_))
{
case 10:
{
lean_object* v_expr_1312_; 
lean_inc_ref(v_expr_1231_);
lean_inc(v_pos_1232_);
lean_dec_ref(v_after_1207_);
v_expr_1312_ = lean_ctor_get(v_expr_1231_, 1);
lean_inc_ref(v_expr_1312_);
lean_dec_ref_known(v_expr_1231_, 2);
v_e_u2081_1234_ = v_expr_1312_;
v___y_1235_ = v_a_1208_;
v___y_1236_ = v_a_1209_;
v___y_1237_ = v_a_1210_;
v___y_1238_ = v_a_1211_;
goto v___jp_1233_;
}
case 6:
{
lean_object* v_binderName_1313_; lean_object* v_binderType_1314_; lean_object* v_body_1315_; uint8_t v_binderInfo_1316_; lean_object* v_binderName_1317_; lean_object* v_binderType_1318_; lean_object* v_body_1319_; uint8_t v_binderInfo_1320_; uint8_t v___x_1321_; 
v_binderName_1313_ = lean_ctor_get(v_expr_1229_, 0);
v_binderType_1314_ = lean_ctor_get(v_expr_1229_, 1);
v_body_1315_ = lean_ctor_get(v_expr_1229_, 2);
v_binderInfo_1316_ = lean_ctor_get_uint8(v_expr_1229_, sizeof(void*)*3 + 8);
v_binderName_1317_ = lean_ctor_get(v_expr_1231_, 0);
v_binderType_1318_ = lean_ctor_get(v_expr_1231_, 1);
v_body_1319_ = lean_ctor_get(v_expr_1231_, 2);
v_binderInfo_1320_ = lean_ctor_get_uint8(v_expr_1231_, sizeof(void*)*3 + 8);
v___x_1321_ = lean_name_eq(v_binderName_1313_, v_binderName_1317_);
if (v___x_1321_ == 0)
{
goto v___jp_1217_;
}
else
{
if (v___x_1241_ == 0)
{
uint8_t v___x_1322_; 
v___x_1322_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1316_, v_binderInfo_1320_);
if (v___x_1322_ == 0)
{
goto v___jp_1217_;
}
else
{
if (v___x_1241_ == 0)
{
lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1372_; 
lean_inc_ref(v_body_1319_);
lean_inc_ref(v_binderType_1318_);
lean_inc_ref(v_body_1315_);
lean_inc_ref(v_binderType_1314_);
lean_inc(v_pos_1232_);
lean_inc(v_pos_1230_);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_before_1206_);
if (v_isSharedCheck_1372_ == 0)
{
lean_object* v_unused_1373_; lean_object* v_unused_1374_; 
v_unused_1373_ = lean_ctor_get(v_before_1206_, 1);
lean_dec(v_unused_1373_);
v_unused_1374_ = lean_ctor_get(v_before_1206_, 0);
lean_dec(v_unused_1374_);
v___x_1324_ = v_before_1206_;
v_isShared_1325_ = v_isSharedCheck_1372_;
goto v_resetjp_1323_;
}
else
{
lean_dec(v_before_1206_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1372_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1369_; 
v_isSharedCheck_1369_ = !lean_is_exclusive(v_after_1207_);
if (v_isSharedCheck_1369_ == 0)
{
lean_object* v_unused_1370_; lean_object* v_unused_1371_; 
v_unused_1370_ = lean_ctor_get(v_after_1207_, 1);
lean_dec(v_unused_1370_);
v_unused_1371_ = lean_ctor_get(v_after_1207_, 0);
lean_dec(v_unused_1371_);
v___x_1327_ = v_after_1207_;
v_isShared_1328_ = v_isSharedCheck_1369_;
goto v_resetjp_1326_;
}
else
{
lean_dec(v_after_1207_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1369_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___x_1329_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1230_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 1, v___x_1329_);
lean_ctor_set(v___x_1327_, 0, v_binderType_1314_);
v___x_1331_ = v___x_1327_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_binderType_1314_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v___x_1329_);
v___x_1331_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
lean_object* v___x_1332_; lean_object* v___x_1334_; 
v___x_1332_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1232_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 1, v___x_1332_);
lean_ctor_set(v___x_1324_, 0, v_binderType_1318_);
v___x_1334_ = v___x_1324_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_binderType_1318_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v___x_1332_);
v___x_1334_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
lean_object* v___x_1335_; 
v___x_1335_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1331_, v___x_1334_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1366_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1338_ = v___x_1335_;
v_isShared_1339_ = v_isSharedCheck_1366_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1335_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1366_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
uint8_t v___x_1340_; 
v___x_1340_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_a_1336_);
if (v___x_1340_ == 0)
{
lean_object* v_changesBefore_1341_; lean_object* v_changesAfter_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; lean_object* v___x_1346_; lean_object* v_changesBefore_1347_; lean_object* v_changesAfter_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1360_; 
lean_dec_ref(v_body_1319_);
lean_dec_ref(v_body_1315_);
v_changesBefore_1341_ = lean_ctor_get(v_a_1336_, 0);
lean_inc(v_changesBefore_1341_);
v_changesAfter_1342_ = lean_ctor_get(v_a_1336_, 1);
lean_inc(v_changesAfter_1342_);
lean_dec(v_a_1336_);
v___x_1343_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1230_);
lean_dec(v_pos_1230_);
v___x_1344_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1232_);
lean_dec(v_pos_1232_);
v___x_1345_ = 0;
v___x_1346_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(v___x_1343_, v___x_1344_, v___x_1345_);
v_changesBefore_1347_ = lean_ctor_get(v___x_1346_, 0);
v_changesAfter_1348_ = lean_ctor_get(v___x_1346_, 1);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1350_ = v___x_1346_;
v_isShared_1351_ = v_isSharedCheck_1360_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_changesAfter_1348_);
lean_inc(v_changesBefore_1347_);
lean_dec(v___x_1346_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1360_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1355_; 
v___x_1352_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesBefore_1341_, v_changesBefore_1347_);
v___x_1353_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesAfter_1342_, v_changesAfter_1348_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 1, v___x_1353_);
lean_ctor_set(v___x_1350_, 0, v___x_1352_);
v___x_1355_ = v___x_1350_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v___x_1353_);
v___x_1355_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v___x_1357_; 
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1355_);
v___x_1357_ = v___x_1338_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
else
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
lean_del_object(v___x_1338_);
lean_dec(v_a_1336_);
v___x_1361_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1230_);
lean_dec(v_pos_1230_);
v___x_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1362_, 0, v_body_1315_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
v___x_1363_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1232_);
lean_dec(v_pos_1232_);
v___x_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1364_, 0, v_body_1319_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
v_before_1206_ = v___x_1362_;
v_after_1207_ = v___x_1364_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_body_1319_);
lean_dec_ref(v_body_1315_);
lean_dec(v_pos_1232_);
lean_dec(v_pos_1230_);
return v___x_1335_;
}
}
}
}
}
}
else
{
goto v___jp_1217_;
}
}
}
else
{
goto v___jp_1217_;
}
}
}
default: 
{
goto v___jp_1225_;
}
}
}
case 11:
{
switch(lean_obj_tag(v_expr_1231_))
{
case 10:
{
lean_object* v_expr_1375_; 
lean_inc_ref(v_expr_1231_);
lean_inc(v_pos_1232_);
lean_dec_ref(v_after_1207_);
v_expr_1375_ = lean_ctor_get(v_expr_1231_, 1);
lean_inc_ref(v_expr_1375_);
lean_dec_ref_known(v_expr_1231_, 2);
v_e_u2081_1234_ = v_expr_1375_;
v___y_1235_ = v_a_1208_;
v___y_1236_ = v_a_1209_;
v___y_1237_ = v_a_1210_;
v___y_1238_ = v_a_1211_;
goto v___jp_1233_;
}
case 11:
{
lean_object* v_typeName_1376_; lean_object* v_idx_1377_; lean_object* v_struct_1378_; lean_object* v_typeName_1379_; lean_object* v_idx_1380_; lean_object* v_struct_1381_; uint8_t v___x_1382_; 
v_typeName_1376_ = lean_ctor_get(v_expr_1229_, 0);
v_idx_1377_ = lean_ctor_get(v_expr_1229_, 1);
v_struct_1378_ = lean_ctor_get(v_expr_1229_, 2);
v_typeName_1379_ = lean_ctor_get(v_expr_1231_, 0);
v_idx_1380_ = lean_ctor_get(v_expr_1231_, 1);
v_struct_1381_ = lean_ctor_get(v_expr_1231_, 2);
v___x_1382_ = lean_name_eq(v_typeName_1376_, v_typeName_1379_);
if (v___x_1382_ == 0)
{
goto v___jp_1213_;
}
else
{
if (v___x_1241_ == 0)
{
uint8_t v___x_1383_; 
v___x_1383_ = lean_nat_dec_eq(v_idx_1377_, v_idx_1380_);
if (v___x_1383_ == 0)
{
goto v___jp_1213_;
}
else
{
if (v___x_1241_ == 0)
{
lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1402_; 
lean_inc_ref(v_struct_1381_);
lean_inc_ref(v_struct_1378_);
lean_inc(v_pos_1232_);
lean_inc(v_pos_1230_);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_before_1206_);
if (v_isSharedCheck_1402_ == 0)
{
lean_object* v_unused_1403_; lean_object* v_unused_1404_; 
v_unused_1403_ = lean_ctor_get(v_before_1206_, 1);
lean_dec(v_unused_1403_);
v_unused_1404_ = lean_ctor_get(v_before_1206_, 0);
lean_dec(v_unused_1404_);
v___x_1385_ = v_before_1206_;
v_isShared_1386_ = v_isSharedCheck_1402_;
goto v_resetjp_1384_;
}
else
{
lean_dec(v_before_1206_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1402_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1399_; 
v_isSharedCheck_1399_ = !lean_is_exclusive(v_after_1207_);
if (v_isSharedCheck_1399_ == 0)
{
lean_object* v_unused_1400_; lean_object* v_unused_1401_; 
v_unused_1400_ = lean_ctor_get(v_after_1207_, 1);
lean_dec(v_unused_1400_);
v_unused_1401_ = lean_ctor_get(v_after_1207_, 0);
lean_dec(v_unused_1401_);
v___x_1388_ = v_after_1207_;
v_isShared_1389_ = v_isSharedCheck_1399_;
goto v_resetjp_1387_;
}
else
{
lean_dec(v_after_1207_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1399_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1390_; lean_object* v___x_1392_; 
v___x_1390_ = l_Lean_SubExpr_Pos_pushProj(v_pos_1230_);
lean_dec(v_pos_1230_);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 1, v___x_1390_);
lean_ctor_set(v___x_1388_, 0, v_struct_1378_);
v___x_1392_ = v___x_1388_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_struct_1378_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1393_ = l_Lean_SubExpr_Pos_pushProj(v_pos_1232_);
lean_dec(v_pos_1232_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 1, v___x_1393_);
lean_ctor_set(v___x_1385_, 0, v_struct_1381_);
v___x_1395_ = v___x_1385_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_struct_1381_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
v_before_1206_ = v___x_1392_;
v_after_1207_ = v___x_1395_;
goto _start;
}
}
}
}
}
else
{
goto v___jp_1213_;
}
}
}
else
{
goto v___jp_1213_;
}
}
}
default: 
{
goto v___jp_1225_;
}
}
}
default: 
{
if (lean_obj_tag(v_expr_1231_) == 10)
{
lean_object* v_expr_1405_; 
lean_inc_ref(v_expr_1231_);
lean_inc(v_pos_1232_);
lean_dec_ref(v_after_1207_);
v_expr_1405_ = lean_ctor_get(v_expr_1231_, 1);
lean_inc_ref(v_expr_1405_);
lean_dec_ref_known(v_expr_1231_, 2);
v_e_u2081_1234_ = v_expr_1405_;
v___y_1235_ = v_a_1208_;
v___y_1236_ = v_a_1209_;
v___y_1237_ = v_a_1210_;
v___y_1238_ = v_a_1211_;
goto v___jp_1233_;
}
else
{
goto v___jp_1225_;
}
}
}
}
else
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
lean_dec_ref(v_after_1207_);
lean_dec_ref(v_before_1206_);
v___x_1406_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0));
v___x_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
return v___x_1407_;
}
v___jp_1213_:
{
uint8_t v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1214_ = 0;
v___x_1215_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1206_, v_after_1207_, v___x_1214_);
v___x_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
return v___x_1216_;
}
v___jp_1217_:
{
uint8_t v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1218_ = 0;
v___x_1219_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1206_, v_after_1207_, v___x_1218_);
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
return v___x_1220_;
}
v___jp_1221_:
{
uint8_t v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1222_ = 0;
v___x_1223_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1206_, v_after_1207_, v___x_1222_);
v___x_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
return v___x_1224_;
}
v___jp_1225_:
{
uint8_t v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1226_ = 0;
v___x_1227_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(v_before_1206_, v_after_1207_, v___x_1226_);
v___x_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
return v___x_1228_;
}
v___jp_1233_:
{
lean_object* v___x_1239_; 
v___x_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1239_, 0, v_e_u2081_1234_);
lean_ctor_set(v___x_1239_, 1, v_pos_1232_);
v_after_1207_ = v___x_1239_;
v_a_1208_ = v___y_1235_;
v_a_1209_ = v___y_1236_;
v_a_1210_ = v___y_1237_;
v_a_1211_ = v___y_1238_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0(lean_object* v_body_1408_, lean_object* v_pos_1409_, lean_object* v_body_1410_, lean_object* v_pos_1411_, lean_object* v_x_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1418_ = lean_expr_instantiate1(v_body_1408_, v_x_1412_);
v___x_1419_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1409_);
v___x_1420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1418_);
lean_ctor_set(v___x_1420_, 1, v___x_1419_);
v___x_1421_ = lean_expr_instantiate1(v_body_1410_, v_x_1412_);
v___x_1422_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1411_);
v___x_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1421_);
lean_ctor_set(v___x_1423_, 1, v___x_1422_);
v___x_1424_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v___x_1420_, v___x_1423_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg___boxed(lean_object* v_snd_1425_, lean_object* v_before_1426_, lean_object* v_after_1427_, lean_object* v_sz_1428_, lean_object* v_i_1429_, lean_object* v_bs_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
size_t v_sz_boxed_1436_; size_t v_i_boxed_1437_; lean_object* v_res_1438_; 
v_sz_boxed_1436_ = lean_unbox_usize(v_sz_1428_);
lean_dec(v_sz_1428_);
v_i_boxed_1437_ = lean_unbox_usize(v_i_1429_);
lean_dec(v_i_1429_);
v_res_1438_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_1425_, v_before_1426_, v_after_1427_, v_sz_boxed_1436_, v_i_boxed_1437_, v_bs_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec_ref(v_after_1427_);
lean_dec_ref(v_before_1426_);
lean_dec_ref(v_snd_1425_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___boxed(lean_object* v_before_1439_, lean_object* v_after_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(v_before_1439_, v_after_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_);
lean_dec(v_a_1444_);
lean_dec_ref(v_a_1443_);
lean_dec(v_a_1442_);
lean_dec_ref(v_a_1441_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___boxed(lean_object* v_before_1447_, lean_object* v_after_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v_before_1447_, v_after_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_);
lean_dec(v_a_1452_);
lean_dec_ref(v_a_1451_);
lean_dec(v_a_1450_);
lean_dec_ref(v_a_1449_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1(lean_object* v_upperBound_1455_, lean_object* v_before_1456_, lean_object* v_inst_1457_, lean_object* v_R_1458_, lean_object* v_a_1459_, lean_object* v_b_1460_, lean_object* v_c_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v_upperBound_1455_, v_before_1456_, v_a_1459_, v_b_1460_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___boxed(lean_object* v_upperBound_1468_, lean_object* v_before_1469_, lean_object* v_inst_1470_, lean_object* v_R_1471_, lean_object* v_a_1472_, lean_object* v_b_1473_, lean_object* v_c_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1(v_upperBound_1468_, v_before_1469_, v_inst_1470_, v_R_1471_, v_a_1472_, v_b_1473_, v_c_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v_upperBound_1468_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3(lean_object* v_00_u03b1_1481_, lean_object* v_msg_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v_msg_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___boxed(lean_object* v_00_u03b1_1489_, lean_object* v_msg_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3(v_00_u03b1_1489_, v_msg_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4(uint8_t v_b_u2082_1497_, lean_object* v_k_1498_, lean_object* v_t_1499_, lean_object* v_hl_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_1497_, v_k_1498_, v_t_1499_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___boxed(lean_object* v_b_u2082_1502_, lean_object* v_k_1503_, lean_object* v_t_1504_, lean_object* v_hl_1505_){
_start:
{
uint8_t v_b_u2082_boxed_1506_; lean_object* v_res_1507_; 
v_b_u2082_boxed_1506_ = lean_unbox(v_b_u2082_1502_);
v_res_1507_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4(v_b_u2082_boxed_1506_, v_k_1503_, v_t_1504_, v_hl_1505_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5(lean_object* v_init_1508_, lean_object* v_t_1509_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_init_1508_, v_t_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9(lean_object* v_snd_1511_, lean_object* v_before_1512_, lean_object* v_after_1513_, lean_object* v_as_1514_, size_t v_sz_1515_, size_t v_i_1516_, lean_object* v_bs_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_1511_, v_before_1512_, v_after_1513_, v_sz_1515_, v_i_1516_, v_bs_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___boxed(lean_object* v_snd_1524_, lean_object* v_before_1525_, lean_object* v_after_1526_, lean_object* v_as_1527_, lean_object* v_sz_1528_, lean_object* v_i_1529_, lean_object* v_bs_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
size_t v_sz_boxed_1536_; size_t v_i_boxed_1537_; lean_object* v_res_1538_; 
v_sz_boxed_1536_ = lean_unbox_usize(v_sz_1528_);
lean_dec(v_sz_1528_);
v_i_boxed_1537_ = lean_unbox_usize(v_i_1529_);
lean_dec(v_i_1529_);
v_res_1538_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9(v_snd_1524_, v_before_1525_, v_after_1526_, v_as_1527_, v_sz_boxed_1536_, v_i_boxed_1537_, v_bs_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec_ref(v_as_1527_);
lean_dec_ref(v_after_1526_);
lean_dec_ref(v_before_1525_);
lean_dec_ref(v_snd_1524_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(lean_object* v_e_u2080_1539_, lean_object* v_e_u2081_1540_, uint8_t v_useAfter_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_){
_start:
{
lean_object* v___x_1547_; lean_object* v_s_u2080_1548_; lean_object* v_s_u2081_1549_; 
v___x_1547_ = l_Lean_SubExpr_Pos_root;
v_s_u2080_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_u2080_1548_, 0, v_e_u2080_1539_);
lean_ctor_set(v_s_u2080_1548_, 1, v___x_1547_);
v_s_u2081_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_u2081_1549_, 0, v_e_u2081_1540_);
lean_ctor_set(v_s_u2081_1549_, 1, v___x_1547_);
if (v_useAfter_1541_ == 0)
{
lean_object* v___x_1550_; 
v___x_1550_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v_s_u2081_1549_, v_s_u2080_1548_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_);
return v___x_1550_;
}
else
{
lean_object* v___x_1551_; 
v___x_1551_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(v_s_u2080_1548_, v_s_u2081_1549_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_);
return v___x_1551_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff___boxed(lean_object* v_e_u2080_1552_, lean_object* v_e_u2081_1553_, lean_object* v_useAfter_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_){
_start:
{
uint8_t v_useAfter_boxed_1560_; lean_object* v_res_1561_; 
v_useAfter_boxed_1560_ = lean_unbox(v_useAfter_1554_);
v_res_1561_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(v_e_u2080_1552_, v_e_u2081_1553_, v_useAfter_boxed_1560_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_);
lean_dec(v_a_1558_);
lean_dec_ref(v_a_1557_);
lean_dec(v_a_1556_);
lean_dec_ref(v_a_1555_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0(uint8_t v_useAfter_1562_, lean_object* v_info_1563_, uint8_t v_d_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
uint8_t v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1570_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag(v_useAfter_1562_, v_d_1564_);
v___x_1571_ = l_Lean_Widget_SubexprInfo_withDiffTag(v___x_1570_, v_info_1563_);
v___x_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0___boxed(lean_object* v_useAfter_1573_, lean_object* v_info_1574_, lean_object* v_d_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
uint8_t v_useAfter_boxed_1581_; uint8_t v_d_boxed_1582_; lean_object* v_res_1583_; 
v_useAfter_boxed_1581_ = lean_unbox(v_useAfter_1573_);
v_d_boxed_1582_ = lean_unbox(v_d_1575_);
v_res_1583_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0(v_useAfter_boxed_1581_, v_info_1574_, v_d_boxed_1582_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(lean_object* v_f_1584_, lean_object* v_x_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
switch(lean_obj_tag(v_x_1585_))
{
case 0:
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1599_; 
lean_dec_ref(v_f_1584_);
v_a_1591_ = lean_ctor_get(v_x_1585_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v_x_1585_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1593_ = v_x_1585_;
v_isShared_1594_ = v_isSharedCheck_1599_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v_x_1585_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1599_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_object* v___x_1597_; 
v___x_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1596_);
return v___x_1597_;
}
}
}
case 1:
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1626_; 
v_a_1600_ = lean_ctor_get(v_x_1585_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v_x_1585_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1602_ = v_x_1585_;
v_isShared_1603_ = v_isSharedCheck_1626_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v_x_1585_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1626_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
size_t v_sz_1604_; size_t v___x_1605_; lean_object* v___x_1606_; 
v_sz_1604_ = lean_array_size(v_a_1600_);
v___x_1605_ = ((size_t)0ULL);
v___x_1606_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_1584_, v_sz_1604_, v___x_1605_, v_a_1600_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1617_; 
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1609_ = v___x_1606_;
v_isShared_1610_ = v_isSharedCheck_1617_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1606_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1617_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 0, v_a_1607_);
v___x_1612_ = v___x_1602_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
lean_object* v___x_1614_; 
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v___x_1612_);
v___x_1614_ = v___x_1609_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1612_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
else
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
lean_del_object(v___x_1602_);
v_a_1618_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1606_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1606_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
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
}
default: 
{
lean_object* v_a_1627_; lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1654_; 
v_a_1627_ = lean_ctor_get(v_x_1585_, 0);
v_a_1628_ = lean_ctor_get(v_x_1585_, 1);
v_isSharedCheck_1654_ = !lean_is_exclusive(v_x_1585_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1630_ = v_x_1585_;
v_isShared_1631_ = v_isSharedCheck_1654_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_inc(v_a_1627_);
lean_dec(v_x_1585_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1654_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1632_; 
lean_inc_ref(v_f_1584_);
lean_inc(v___y_1589_);
lean_inc_ref(v___y_1588_);
lean_inc(v___y_1587_);
lean_inc_ref(v___y_1586_);
v___x_1632_ = lean_apply_6(v_f_1584_, v_a_1627_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, lean_box(0));
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; lean_object* v___x_1634_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_a_1633_);
lean_dec_ref_known(v___x_1632_, 1);
v___x_1634_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1584_, v_a_1628_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1645_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1645_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1645_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 1, v_a_1635_);
lean_ctor_set(v___x_1630_, 0, v_a_1633_);
v___x_1640_ = v___x_1630_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1633_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_a_1635_);
v___x_1640_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
lean_object* v___x_1642_; 
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1640_);
v___x_1642_ = v___x_1637_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1640_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
else
{
lean_dec(v_a_1633_);
lean_del_object(v___x_1630_);
return v___x_1634_;
}
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
lean_del_object(v___x_1630_);
lean_dec_ref(v_a_1628_);
lean_dec_ref(v_f_1584_);
v_a_1646_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1632_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1632_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(lean_object* v_f_1655_, size_t v_sz_1656_, size_t v_i_1657_, lean_object* v_bs_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
uint8_t v___x_1664_; 
v___x_1664_ = lean_usize_dec_lt(v_i_1657_, v_sz_1656_);
if (v___x_1664_ == 0)
{
lean_object* v___x_1665_; 
lean_dec_ref(v_f_1655_);
v___x_1665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1665_, 0, v_bs_1658_);
return v___x_1665_;
}
else
{
lean_object* v_v_1666_; lean_object* v___x_1667_; 
v_v_1666_ = lean_array_uget_borrowed(v_bs_1658_, v_i_1657_);
lean_inc(v_v_1666_);
lean_inc_ref(v_f_1655_);
v___x_1667_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1655_, v_v_1666_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1669_; lean_object* v_bs_x27_1670_; size_t v___x_1671_; size_t v___x_1672_; lean_object* v___x_1673_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1668_);
lean_dec_ref_known(v___x_1667_, 1);
v___x_1669_ = lean_unsigned_to_nat(0u);
v_bs_x27_1670_ = lean_array_uset(v_bs_1658_, v_i_1657_, v___x_1669_);
v___x_1671_ = ((size_t)1ULL);
v___x_1672_ = lean_usize_add(v_i_1657_, v___x_1671_);
v___x_1673_ = lean_array_uset(v_bs_x27_1670_, v_i_1657_, v_a_1668_);
v_i_1657_ = v___x_1672_;
v_bs_1658_ = v___x_1673_;
goto _start;
}
else
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1682_; 
lean_dec_ref(v_bs_1658_);
lean_dec_ref(v_f_1655_);
v_a_1675_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1677_ = v___x_1667_;
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1667_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1680_; 
if (v_isShared_1678_ == 0)
{
v___x_1680_ = v___x_1677_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_a_1675_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_1683_, lean_object* v_sz_1684_, lean_object* v_i_1685_, lean_object* v_bs_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
size_t v_sz_boxed_1692_; size_t v_i_boxed_1693_; lean_object* v_res_1694_; 
v_sz_boxed_1692_ = lean_unbox_usize(v_sz_1684_);
lean_dec(v_sz_1684_);
v_i_boxed_1693_ = lean_unbox_usize(v_i_1685_);
lean_dec(v_i_1685_);
v_res_1694_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_1683_, v_sz_boxed_1692_, v_i_boxed_1693_, v_bs_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg___boxed(lean_object* v_f_1695_, lean_object* v_x_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1695_, v_x_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(lean_object* v_t_1703_, lean_object* v_k_1704_){
_start:
{
if (lean_obj_tag(v_t_1703_) == 0)
{
lean_object* v_k_1705_; lean_object* v_v_1706_; lean_object* v_l_1707_; lean_object* v_r_1708_; uint8_t v___x_1709_; 
v_k_1705_ = lean_ctor_get(v_t_1703_, 1);
v_v_1706_ = lean_ctor_get(v_t_1703_, 2);
v_l_1707_ = lean_ctor_get(v_t_1703_, 3);
v_r_1708_ = lean_ctor_get(v_t_1703_, 4);
v___x_1709_ = lean_nat_dec_lt(v_k_1704_, v_k_1705_);
if (v___x_1709_ == 0)
{
uint8_t v___x_1710_; 
v___x_1710_ = lean_nat_dec_eq(v_k_1704_, v_k_1705_);
if (v___x_1710_ == 0)
{
v_t_1703_ = v_r_1708_;
goto _start;
}
else
{
lean_object* v___x_1712_; 
lean_inc(v_v_1706_);
v___x_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1712_, 0, v_v_1706_);
return v___x_1712_;
}
}
else
{
v_t_1703_ = v_l_1707_;
goto _start;
}
}
else
{
lean_object* v___x_1714_; 
v___x_1714_ = lean_box(0);
return v___x_1714_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg___boxed(lean_object* v_t_1715_, lean_object* v_k_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_t_1715_, v_k_1716_);
lean_dec(v_k_1716_);
lean_dec(v_t_1715_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0(lean_object* v_pm_1718_, lean_object* v_merger_1719_, lean_object* v_info_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v_subexprPos_1726_; lean_object* v___x_1727_; 
v_subexprPos_1726_ = lean_ctor_get(v_info_1720_, 1);
v___x_1727_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_pm_1718_, v_subexprPos_1726_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v___x_1728_; 
lean_dec_ref(v_merger_1719_);
v___x_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1728_, 0, v_info_1720_);
return v___x_1728_;
}
else
{
lean_object* v_val_1729_; lean_object* v___x_1730_; 
v_val_1729_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_val_1729_);
lean_dec_ref_known(v___x_1727_, 1);
lean_inc(v___y_1724_);
lean_inc_ref(v___y_1723_);
lean_inc(v___y_1722_);
lean_inc_ref(v___y_1721_);
v___x_1730_ = lean_apply_7(v_merger_1719_, v_info_1720_, v_val_1729_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, lean_box(0));
return v___x_1730_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0___boxed(lean_object* v_pm_1731_, lean_object* v_merger_1732_, lean_object* v_info_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0(v_pm_1731_, v_merger_1732_, v_info_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v_pm_1731_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(lean_object* v_merger_1740_, lean_object* v_pm_1741_, lean_object* v_tt_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
if (lean_obj_tag(v_pm_1741_) == 0)
{
lean_object* v___f_1748_; lean_object* v___x_1749_; 
v___f_1748_ = lean_alloc_closure((void*)(l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1748_, 0, v_pm_1741_);
lean_closure_set(v___f_1748_, 1, v_merger_1740_);
v___x_1749_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v___f_1748_, v_tt_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
return v___x_1749_;
}
else
{
lean_object* v___x_1750_; 
lean_dec_ref(v_merger_1740_);
v___x_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1750_, 0, v_tt_1742_);
return v___x_1750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___boxed(lean_object* v_merger_1751_, lean_object* v_pm_1752_, lean_object* v_tt_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v_merger_1751_, v_pm_1752_, v_tt_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(uint8_t v_useAfter_1760_, lean_object* v_diff_1761_, lean_object* v_info_u2081_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_){
_start:
{
lean_object* v___x_1768_; lean_object* v___f_1769_; 
v___x_1768_ = lean_box(v_useAfter_1760_);
v___f_1769_ = lean_alloc_closure((void*)(l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1769_, 0, v___x_1768_);
if (v_useAfter_1760_ == 0)
{
lean_object* v_changesBefore_1770_; lean_object* v___x_1771_; 
v_changesBefore_1770_ = lean_ctor_get(v_diff_1761_, 0);
lean_inc(v_changesBefore_1770_);
lean_dec_ref(v_diff_1761_);
v___x_1771_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v___f_1769_, v_changesBefore_1770_, v_info_u2081_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_);
return v___x_1771_;
}
else
{
lean_object* v_changesAfter_1772_; lean_object* v___x_1773_; 
v_changesAfter_1772_ = lean_ctor_get(v_diff_1761_, 1);
lean_inc(v_changesAfter_1772_);
lean_dec_ref(v_diff_1761_);
v___x_1773_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v___f_1769_, v_changesAfter_1772_, v_info_u2081_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_);
return v___x_1773_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___boxed(lean_object* v_useAfter_1774_, lean_object* v_diff_1775_, lean_object* v_info_u2081_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_){
_start:
{
uint8_t v_useAfter_boxed_1782_; lean_object* v_res_1783_; 
v_useAfter_boxed_1782_ = lean_unbox(v_useAfter_1774_);
v_res_1783_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(v_useAfter_boxed_1782_, v_diff_1775_, v_info_u2081_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
lean_dec(v_a_1780_);
lean_dec_ref(v_a_1779_);
lean_dec(v_a_1778_);
lean_dec_ref(v_a_1777_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0(lean_object* v_00_u03b1_1784_, lean_object* v_merger_1785_, lean_object* v_pm_1786_, lean_object* v_tt_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v_merger_1785_, v_pm_1786_, v_tt_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___boxed(lean_object* v_00_u03b1_1794_, lean_object* v_merger_1795_, lean_object* v_pm_1796_, lean_object* v_tt_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0(v_00_u03b1_1794_, v_merger_1795_, v_pm_1796_, v_tt_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0(lean_object* v_00_u03b4_1804_, lean_object* v_t_1805_, lean_object* v_k_1806_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_t_1805_, v_k_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___boxed(lean_object* v_00_u03b4_1808_, lean_object* v_t_1809_, lean_object* v_k_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0(v_00_u03b4_1808_, v_t_1809_, v_k_1810_);
lean_dec(v_k_1810_);
lean_dec(v_t_1809_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1(lean_object* v_00_u03b1_1812_, lean_object* v_00_u03b2_1813_, lean_object* v_f_1814_, lean_object* v_x_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_1814_, v_x_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1822_, lean_object* v_00_u03b2_1823_, lean_object* v_f_1824_, lean_object* v_x_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1(v_00_u03b1_1822_, v_00_u03b2_1823_, v_f_1824_, v_x_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1832_, lean_object* v_00_u03b2_1833_, lean_object* v_f_1834_, size_t v_sz_1835_, size_t v_i_1836_, lean_object* v_bs_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_1834_, v_sz_1835_, v_i_1836_, v_bs_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1844_, lean_object* v_00_u03b2_1845_, lean_object* v_f_1846_, lean_object* v_sz_1847_, lean_object* v_i_1848_, lean_object* v_bs_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
size_t v_sz_boxed_1855_; size_t v_i_boxed_1856_; lean_object* v_res_1857_; 
v_sz_boxed_1855_ = lean_unbox_usize(v_sz_1847_);
lean_dec(v_sz_1847_);
v_i_boxed_1856_ = lean_unbox_usize(v_i_1848_);
lean_dec(v_i_1848_);
v_res_1857_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2(v_00_u03b1_1844_, v_00_u03b2_1845_, v_f_1846_, v_sz_boxed_1855_, v_i_boxed_1856_, v_bs_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(lean_object* v_e_1858_, lean_object* v___y_1859_){
_start:
{
uint8_t v___x_1861_; 
v___x_1861_ = l_Lean_Expr_hasMVar(v_e_1858_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; 
v___x_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1862_, 0, v_e_1858_);
return v___x_1862_;
}
else
{
lean_object* v___x_1863_; lean_object* v_mctx_1864_; lean_object* v___x_1865_; lean_object* v_fst_1866_; lean_object* v_snd_1867_; lean_object* v___x_1868_; lean_object* v_cache_1869_; lean_object* v_zetaDeltaFVarIds_1870_; lean_object* v_postponed_1871_; lean_object* v_diag_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1881_; 
v___x_1863_ = lean_st_ref_get(v___y_1859_);
v_mctx_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc_ref(v_mctx_1864_);
lean_dec(v___x_1863_);
v___x_1865_ = l_Lean_instantiateMVarsCore(v_mctx_1864_, v_e_1858_);
v_fst_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_fst_1866_);
v_snd_1867_ = lean_ctor_get(v___x_1865_, 1);
lean_inc(v_snd_1867_);
lean_dec_ref(v___x_1865_);
v___x_1868_ = lean_st_ref_take(v___y_1859_);
v_cache_1869_ = lean_ctor_get(v___x_1868_, 1);
v_zetaDeltaFVarIds_1870_ = lean_ctor_get(v___x_1868_, 2);
v_postponed_1871_ = lean_ctor_get(v___x_1868_, 3);
v_diag_1872_ = lean_ctor_get(v___x_1868_, 4);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1881_ == 0)
{
lean_object* v_unused_1882_; 
v_unused_1882_ = lean_ctor_get(v___x_1868_, 0);
lean_dec(v_unused_1882_);
v___x_1874_ = v___x_1868_;
v_isShared_1875_ = v_isSharedCheck_1881_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_diag_1872_);
lean_inc(v_postponed_1871_);
lean_inc(v_zetaDeltaFVarIds_1870_);
lean_inc(v_cache_1869_);
lean_dec(v___x_1868_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1881_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 0, v_snd_1867_);
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_snd_1867_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v_cache_1869_);
lean_ctor_set(v_reuseFailAlloc_1880_, 2, v_zetaDeltaFVarIds_1870_);
lean_ctor_set(v_reuseFailAlloc_1880_, 3, v_postponed_1871_);
lean_ctor_set(v_reuseFailAlloc_1880_, 4, v_diag_1872_);
v___x_1877_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = lean_st_ref_put(v___y_1859_, v___x_1877_);
v___x_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1879_, 0, v_fst_1866_);
return v___x_1879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg___boxed(lean_object* v_e_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_e_1883_, v___y_1884_);
lean_dec(v___y_1884_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0(lean_object* v_e_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_e_1887_, v___y_1889_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___boxed(lean_object* v_e_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0(v_e_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
return v_res_1900_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1(void){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1902_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__0));
v___x_1903_ = l_Lean_stringToMessageData(v___x_1902_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(uint8_t v_useAfter_1904_, lean_object* v_t_u2080_1905_, lean_object* v_h_u2081_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_){
_start:
{
lean_object* v_names_1912_; lean_object* v_fvarIds_1913_; lean_object* v_type_1914_; lean_object* v_val_x3f_1915_; lean_object* v_isInstance_x3f_1916_; lean_object* v_isType_x3f_1917_; lean_object* v_isInserted_x3f_1918_; lean_object* v_isRemoved_x3f_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1974_; 
v_names_1912_ = lean_ctor_get(v_h_u2081_1906_, 0);
v_fvarIds_1913_ = lean_ctor_get(v_h_u2081_1906_, 1);
v_type_1914_ = lean_ctor_get(v_h_u2081_1906_, 2);
v_val_x3f_1915_ = lean_ctor_get(v_h_u2081_1906_, 3);
v_isInstance_x3f_1916_ = lean_ctor_get(v_h_u2081_1906_, 4);
v_isType_x3f_1917_ = lean_ctor_get(v_h_u2081_1906_, 5);
v_isInserted_x3f_1918_ = lean_ctor_get(v_h_u2081_1906_, 6);
v_isRemoved_x3f_1919_ = lean_ctor_get(v_h_u2081_1906_, 7);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_h_u2081_1906_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1921_ = v_h_u2081_1906_;
v_isShared_1922_ = v_isSharedCheck_1974_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_isRemoved_x3f_1919_);
lean_inc(v_isInserted_x3f_1918_);
lean_inc(v_isType_x3f_1917_);
lean_inc(v_isInstance_x3f_1916_);
lean_inc(v_val_x3f_1915_);
lean_inc(v_type_1914_);
lean_inc(v_fvarIds_1913_);
lean_inc(v_names_1912_);
lean_dec(v_h_u2081_1906_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1974_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___y_1924_; lean_object* v___x_1964_; lean_object* v___x_1965_; uint8_t v___x_1966_; 
v___x_1964_ = lean_unsigned_to_nat(0u);
v___x_1965_ = lean_array_get_size(v_fvarIds_1913_);
v___x_1966_ = lean_nat_dec_lt(v___x_1964_, v___x_1965_);
if (v___x_1966_ == 0)
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
lean_del_object(v___x_1921_);
lean_dec(v_isRemoved_x3f_1919_);
lean_dec(v_isInserted_x3f_1918_);
lean_dec(v_isType_x3f_1917_);
lean_dec(v_isInstance_x3f_1916_);
lean_dec(v_val_x3f_1915_);
lean_dec_ref(v_type_1914_);
lean_dec_ref(v_fvarIds_1913_);
lean_dec_ref(v_names_1912_);
lean_dec_ref(v_t_u2080_1905_);
v___x_1967_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1);
v___x_1968_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_1967_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_);
return v___x_1968_;
}
else
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = lean_array_fget_borrowed(v_fvarIds_1913_, v___x_1964_);
lean_inc(v___x_1969_);
v___x_1970_ = l_Lean_Expr_fvar___override(v___x_1969_);
lean_inc(v_a_1910_);
lean_inc_ref(v_a_1909_);
lean_inc(v_a_1908_);
lean_inc_ref(v_a_1907_);
v___x_1971_ = lean_infer_type(v___x_1970_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; lean_object* v___x_1973_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc(v_a_1972_);
lean_dec_ref_known(v___x_1971_, 1);
v___x_1973_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_a_1972_, v_a_1908_);
v___y_1924_ = v___x_1973_;
goto v___jp_1923_;
}
else
{
v___y_1924_ = v___x_1971_;
goto v___jp_1923_;
}
}
v___jp_1923_:
{
if (lean_obj_tag(v___y_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v___x_1926_; 
v_a_1925_ = lean_ctor_get(v___y_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref_known(v___y_1924_, 1);
v___x_1926_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(v_t_u2080_1905_, v_a_1925_, v_useAfter_1904_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_a_1927_; lean_object* v___x_1928_; 
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_a_1927_);
lean_dec_ref_known(v___x_1926_, 1);
v___x_1928_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(v_useAfter_1904_, v_a_1927_, v_type_1914_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1939_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1931_ = v___x_1928_;
v_isShared_1932_ = v_isSharedCheck_1939_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1928_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1939_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 2, v_a_1929_);
v___x_1934_ = v___x_1921_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_names_1912_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_fvarIds_1913_);
lean_ctor_set(v_reuseFailAlloc_1938_, 2, v_a_1929_);
lean_ctor_set(v_reuseFailAlloc_1938_, 3, v_val_x3f_1915_);
lean_ctor_set(v_reuseFailAlloc_1938_, 4, v_isInstance_x3f_1916_);
lean_ctor_set(v_reuseFailAlloc_1938_, 5, v_isType_x3f_1917_);
lean_ctor_set(v_reuseFailAlloc_1938_, 6, v_isInserted_x3f_1918_);
lean_ctor_set(v_reuseFailAlloc_1938_, 7, v_isRemoved_x3f_1919_);
v___x_1934_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1936_; 
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v___x_1934_);
v___x_1936_ = v___x_1931_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1934_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
lean_del_object(v___x_1921_);
lean_dec(v_isRemoved_x3f_1919_);
lean_dec(v_isInserted_x3f_1918_);
lean_dec(v_isType_x3f_1917_);
lean_dec(v_isInstance_x3f_1916_);
lean_dec(v_val_x3f_1915_);
lean_dec_ref(v_fvarIds_1913_);
lean_dec_ref(v_names_1912_);
v_a_1940_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1928_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1928_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_del_object(v___x_1921_);
lean_dec(v_isRemoved_x3f_1919_);
lean_dec(v_isInserted_x3f_1918_);
lean_dec(v_isType_x3f_1917_);
lean_dec(v_isInstance_x3f_1916_);
lean_dec(v_val_x3f_1915_);
lean_dec_ref(v_type_1914_);
lean_dec_ref(v_fvarIds_1913_);
lean_dec_ref(v_names_1912_);
v_a_1948_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1926_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1926_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_del_object(v___x_1921_);
lean_dec(v_isRemoved_x3f_1919_);
lean_dec(v_isInserted_x3f_1918_);
lean_dec(v_isType_x3f_1917_);
lean_dec(v_isInstance_x3f_1916_);
lean_dec(v_val_x3f_1915_);
lean_dec_ref(v_type_1914_);
lean_dec_ref(v_fvarIds_1913_);
lean_dec_ref(v_names_1912_);
lean_dec_ref(v_t_u2080_1905_);
v_a_1956_ = lean_ctor_get(v___y_1924_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___y_1924_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___y_1924_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___y_1924_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___boxed(lean_object* v_useAfter_1975_, lean_object* v_t_u2080_1976_, lean_object* v_h_u2081_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_){
_start:
{
uint8_t v_useAfter_boxed_1983_; lean_object* v_res_1984_; 
v_useAfter_boxed_1983_ = lean_unbox(v_useAfter_1975_);
v_res_1984_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(v_useAfter_boxed_1983_, v_t_u2080_1976_, v_h_u2081_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
lean_dec(v_a_1979_);
lean_dec_ref(v_a_1978_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(lean_object* v_ctx_u2080_1988_, uint8_t v_useAfter_1989_, lean_object* v_h_u2081_1990_, lean_object* v___x_1991_, lean_object* v___x_1992_, lean_object* v_as_1993_, size_t v_sz_1994_, size_t v_i_1995_, lean_object* v_b_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
uint8_t v___x_2002_; 
v___x_2002_ = lean_usize_dec_lt(v_i_1995_, v_sz_1994_);
if (v___x_2002_ == 0)
{
lean_object* v___x_2003_; 
lean_dec_ref(v___x_1992_);
lean_dec_ref(v___x_1991_);
lean_dec_ref(v_h_u2081_1990_);
v___x_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2003_, 0, v_b_1996_);
return v___x_2003_;
}
else
{
lean_object* v_a_2004_; lean_object* v_fst_2005_; lean_object* v_snd_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2102_; 
lean_dec_ref(v_b_1996_);
v_a_2004_ = lean_array_uget(v_as_1993_, v_i_1995_);
v_fst_2005_ = lean_ctor_get(v_a_2004_, 0);
v_snd_2006_ = lean_ctor_get(v_a_2004_, 1);
v_isSharedCheck_2102_ = !lean_is_exclusive(v_a_2004_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2008_ = v_a_2004_;
v_isShared_2009_ = v_isSharedCheck_2102_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_snd_2006_);
lean_inc(v_fst_2005_);
lean_dec(v_a_2004_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2102_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2010_; uint8_t v___x_2011_; 
v___x_2010_ = lean_box(0);
v___x_2011_ = l_Lean_LocalContext_contains(v_ctx_u2080_1988_, v_snd_2006_);
lean_dec(v_snd_2006_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2012_ = lean_box(0);
v___x_2013_ = l_Lean_Name_str___override(v___x_2012_, v_fst_2005_);
v___x_2014_ = l_Lean_LocalContext_findFromUserName_x3f(v_ctx_u2080_1988_, v___x_2013_);
lean_dec(v___x_2013_);
if (lean_obj_tag(v___x_2014_) == 1)
{
lean_object* v_val_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2053_; 
lean_dec_ref(v___x_1992_);
lean_dec_ref(v___x_1991_);
v_val_2015_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2017_ = v___x_2014_;
v_isShared_2018_ = v_isSharedCheck_2053_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_val_2015_);
lean_dec(v___x_2014_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2053_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = l_Lean_LocalDecl_type(v_val_2015_);
lean_dec(v_val_2015_);
v___x_2020_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v___x_2019_, v___y_1998_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; lean_object* v___x_2022_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_a_2021_);
lean_dec_ref_known(v___x_2020_, 1);
v___x_2022_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(v_useAfter_1989_, v_a_2021_, v_h_u2081_1990_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2036_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2025_ = v___x_2022_;
v_isShared_2026_ = v_isSharedCheck_2036_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_2022_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2036_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v_a_2023_);
v___x_2028_ = v___x_2017_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
lean_object* v___x_2030_; 
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 1, v___x_2010_);
lean_ctor_set(v___x_2008_, 0, v___x_2028_);
v___x_2030_ = v___x_2008_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2028_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v___x_2010_);
v___x_2030_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
lean_object* v___x_2032_; 
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 0, v___x_2030_);
v___x_2032_ = v___x_2025_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_del_object(v___x_2017_);
lean_del_object(v___x_2008_);
v_a_2037_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_2022_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2022_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
lean_del_object(v___x_2017_);
lean_del_object(v___x_2008_);
lean_dec_ref(v_h_u2081_1990_);
v_a_2045_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_2020_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2020_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
}
else
{
lean_dec(v___x_2014_);
if (v_useAfter_1989_ == 0)
{
lean_object* v_type_2054_; lean_object* v_val_x3f_2055_; lean_object* v_isInstance_x3f_2056_; lean_object* v_isType_x3f_2057_; lean_object* v_isInserted_x3f_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2072_; 
v_type_2054_ = lean_ctor_get(v_h_u2081_1990_, 2);
v_val_x3f_2055_ = lean_ctor_get(v_h_u2081_1990_, 3);
v_isInstance_x3f_2056_ = lean_ctor_get(v_h_u2081_1990_, 4);
v_isType_x3f_2057_ = lean_ctor_get(v_h_u2081_1990_, 5);
v_isInserted_x3f_2058_ = lean_ctor_get(v_h_u2081_1990_, 6);
v_isSharedCheck_2072_ = !lean_is_exclusive(v_h_u2081_1990_);
if (v_isSharedCheck_2072_ == 0)
{
lean_object* v_unused_2073_; lean_object* v_unused_2074_; lean_object* v_unused_2075_; 
v_unused_2073_ = lean_ctor_get(v_h_u2081_1990_, 7);
lean_dec(v_unused_2073_);
v_unused_2074_ = lean_ctor_get(v_h_u2081_1990_, 1);
lean_dec(v_unused_2074_);
v_unused_2075_ = lean_ctor_get(v_h_u2081_1990_, 0);
lean_dec(v_unused_2075_);
v___x_2060_ = v_h_u2081_1990_;
v_isShared_2061_ = v_isSharedCheck_2072_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_isInserted_x3f_2058_);
lean_inc(v_isType_x3f_2057_);
lean_inc(v_isInstance_x3f_2056_);
lean_inc(v_val_x3f_2055_);
lean_inc(v_type_2054_);
lean_dec(v_h_u2081_1990_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2072_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2065_; 
v___x_2062_ = lean_box(v___x_2002_);
v___x_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 7, v___x_2063_);
lean_ctor_set(v___x_2060_, 1, v___x_1992_);
lean_ctor_set(v___x_2060_, 0, v___x_1991_);
v___x_2065_ = v___x_2060_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_1991_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_2071_, 2, v_type_2054_);
lean_ctor_set(v_reuseFailAlloc_2071_, 3, v_val_x3f_2055_);
lean_ctor_set(v_reuseFailAlloc_2071_, 4, v_isInstance_x3f_2056_);
lean_ctor_set(v_reuseFailAlloc_2071_, 5, v_isType_x3f_2057_);
lean_ctor_set(v_reuseFailAlloc_2071_, 6, v_isInserted_x3f_2058_);
lean_ctor_set(v_reuseFailAlloc_2071_, 7, v___x_2063_);
v___x_2065_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
lean_object* v___x_2066_; lean_object* v___x_2068_; 
v___x_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 1, v___x_2010_);
lean_ctor_set(v___x_2008_, 0, v___x_2066_);
v___x_2068_ = v___x_2008_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2066_);
lean_ctor_set(v_reuseFailAlloc_2070_, 1, v___x_2010_);
v___x_2068_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
lean_object* v___x_2069_; 
v___x_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
return v___x_2069_;
}
}
}
}
else
{
lean_object* v_type_2076_; lean_object* v_val_x3f_2077_; lean_object* v_isInstance_x3f_2078_; lean_object* v_isType_x3f_2079_; lean_object* v_isRemoved_x3f_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2094_; 
v_type_2076_ = lean_ctor_get(v_h_u2081_1990_, 2);
v_val_x3f_2077_ = lean_ctor_get(v_h_u2081_1990_, 3);
v_isInstance_x3f_2078_ = lean_ctor_get(v_h_u2081_1990_, 4);
v_isType_x3f_2079_ = lean_ctor_get(v_h_u2081_1990_, 5);
v_isRemoved_x3f_2080_ = lean_ctor_get(v_h_u2081_1990_, 7);
v_isSharedCheck_2094_ = !lean_is_exclusive(v_h_u2081_1990_);
if (v_isSharedCheck_2094_ == 0)
{
lean_object* v_unused_2095_; lean_object* v_unused_2096_; lean_object* v_unused_2097_; 
v_unused_2095_ = lean_ctor_get(v_h_u2081_1990_, 6);
lean_dec(v_unused_2095_);
v_unused_2096_ = lean_ctor_get(v_h_u2081_1990_, 1);
lean_dec(v_unused_2096_);
v_unused_2097_ = lean_ctor_get(v_h_u2081_1990_, 0);
lean_dec(v_unused_2097_);
v___x_2082_ = v_h_u2081_1990_;
v_isShared_2083_ = v_isSharedCheck_2094_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_isRemoved_x3f_2080_);
lean_inc(v_isType_x3f_2079_);
lean_inc(v_isInstance_x3f_2078_);
lean_inc(v_val_x3f_2077_);
lean_inc(v_type_2076_);
lean_dec(v_h_u2081_1990_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2094_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2087_; 
v___x_2084_ = lean_box(v___x_2002_);
v___x_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 6, v___x_2085_);
lean_ctor_set(v___x_2082_, 1, v___x_1992_);
lean_ctor_set(v___x_2082_, 0, v___x_1991_);
v___x_2087_ = v___x_2082_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_1991_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_2093_, 2, v_type_2076_);
lean_ctor_set(v_reuseFailAlloc_2093_, 3, v_val_x3f_2077_);
lean_ctor_set(v_reuseFailAlloc_2093_, 4, v_isInstance_x3f_2078_);
lean_ctor_set(v_reuseFailAlloc_2093_, 5, v_isType_x3f_2079_);
lean_ctor_set(v_reuseFailAlloc_2093_, 6, v___x_2085_);
lean_ctor_set(v_reuseFailAlloc_2093_, 7, v_isRemoved_x3f_2080_);
v___x_2087_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
lean_object* v___x_2088_; lean_object* v___x_2090_; 
v___x_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 1, v___x_2010_);
lean_ctor_set(v___x_2008_, 0, v___x_2088_);
v___x_2090_ = v___x_2008_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2088_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v___x_2010_);
v___x_2090_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
lean_object* v___x_2091_; 
v___x_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
return v___x_2091_;
}
}
}
}
}
}
else
{
lean_object* v___x_2098_; size_t v___x_2099_; size_t v___x_2100_; 
lean_del_object(v___x_2008_);
lean_dec(v_fst_2005_);
v___x_2098_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___closed__0));
v___x_2099_ = ((size_t)1ULL);
v___x_2100_ = lean_usize_add(v_i_1995_, v___x_2099_);
v_i_1995_ = v___x_2100_;
v_b_1996_ = v___x_2098_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___boxed(lean_object* v_ctx_u2080_2103_, lean_object* v_useAfter_2104_, lean_object* v_h_u2081_2105_, lean_object* v___x_2106_, lean_object* v___x_2107_, lean_object* v_as_2108_, lean_object* v_sz_2109_, lean_object* v_i_2110_, lean_object* v_b_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
uint8_t v_useAfter_boxed_2117_; size_t v_sz_boxed_2118_; size_t v_i_boxed_2119_; lean_object* v_res_2120_; 
v_useAfter_boxed_2117_ = lean_unbox(v_useAfter_2104_);
v_sz_boxed_2118_ = lean_unbox_usize(v_sz_2109_);
lean_dec(v_sz_2109_);
v_i_boxed_2119_ = lean_unbox_usize(v_i_2110_);
lean_dec(v_i_2110_);
v_res_2120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(v_ctx_u2080_2103_, v_useAfter_boxed_2117_, v_h_u2081_2105_, v___x_2106_, v___x_2107_, v_as_2108_, v_sz_boxed_2118_, v_i_boxed_2119_, v_b_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec_ref(v_as_2108_);
lean_dec_ref(v_ctx_u2080_2103_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(uint8_t v_useAfter_2121_, lean_object* v_ctx_u2080_2122_, lean_object* v_h_u2081_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_){
_start:
{
lean_object* v_names_2129_; lean_object* v_fvarIds_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; size_t v_sz_2133_; size_t v___x_2134_; lean_object* v___x_2135_; 
v_names_2129_ = lean_ctor_get(v_h_u2081_2123_, 0);
v_fvarIds_2130_ = lean_ctor_get(v_h_u2081_2123_, 1);
v___x_2131_ = l_Array_zip___redArg(v_names_2129_, v_fvarIds_2130_);
v___x_2132_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___closed__0));
v_sz_2133_ = lean_array_size(v___x_2131_);
v___x_2134_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_2130_);
lean_inc_ref(v_names_2129_);
lean_inc_ref(v_h_u2081_2123_);
v___x_2135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(v_ctx_u2080_2122_, v_useAfter_2121_, v_h_u2081_2123_, v_names_2129_, v_fvarIds_2130_, v___x_2131_, v_sz_2133_, v___x_2134_, v___x_2132_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_);
lean_dec_ref(v___x_2131_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2148_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2148_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2148_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v_fst_2140_; 
v_fst_2140_ = lean_ctor_get(v_a_2136_, 0);
lean_inc(v_fst_2140_);
lean_dec(v_a_2136_);
if (lean_obj_tag(v_fst_2140_) == 0)
{
lean_object* v___x_2142_; 
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v_h_u2081_2123_);
v___x_2142_ = v___x_2138_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_h_u2081_2123_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
else
{
lean_object* v_val_2144_; lean_object* v___x_2146_; 
lean_dec_ref(v_h_u2081_2123_);
v_val_2144_ = lean_ctor_get(v_fst_2140_, 0);
lean_inc(v_val_2144_);
lean_dec_ref_known(v_fst_2140_, 1);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v_val_2144_);
v___x_2146_ = v___x_2138_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_val_2144_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
lean_dec_ref(v_h_u2081_2123_);
v_a_2149_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2135_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2135_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle___boxed(lean_object* v_useAfter_2157_, lean_object* v_ctx_u2080_2158_, lean_object* v_h_u2081_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_){
_start:
{
uint8_t v_useAfter_boxed_2165_; lean_object* v_res_2166_; 
v_useAfter_boxed_2165_ = lean_unbox(v_useAfter_2157_);
v_res_2166_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(v_useAfter_boxed_2165_, v_ctx_u2080_2158_, v_h_u2081_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_);
lean_dec(v_a_2163_);
lean_dec_ref(v_a_2162_);
lean_dec(v_a_2161_);
lean_dec_ref(v_a_2160_);
lean_dec_ref(v_ctx_u2080_2158_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(uint8_t v_useAfter_2167_, lean_object* v_lctx_u2080_2168_, size_t v_sz_2169_, size_t v_i_2170_, lean_object* v_bs_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
uint8_t v___x_2177_; 
v___x_2177_ = lean_usize_dec_lt(v_i_2170_, v_sz_2169_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; 
v___x_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2178_, 0, v_bs_2171_);
return v___x_2178_;
}
else
{
lean_object* v_v_2179_; lean_object* v___x_2180_; 
v_v_2179_ = lean_array_uget_borrowed(v_bs_2171_, v_i_2170_);
lean_inc(v_v_2179_);
v___x_2180_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(v_useAfter_2167_, v_lctx_u2080_2168_, v_v_2179_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v___x_2182_; lean_object* v_bs_x27_2183_; size_t v___x_2184_; size_t v___x_2185_; lean_object* v___x_2186_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2181_);
lean_dec_ref_known(v___x_2180_, 1);
v___x_2182_ = lean_unsigned_to_nat(0u);
v_bs_x27_2183_ = lean_array_uset(v_bs_2171_, v_i_2170_, v___x_2182_);
v___x_2184_ = ((size_t)1ULL);
v___x_2185_ = lean_usize_add(v_i_2170_, v___x_2184_);
v___x_2186_ = lean_array_uset(v_bs_x27_2183_, v_i_2170_, v_a_2181_);
v_i_2170_ = v___x_2185_;
v_bs_2171_ = v___x_2186_;
goto _start;
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_dec_ref(v_bs_2171_);
v_a_2188_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2180_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2180_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0___boxed(lean_object* v_useAfter_2196_, lean_object* v_lctx_u2080_2197_, lean_object* v_sz_2198_, lean_object* v_i_2199_, lean_object* v_bs_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
uint8_t v_useAfter_boxed_2206_; size_t v_sz_boxed_2207_; size_t v_i_boxed_2208_; lean_object* v_res_2209_; 
v_useAfter_boxed_2206_ = lean_unbox(v_useAfter_2196_);
v_sz_boxed_2207_ = lean_unbox_usize(v_sz_2198_);
lean_dec(v_sz_2198_);
v_i_boxed_2208_ = lean_unbox_usize(v_i_2199_);
lean_dec(v_i_2199_);
v_res_2209_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(v_useAfter_boxed_2206_, v_lctx_u2080_2197_, v_sz_boxed_2207_, v_i_boxed_2208_, v_bs_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec_ref(v_lctx_u2080_2197_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(uint8_t v_useAfter_2210_, lean_object* v_lctx_u2080_2211_, lean_object* v_hs_u2081_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_){
_start:
{
size_t v_sz_2218_; size_t v___x_2219_; lean_object* v___x_2220_; 
v_sz_2218_ = lean_array_size(v_hs_u2081_2212_);
v___x_2219_ = ((size_t)0ULL);
v___x_2220_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(v_useAfter_2210_, v_lctx_u2080_2211_, v_sz_2218_, v___x_2219_, v_hs_u2081_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses___boxed(lean_object* v_useAfter_2221_, lean_object* v_lctx_u2080_2222_, lean_object* v_hs_u2081_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_){
_start:
{
uint8_t v_useAfter_boxed_2229_; lean_object* v_res_2230_; 
v_useAfter_boxed_2229_ = lean_unbox(v_useAfter_2221_);
v_res_2230_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(v_useAfter_boxed_2229_, v_lctx_u2080_2222_, v_hs_u2081_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
lean_dec_ref(v_lctx_u2080_2222_);
return v_res_2230_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2(void){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2235_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__1));
v___x_2236_ = l_Lean_stringToMessageData(v___x_2235_);
return v___x_2236_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4(void){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__3));
v___x_2239_ = l_Lean_stringToMessageData(v___x_2238_);
return v___x_2239_;
}
}
static lean_object* _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6(void){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = ((lean_object*)(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__5));
v___x_2242_ = l_Lean_stringToMessageData(v___x_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(uint8_t v_useAfter_2243_, lean_object* v_g_u2080_2244_, lean_object* v_i_u2081_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_){
_start:
{
lean_object* v___x_2251_; lean_object* v_mctx_2252_; lean_object* v___x_2253_; 
v___x_2251_ = lean_st_ref_get(v_a_2247_);
v_mctx_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc_ref(v_mctx_2252_);
lean_dec(v___x_2251_);
v___x_2253_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2252_, v_g_u2080_2244_);
lean_dec_ref(v_mctx_2252_);
if (lean_obj_tag(v___x_2253_) == 1)
{
lean_object* v_toCold_2254_; lean_object* v_val_2255_; lean_object* v_options_2256_; lean_object* v_lctx_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v_toInteractiveGoalCore_2261_; lean_object* v_fst_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2359_; 
v_toCold_2254_ = lean_ctor_get(v_a_2248_, 0);
v_val_2255_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_val_2255_);
lean_dec_ref_known(v___x_2253_, 1);
v_options_2256_ = lean_ctor_get(v_toCold_2254_, 2);
v_lctx_2257_ = lean_ctor_get(v_val_2255_, 1);
lean_inc_ref(v_lctx_2257_);
lean_dec(v_val_2255_);
v___x_2258_ = lean_box(1);
lean_inc_ref(v_options_2256_);
v___x_2259_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2259_, 0, v_options_2256_);
lean_ctor_set(v___x_2259_, 1, v___x_2258_);
lean_ctor_set(v___x_2259_, 2, v___x_2258_);
v___x_2260_ = l_Lean_LocalContext_sanitizeNames(v_lctx_2257_, v___x_2259_);
v_toInteractiveGoalCore_2261_ = lean_ctor_get(v_i_u2081_2245_, 0);
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
v_userName_x3f_2266_ = lean_ctor_get(v_i_u2081_2245_, 1);
v_goalPrefix_2267_ = lean_ctor_get(v_i_u2081_2245_, 2);
v_mvarId_2268_ = lean_ctor_get(v_i_u2081_2245_, 3);
v_isRemoved_x3f_2269_ = lean_ctor_get(v_i_u2081_2245_, 5);
v_isSharedCheck_2356_ = !lean_is_exclusive(v_i_u2081_2245_);
if (v_isSharedCheck_2356_ == 0)
{
lean_object* v_unused_2357_; lean_object* v_unused_2358_; 
v_unused_2357_ = lean_ctor_get(v_i_u2081_2245_, 4);
lean_dec(v_unused_2357_);
v_unused_2358_ = lean_ctor_get(v_i_u2081_2245_, 0);
lean_dec(v_unused_2358_);
v___x_2271_ = v_i_u2081_2245_;
v_isShared_2272_ = v_isSharedCheck_2356_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_isRemoved_x3f_2269_);
lean_inc(v_mvarId_2268_);
lean_inc(v_goalPrefix_2267_);
lean_inc(v_userName_x3f_2266_);
lean_dec(v_i_u2081_2245_);
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
v___x_2279_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(v_useAfter_2243_, v_fst_2262_, v_hyps_2273_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
lean_dec(v_fst_2262_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref_known(v___x_2279_, 1);
v___x_2281_ = l_Lean_Expr_mvar___override(v_g_u2080_2244_);
lean_inc(v_a_2249_);
lean_inc_ref(v_a_2248_);
lean_inc(v_a_2247_);
lean_inc_ref(v_a_2246_);
v___x_2282_ = lean_infer_type(v___x_2281_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v___x_2284_; lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2338_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2283_);
lean_dec_ref_known(v___x_2282_, 1);
v___x_2284_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_a_2283_, v_a_2247_);
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
v___x_2289_ = lean_st_ref_get(v_a_2247_);
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
v___x_2294_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_type_2293_, v_a_2247_);
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
lean_dec_ref(v___x_2294_);
v___x_2296_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(v_a_2285_, v_a_2295_, v_useAfter_2243_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; lean_object* v___x_2298_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_a_2297_);
lean_dec_ref_known(v___x_2296_, 1);
v___x_2298_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(v_useAfter_2243_, v_a_2297_, v_type_2274_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
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
v___x_2335_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_2334_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
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
lean_dec(v_g_u2080_2244_);
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
lean_dec(v___x_2253_);
lean_dec_ref(v_i_u2081_2245_);
v___x_2361_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4);
v___x_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2362_, 0, v_g_u2080_2244_);
v___x_2363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2361_);
lean_ctor_set(v___x_2363_, 1, v___x_2362_);
v___x_2364_ = lean_obj_once(&l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6, &l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6_once, _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6);
v___x_2365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2363_);
lean_ctor_set(v___x_2365_, 1, v___x_2364_);
v___x_2366_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_2365_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
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
lean_object* v_toCold_2470_; lean_object* v_val_2471_; lean_object* v_options_2472_; lean_object* v_lctx_2473_; lean_object* v_localInstances_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v_fst_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
lean_dec(v_goal_2460_);
v_toCold_2470_ = lean_ctor_get(v___y_2464_, 0);
v_val_2471_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_val_2471_);
lean_dec_ref_known(v___x_2469_, 1);
v_options_2472_ = lean_ctor_get(v_toCold_2470_, 2);
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
v___x_2479_ = lean_apply_2(v_action_2461_, v_fst_2478_, v_val_2471_);
v___x_2480_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(v_fst_2478_, v_localInstances_2474_, v___x_2479_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
return v___x_2480_;
}
else
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
lean_dec(v___x_2469_);
lean_dec_ref(v_action_2461_);
v___x_2481_ = lean_obj_once(&l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1, &l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1_once, _init_l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1);
v___x_2482_ = l_Lean_MessageData_ofName(v_goal_2460_);
v___x_2483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2481_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
v___x_2484_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_2483_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
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
uint8_t v___x_3253__boxed_2543_; uint8_t v_res_2544_; lean_object* v_r_2545_; 
v___x_3253__boxed_2543_ = lean_unbox(v___x_2540_);
v_res_2544_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(v_a_2539_, v___x_3253__boxed_2543_, v_before_2541_, v_after_2542_);
lean_dec(v_after_2542_);
lean_dec(v_before_2541_);
lean_dec(v_a_2539_);
v_r_2545_ = lean_box(v_res_2544_);
return v_r_2545_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5(uint8_t v_useAfter_2546_, lean_object* v_a_2547_, lean_object* v___x_2548_, lean_object* v_x_2549_){
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
if (v_useAfter_2546_ == 0)
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
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___boxed(lean_object* v_useAfter_2560_, lean_object* v_a_2561_, lean_object* v___x_2562_, lean_object* v_x_2563_){
_start:
{
uint8_t v_useAfter_boxed_2564_; lean_object* v_res_2565_; 
v_useAfter_boxed_2564_ = lean_unbox(v_useAfter_2560_);
v_res_2565_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5(v_useAfter_boxed_2564_, v_a_2561_, v___x_2562_, v_x_2563_);
lean_dec(v_x_2563_);
lean_dec(v___x_2562_);
lean_dec(v_a_2561_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0(lean_object* v_mvarId_2566_, lean_object* v___y_2567_, uint8_t v_useAfter_2568_, lean_object* v_a_2569_, lean_object* v_v_2570_, uint8_t v___x_2571_, lean_object* v_toInteractiveGoalCore_2572_, lean_object* v_userName_x3f_2573_, lean_object* v_goalPrefix_2574_, lean_object* v_isInserted_x3f_2575_, lean_object* v_isRemoved_x3f_2576_, lean_object* v___lctx_u2081_2577_, lean_object* v___md_u2081_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
uint8_t v___x_2584_; 
v___x_2584_ = l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4(v_mvarId_2566_, v___y_2567_);
if (v___x_2584_ == 0)
{
lean_object* v___x_2585_; 
v___x_2585_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5(v_useAfter_2568_, v_a_2569_, v_mvarId_2566_, v___y_2567_);
if (lean_obj_tag(v___x_2585_) == 1)
{
lean_object* v_val_2586_; lean_object* v___x_2587_; 
lean_dec(v_isRemoved_x3f_2576_);
lean_dec(v_isInserted_x3f_2575_);
lean_dec_ref(v_goalPrefix_2574_);
lean_dec(v_userName_x3f_2573_);
lean_dec_ref(v_toInteractiveGoalCore_2572_);
lean_dec(v_mvarId_2566_);
v_val_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc(v_val_2586_);
lean_dec_ref_known(v___x_2585_, 1);
v___x_2587_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(v_useAfter_2568_, v_val_2586_, v_v_2570_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
return v___x_2587_;
}
else
{
lean_dec(v___x_2585_);
lean_dec(v_v_2570_);
if (v_useAfter_2568_ == 0)
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
lean_dec(v_isRemoved_x3f_2576_);
v___x_2588_ = lean_box(v___x_2571_);
v___x_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2588_);
v___x_2590_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2590_, 0, v_toInteractiveGoalCore_2572_);
lean_ctor_set(v___x_2590_, 1, v_userName_x3f_2573_);
lean_ctor_set(v___x_2590_, 2, v_goalPrefix_2574_);
lean_ctor_set(v___x_2590_, 3, v_mvarId_2566_);
lean_ctor_set(v___x_2590_, 4, v_isInserted_x3f_2575_);
lean_ctor_set(v___x_2590_, 5, v___x_2589_);
v___x_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2590_);
return v___x_2591_;
}
else
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
lean_dec(v_isInserted_x3f_2575_);
v___x_2592_ = lean_box(v___x_2571_);
v___x_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2592_);
v___x_2594_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2594_, 0, v_toInteractiveGoalCore_2572_);
lean_ctor_set(v___x_2594_, 1, v_userName_x3f_2573_);
lean_ctor_set(v___x_2594_, 2, v_goalPrefix_2574_);
lean_ctor_set(v___x_2594_, 3, v_mvarId_2566_);
lean_ctor_set(v___x_2594_, 4, v___x_2593_);
lean_ctor_set(v___x_2594_, 5, v_isRemoved_x3f_2576_);
v___x_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
return v___x_2595_;
}
}
}
else
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
lean_dec(v_isInserted_x3f_2575_);
lean_dec(v_v_2570_);
v___x_2596_ = lean_box(0);
v___x_2597_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2597_, 0, v_toInteractiveGoalCore_2572_);
lean_ctor_set(v___x_2597_, 1, v_userName_x3f_2573_);
lean_ctor_set(v___x_2597_, 2, v_goalPrefix_2574_);
lean_ctor_set(v___x_2597_, 3, v_mvarId_2566_);
lean_ctor_set(v___x_2597_, 4, v___x_2596_);
lean_ctor_set(v___x_2597_, 5, v_isRemoved_x3f_2576_);
v___x_2598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2597_);
return v___x_2598_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0___boxed(lean_object** _args){
lean_object* v_mvarId_2599_ = _args[0];
lean_object* v___y_2600_ = _args[1];
lean_object* v_useAfter_2601_ = _args[2];
lean_object* v_a_2602_ = _args[3];
lean_object* v_v_2603_ = _args[4];
lean_object* v___x_2604_ = _args[5];
lean_object* v_toInteractiveGoalCore_2605_ = _args[6];
lean_object* v_userName_x3f_2606_ = _args[7];
lean_object* v_goalPrefix_2607_ = _args[8];
lean_object* v_isInserted_x3f_2608_ = _args[9];
lean_object* v_isRemoved_x3f_2609_ = _args[10];
lean_object* v___lctx_u2081_2610_ = _args[11];
lean_object* v___md_u2081_2611_ = _args[12];
lean_object* v___y_2612_ = _args[13];
lean_object* v___y_2613_ = _args[14];
lean_object* v___y_2614_ = _args[15];
lean_object* v___y_2615_ = _args[16];
lean_object* v___y_2616_ = _args[17];
_start:
{
uint8_t v_useAfter_boxed_2617_; uint8_t v___x_3295__boxed_2618_; lean_object* v_res_2619_; 
v_useAfter_boxed_2617_ = lean_unbox(v_useAfter_2601_);
v___x_3295__boxed_2618_ = lean_unbox(v___x_2604_);
v_res_2619_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0(v_mvarId_2599_, v___y_2600_, v_useAfter_boxed_2617_, v_a_2602_, v_v_2603_, v___x_3295__boxed_2618_, v_toInteractiveGoalCore_2605_, v_userName_x3f_2606_, v_goalPrefix_2607_, v_isInserted_x3f_2608_, v_isRemoved_x3f_2609_, v___lctx_u2081_2610_, v___md_u2081_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec_ref(v___md_u2081_2611_);
lean_dec_ref(v___lctx_u2081_2610_);
lean_dec(v_a_2602_);
lean_dec(v___y_2600_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8(lean_object* v___y_2620_, uint8_t v_useAfter_2621_, lean_object* v_a_2622_, uint8_t v___x_2623_, size_t v_sz_2624_, size_t v_i_2625_, lean_object* v_bs_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
uint8_t v___x_2632_; 
v___x_2632_ = lean_usize_dec_lt(v_i_2625_, v_sz_2624_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2633_; 
lean_dec(v_a_2622_);
lean_dec(v___y_2620_);
v___x_2633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2633_, 0, v_bs_2626_);
return v___x_2633_;
}
else
{
lean_object* v_v_2634_; lean_object* v_toInteractiveGoalCore_2635_; lean_object* v_userName_x3f_2636_; lean_object* v_goalPrefix_2637_; lean_object* v_mvarId_2638_; lean_object* v_isInserted_x3f_2639_; lean_object* v_isRemoved_x3f_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___f_2643_; lean_object* v___x_2644_; 
v_v_2634_ = lean_array_uget_borrowed(v_bs_2626_, v_i_2625_);
v_toInteractiveGoalCore_2635_ = lean_ctor_get(v_v_2634_, 0);
v_userName_x3f_2636_ = lean_ctor_get(v_v_2634_, 1);
v_goalPrefix_2637_ = lean_ctor_get(v_v_2634_, 2);
v_mvarId_2638_ = lean_ctor_get(v_v_2634_, 3);
v_isInserted_x3f_2639_ = lean_ctor_get(v_v_2634_, 4);
v_isRemoved_x3f_2640_ = lean_ctor_get(v_v_2634_, 5);
v___x_2641_ = lean_box(v_useAfter_2621_);
v___x_2642_ = lean_box(v___x_2623_);
lean_inc(v_isRemoved_x3f_2640_);
lean_inc(v_isInserted_x3f_2639_);
lean_inc_ref(v_goalPrefix_2637_);
lean_inc(v_userName_x3f_2636_);
lean_inc_ref(v_toInteractiveGoalCore_2635_);
lean_inc(v_v_2634_);
lean_inc(v_a_2622_);
lean_inc(v___y_2620_);
lean_inc_n(v_mvarId_2638_, 2);
v___f_2643_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0___boxed), 18, 11);
lean_closure_set(v___f_2643_, 0, v_mvarId_2638_);
lean_closure_set(v___f_2643_, 1, v___y_2620_);
lean_closure_set(v___f_2643_, 2, v___x_2641_);
lean_closure_set(v___f_2643_, 3, v_a_2622_);
lean_closure_set(v___f_2643_, 4, v_v_2634_);
lean_closure_set(v___f_2643_, 5, v___x_2642_);
lean_closure_set(v___f_2643_, 6, v_toInteractiveGoalCore_2635_);
lean_closure_set(v___f_2643_, 7, v_userName_x3f_2636_);
lean_closure_set(v___f_2643_, 8, v_goalPrefix_2637_);
lean_closure_set(v___f_2643_, 9, v_isInserted_x3f_2639_);
lean_closure_set(v___f_2643_, 10, v_isRemoved_x3f_2640_);
v___x_2644_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(v_mvarId_2638_, v___f_2643_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v_a_2645_; lean_object* v___x_2646_; lean_object* v_bs_x27_2647_; size_t v___x_2648_; size_t v___x_2649_; lean_object* v___x_2650_; 
v_a_2645_ = lean_ctor_get(v___x_2644_, 0);
lean_inc(v_a_2645_);
lean_dec_ref_known(v___x_2644_, 1);
v___x_2646_ = lean_unsigned_to_nat(0u);
v_bs_x27_2647_ = lean_array_uset(v_bs_2626_, v_i_2625_, v___x_2646_);
v___x_2648_ = ((size_t)1ULL);
v___x_2649_ = lean_usize_add(v_i_2625_, v___x_2648_);
v___x_2650_ = lean_array_uset(v_bs_x27_2647_, v_i_2625_, v_a_2645_);
v_i_2625_ = v___x_2649_;
v_bs_2626_ = v___x_2650_;
goto _start;
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
lean_dec_ref(v_bs_2626_);
lean_dec(v_a_2622_);
lean_dec(v___y_2620_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8___boxed(lean_object* v___y_2660_, lean_object* v_useAfter_2661_, lean_object* v_a_2662_, lean_object* v___x_2663_, lean_object* v_sz_2664_, lean_object* v_i_2665_, lean_object* v_bs_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
uint8_t v_useAfter_boxed_2672_; uint8_t v___x_3349__boxed_2673_; size_t v_sz_boxed_2674_; size_t v_i_boxed_2675_; lean_object* v_res_2676_; 
v_useAfter_boxed_2672_ = lean_unbox(v_useAfter_2661_);
v___x_3349__boxed_2673_ = lean_unbox(v___x_2663_);
v_sz_boxed_2674_ = lean_unbox_usize(v_sz_2664_);
lean_dec(v_sz_2664_);
v_i_boxed_2675_ = lean_unbox_usize(v_i_2665_);
lean_dec(v_i_2665_);
v_res_2676_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8(v___y_2660_, v_useAfter_boxed_2672_, v_a_2662_, v___x_3349__boxed_2673_, v_sz_boxed_2674_, v_i_boxed_2675_, v_bs_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7(uint8_t v_useAfter_2677_, lean_object* v_a_2678_, lean_object* v___y_2679_, uint8_t v___x_2680_, size_t v_sz_2681_, size_t v_i_2682_, lean_object* v_bs_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
uint8_t v___x_2689_; 
v___x_2689_ = lean_usize_dec_lt(v_i_2682_, v_sz_2681_);
if (v___x_2689_ == 0)
{
lean_object* v___x_2690_; 
lean_dec(v___y_2679_);
lean_dec(v_a_2678_);
v___x_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2690_, 0, v_bs_2683_);
return v___x_2690_;
}
else
{
lean_object* v_v_2691_; lean_object* v_toInteractiveGoalCore_2692_; lean_object* v_userName_x3f_2693_; lean_object* v_goalPrefix_2694_; lean_object* v_mvarId_2695_; lean_object* v_isInserted_x3f_2696_; lean_object* v_isRemoved_x3f_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___f_2700_; lean_object* v___x_2701_; 
v_v_2691_ = lean_array_uget_borrowed(v_bs_2683_, v_i_2682_);
v_toInteractiveGoalCore_2692_ = lean_ctor_get(v_v_2691_, 0);
v_userName_x3f_2693_ = lean_ctor_get(v_v_2691_, 1);
v_goalPrefix_2694_ = lean_ctor_get(v_v_2691_, 2);
v_mvarId_2695_ = lean_ctor_get(v_v_2691_, 3);
v_isInserted_x3f_2696_ = lean_ctor_get(v_v_2691_, 4);
v_isRemoved_x3f_2697_ = lean_ctor_get(v_v_2691_, 5);
v___x_2698_ = lean_box(v_useAfter_2677_);
v___x_2699_ = lean_box(v___x_2680_);
lean_inc(v_isRemoved_x3f_2697_);
lean_inc(v_isInserted_x3f_2696_);
lean_inc_ref(v_goalPrefix_2694_);
lean_inc(v_userName_x3f_2693_);
lean_inc_ref(v_toInteractiveGoalCore_2692_);
lean_inc(v_v_2691_);
lean_inc(v_a_2678_);
lean_inc(v___y_2679_);
lean_inc_n(v_mvarId_2695_, 2);
v___f_2700_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0___boxed), 18, 11);
lean_closure_set(v___f_2700_, 0, v_mvarId_2695_);
lean_closure_set(v___f_2700_, 1, v___y_2679_);
lean_closure_set(v___f_2700_, 2, v___x_2698_);
lean_closure_set(v___f_2700_, 3, v_a_2678_);
lean_closure_set(v___f_2700_, 4, v_v_2691_);
lean_closure_set(v___f_2700_, 5, v___x_2699_);
lean_closure_set(v___f_2700_, 6, v_toInteractiveGoalCore_2692_);
lean_closure_set(v___f_2700_, 7, v_userName_x3f_2693_);
lean_closure_set(v___f_2700_, 8, v_goalPrefix_2694_);
lean_closure_set(v___f_2700_, 9, v_isInserted_x3f_2696_);
lean_closure_set(v___f_2700_, 10, v_isRemoved_x3f_2697_);
v___x_2701_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(v_mvarId_2695_, v___f_2700_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; lean_object* v___x_2703_; lean_object* v_bs_x27_2704_; size_t v___x_2705_; size_t v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2702_);
lean_dec_ref_known(v___x_2701_, 1);
v___x_2703_ = lean_unsigned_to_nat(0u);
v_bs_x27_2704_ = lean_array_uset(v_bs_2683_, v_i_2682_, v___x_2703_);
v___x_2705_ = ((size_t)1ULL);
v___x_2706_ = lean_usize_add(v_i_2682_, v___x_2705_);
v___x_2707_ = lean_array_uset(v_bs_x27_2704_, v_i_2682_, v_a_2702_);
v___x_2708_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8(v___y_2679_, v_useAfter_2677_, v_a_2678_, v___x_2680_, v_sz_2681_, v___x_2706_, v___x_2707_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
return v___x_2708_;
}
else
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2716_; 
lean_dec_ref(v_bs_2683_);
lean_dec(v___y_2679_);
lean_dec(v_a_2678_);
v_a_2709_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2711_ = v___x_2701_;
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2701_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_a_2709_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___boxed(lean_object* v_useAfter_2717_, lean_object* v_a_2718_, lean_object* v___y_2719_, lean_object* v___x_2720_, lean_object* v_sz_2721_, lean_object* v_i_2722_, lean_object* v_bs_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
uint8_t v_useAfter_boxed_2729_; uint8_t v___x_3413__boxed_2730_; size_t v_sz_boxed_2731_; size_t v_i_boxed_2732_; lean_object* v_res_2733_; 
v_useAfter_boxed_2729_ = lean_unbox(v_useAfter_2717_);
v___x_3413__boxed_2730_ = lean_unbox(v___x_2720_);
v_sz_boxed_2731_ = lean_unbox_usize(v_sz_2721_);
lean_dec(v_sz_2721_);
v_i_boxed_2732_ = lean_unbox_usize(v_i_2722_);
lean_dec(v_i_2722_);
v_res_2733_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7(v_useAfter_boxed_2729_, v_a_2718_, v___y_2719_, v___x_3413__boxed_2730_, v_sz_boxed_2731_, v_i_boxed_2732_, v_bs_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_diffInteractiveGoals(uint8_t v_useAfter_2734_, lean_object* v_info_2735_, lean_object* v_igs_u2081_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_){
_start:
{
lean_object* v_toCold_2742_; lean_object* v_options_2743_; lean_object* v___x_2744_; uint8_t v___x_2745_; lean_object* v___y_2747_; 
v_toCold_2742_ = lean_ctor_get(v_a_2739_, 0);
v_options_2743_ = lean_ctor_get(v_toCold_2742_, 2);
v___x_2744_ = l___private_Lean_Widget_Diff_0__Lean_Widget_showTacticDiff;
v___x_2745_ = l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(v_options_2743_, v___x_2744_);
if (v___x_2745_ == 0)
{
lean_object* v___x_2779_; 
lean_dec_ref(v_info_2735_);
v___x_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2779_, 0, v_igs_u2081_2736_);
return v___x_2779_;
}
else
{
if (v_useAfter_2734_ == 0)
{
lean_object* v_goalsAfter_2780_; 
v_goalsAfter_2780_ = lean_ctor_get(v_info_2735_, 4);
lean_inc(v_goalsAfter_2780_);
v___y_2747_ = v_goalsAfter_2780_;
goto v___jp_2746_;
}
else
{
lean_object* v_goalsBefore_2781_; 
v_goalsBefore_2781_ = lean_ctor_get(v_info_2735_, 2);
lean_inc(v_goalsBefore_2781_);
v___y_2747_ = v_goalsBefore_2781_;
goto v___jp_2746_;
}
}
v___jp_2746_:
{
lean_object* v_goalsBefore_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v_goalsBefore_2748_ = lean_ctor_get(v_info_2735_, 2);
lean_inc(v_goalsBefore_2748_);
lean_dec_ref(v_info_2735_);
v___x_2749_ = lean_box(1);
v___x_2750_ = l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(v___x_2749_, v_goalsBefore_2748_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; size_t v_sz_2752_; size_t v___x_2753_; lean_object* v___x_2754_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_a_2751_);
lean_dec_ref_known(v___x_2750_, 1);
v_sz_2752_ = lean_array_size(v_igs_u2081_2736_);
v___x_2753_ = ((size_t)0ULL);
v___x_2754_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7(v_useAfter_2734_, v_a_2751_, v___y_2747_, v___x_2745_, v_sz_2752_, v___x_2753_, v_igs_u2081_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2754_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2754_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
v_a_2763_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2754_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2754_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
else
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
lean_dec(v___y_2747_);
lean_dec_ref(v_igs_u2081_2736_);
v_a_2771_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2750_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2750_);
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
LEAN_EXPORT lean_object* l_Lean_Widget_diffInteractiveGoals___boxed(lean_object* v_useAfter_2782_, lean_object* v_info_2783_, lean_object* v_igs_u2081_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_){
_start:
{
uint8_t v_useAfter_boxed_2790_; lean_object* v_res_2791_; 
v_useAfter_boxed_2790_ = lean_unbox(v_useAfter_2782_);
v_res_2791_ = l_Lean_Widget_diffInteractiveGoals(v_useAfter_boxed_2790_, v_info_2783_, v_igs_u2081_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_);
lean_dec(v_a_2788_);
lean_dec_ref(v_a_2787_);
lean_dec(v_a_2786_);
lean_dec_ref(v_a_2785_);
return v_res_2791_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2(lean_object* v_00_u03b4_2792_, lean_object* v_t_2793_, lean_object* v_k_2794_){
_start:
{
lean_object* v___x_2795_; 
v___x_2795_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(v_t_2793_, v_k_2794_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___boxed(lean_object* v_00_u03b4_2796_, lean_object* v_t_2797_, lean_object* v_k_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2(v_00_u03b4_2796_, v_t_2797_, v_k_2798_);
lean_dec(v_k_2798_);
lean_dec(v_t_2797_);
return v_res_2799_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3(lean_object* v_00_u03b2_2800_, lean_object* v_k_2801_, lean_object* v_t_2802_){
_start:
{
uint8_t v___x_2803_; 
v___x_2803_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_k_2801_, v_t_2802_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___boxed(lean_object* v_00_u03b2_2804_, lean_object* v_k_2805_, lean_object* v_t_2806_){
_start:
{
uint8_t v_res_2807_; lean_object* v_r_2808_; 
v_res_2807_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3(v_00_u03b2_2804_, v_k_2805_, v_t_2806_);
lean_dec(v_t_2806_);
lean_dec(v_k_2805_);
v_r_2808_ = lean_box(v_res_2807_);
return v_r_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6(lean_object* v_00_u03b1_2809_, lean_object* v_lctx_2810_, lean_object* v_localInsts_2811_, lean_object* v_x_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
lean_object* v___x_2818_; 
v___x_2818_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(v_lctx_2810_, v_localInsts_2811_, v_x_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___boxed(lean_object* v_00_u03b1_2819_, lean_object* v_lctx_2820_, lean_object* v_localInsts_2821_, lean_object* v_x_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6(v_00_u03b1_2819_, v_lctx_2820_, v_localInsts_2821_, v_x_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6(lean_object* v_00_u03b1_2829_, lean_object* v_goal_2830_, lean_object* v_action_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_){
_start:
{
lean_object* v___x_2837_; 
v___x_2837_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(v_goal_2830_, v_action_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___boxed(lean_object* v_00_u03b1_2838_, lean_object* v_goal_2839_, lean_object* v_action_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6(v_00_u03b1_2838_, v_goal_2839_, v_action_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
return v_res_2846_;
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
