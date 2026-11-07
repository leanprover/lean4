// Lean compiler output
// Module: Lean.Meta.Tactic.Rewrite
// Imports: public import Lean.Meta.AppBuilder public import Lean.Meta.MatchUtil public import Lean.Meta.KAbstract public import Lean.Meta.Tactic.Apply public import Lean.Meta.BinderNameHint
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isSort(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_inlineExpr(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_appendParentTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_postprocessAppMVars(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Meta_tactic_skipAssignedInstances;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasBinderNameHint(lean_object*);
lean_object* l_Lean_Expr_resolveBinderNameHint(lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__6___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__1_spec__5_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unsupported binder"};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "application type mismatch"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "function expected"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "unexpected loose bound variable"};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "type expected"};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__1_spec__5_spec__11(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___lam__0___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_a"};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(228, 106, 112, 29, 6, 211, 214, 169)}};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__5(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_MVarId_rewrite_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_MVarId_rewrite_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 84, .m_capacity = 84, .m_length = 83, .m_data = "Invalid rewrite argument: Expected an equality or iff proof or definition name, but"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__0 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__1;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "is "};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__2 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__3;
static const lean_array_object l_Lean_MVarId_rewrite___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__4 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__4_value;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__5 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__5_value;
static const lean_ctor_object l_Lean_MVarId_rewrite___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__6 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__6_value;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Motive is dependent:"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__7 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__7_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__8;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 122, .m_capacity = 122, .m_length = 121, .m_data = "The rewrite tactic cannot substitute terms on which the type of the target expression depends. The type of the expression"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__9 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__9_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__10;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "\ndepends on the value"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__11 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__11_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__12;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "motive is not type correct:"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__13 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__13_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__14;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\nError: "};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__15 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__15_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__16;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 353, .m_capacity = 353, .m_length = 352, .m_data = "\n\nExplanation: The rewrite tactic rewrites an expression 'e' using an equality 'a = b' by the following process. First, it looks for all 'a' in 'e'. Second, it tries to abstract these occurrences of 'a' to create a function 'm := fun _a => ...', called the *motive*, with the property that 'm a' is definitionally equal to 'e'. Third, we observe that '"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__17 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__17_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__18;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "' implies that 'm a = m b', which can be used with lemmas such as '"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__19 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__19_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__20;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__21 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__21_value;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mpr"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__22 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__22_value;
static const lean_ctor_object l_Lean_MVarId_rewrite___lam__1___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_MVarId_rewrite___lam__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__23_value_aux_0),((lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(146, 109, 21, 40, 70, 113, 251, 6)}};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__23 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__23_value;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 348, .m_capacity = 348, .m_length = 347, .m_data = "' to change the goal. However, if 'e' depends on specific properties of 'a', then the motive 'm' might not typecheck.\n\nPossible solutions: use rewrite's 'occs' configuration option to limit which occurrences are rewritten, or use 'simp' or 'conv' mode, which have strategies for certain kinds of dependencies (these tactics can handle proofs and '"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__24 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__24_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__25;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__26 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__26_value;
static const lean_ctor_object l_Lean_MVarId_rewrite___lam__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__27 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__27_value;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 118, .m_capacity = 118, .m_length = 117, .m_data = "' instances whose types depend on the rewritten term, and 'simp' can apply user-defined '@[congr]' theorems as well)."};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__28 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__28_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__29;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Did not find an occurrence of the pattern"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__30 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__30_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__31;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "\nin the target expression"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__32 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__32_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__33;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 77, .m_capacity = 77, .m_length = 76, .m_data = "Invalid rewrite argument: The pattern to be substituted is a metavariable (`"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__34 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__34_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__35;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "`) in this equality"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__36 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__36_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__37;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "a value of type"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__38 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__38_value;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "a proof of"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__39 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__39_value;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__40 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__40_value;
static const lean_ctor_object l_Lean_MVarId_rewrite___lam__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__41 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__41_value;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "propext"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__42 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__42_value;
static const lean_ctor_object l_Lean_MVarId_rewrite___lam__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(53, 150, 49, 30, 125, 3, 39, 172)}};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__43 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__43_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__44;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_rewrite___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "rewrite"};
static const lean_object* l_Lean_MVarId_rewrite___closed__0 = (const lean_object*)&l_Lean_MVarId_rewrite___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_rewrite___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_rewrite___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 67, 55, 19, 78, 216, 184, 166)}};
static const lean_object* l_Lean_MVarId_rewrite___closed__1 = (const lean_object*)&l_Lean_MVarId_rewrite___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__3_spec__7___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(0);
return v___x_3_;
}
else
{
lean_object* v_key_4_; lean_object* v_value_5_; lean_object* v_tail_6_; uint8_t v___x_7_; 
v_key_4_ = lean_ctor_get(v_x_2_, 0);
v_value_5_ = lean_ctor_get(v_x_2_, 1);
v_tail_6_ = lean_ctor_get(v_x_2_, 2);
v___x_7_ = l_Lean_ExprStructEq_beq(v_key_4_, v_a_1_);
if (v___x_7_ == 0)
{
v_x_2_ = v_tail_6_;
goto _start;
}
else
{
lean_object* v___x_9_; 
lean_inc(v_value_5_);
v___x_9_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_9_, 0, v_value_5_);
return v___x_9_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__3_spec__7___redArg___boxed(lean_object* v_a_10_, lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__3_spec__7___redArg(v_a_10_, v_x_11_);
lean_dec(v_x_11_);
lean_dec_ref(v_a_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__3___redArg(lean_object* v_m_13_, lean_object* v_a_14_){
_start:
{
lean_object* v_buckets_15_; lean_object* v___x_16_; uint64_t v___x_17_; uint64_t v___x_18_; uint64_t v___x_19_; uint64_t v_fold_20_; uint64_t v___x_21_; uint64_t v___x_22_; uint64_t v___x_23_; size_t v___x_24_; size_t v___x_25_; size_t v___x_26_; size_t v___x_27_; size_t v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v_buckets_15_ = lean_ctor_get(v_m_13_, 1);
v___x_16_ = lean_array_get_size(v_buckets_15_);
v___x_17_ = l_Lean_ExprStructEq_hash(v_a_14_);
v___x_18_ = 32ULL;
v___x_19_ = lean_uint64_shift_right(v___x_17_, v___x_18_);
v_fold_20_ = lean_uint64_xor(v___x_17_, v___x_19_);
v___x_21_ = 16ULL;
v___x_22_ = lean_uint64_shift_right(v_fold_20_, v___x_21_);
v___x_23_ = lean_uint64_xor(v_fold_20_, v___x_22_);
v___x_24_ = lean_uint64_to_usize(v___x_23_);
v___x_25_ = lean_usize_of_nat(v___x_16_);
v___x_26_ = ((size_t)1ULL);
v___x_27_ = lean_usize_sub(v___x_25_, v___x_26_);
v___x_28_ = lean_usize_land(v___x_24_, v___x_27_);
v___x_29_ = lean_array_uget_borrowed(v_buckets_15_, v___x_28_);
v___x_30_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__3_spec__7___redArg(v_a_14_, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__3___redArg___boxed(lean_object* v_m_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__3___redArg(v_m_31_, v_a_32_);
lean_dec_ref(v_a_32_);
lean_dec_ref(v_m_31_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___lam__0(lean_object* v_fst_34_, lean_object* v_a_35_, lean_object* v_____r_36_, lean_object* v_fType_x3f_37_, lean_object* v_j_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_45_ = lean_array_push(v_fst_34_, v_a_35_);
v___x_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_46_, 0, v_fType_x3f_37_);
lean_ctor_set(v___x_46_, 1, v_j_38_);
v___x_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_45_);
lean_ctor_set(v___x_47_, 1, v___x_46_);
v___x_48_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
v___x_49_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___lam__0___boxed(lean_object* v_fst_50_, lean_object* v_a_51_, lean_object* v_____r_52_, lean_object* v_fType_x3f_53_, lean_object* v_j_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___lam__0(v_fst_50_, v_a_51_, v_____r_52_, v_fType_x3f_53_, v_j_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
lean_dec(v___y_55_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__1_spec__4(lean_object* v_msgData_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v___x_68_; lean_object* v_env_69_; uint8_t v___x_70_; lean_object* v_env_71_; lean_object* v___x_72_; lean_object* v_toCold_73_; lean_object* v_mctx_74_; lean_object* v_lctx_75_; lean_object* v_options_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_68_ = lean_st_ref_get(v___y_66_);
v_env_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc_ref(v_env_69_);
lean_dec(v___x_68_);
v___x_70_ = 0;
v_env_71_ = l_Lean_Environment_setRecordingDeps(v_env_69_, v___x_70_);
v___x_72_ = lean_st_ref_get(v___y_64_);
v_toCold_73_ = lean_ctor_get(v___y_65_, 0);
v_mctx_74_ = lean_ctor_get(v___x_72_, 0);
lean_inc_ref(v_mctx_74_);
lean_dec(v___x_72_);
v_lctx_75_ = lean_ctor_get(v___y_63_, 2);
v_options_76_ = lean_ctor_get(v_toCold_73_, 2);
lean_inc_ref(v_options_76_);
lean_inc_ref(v_lctx_75_);
v___x_77_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_77_, 0, v_env_71_);
lean_ctor_set(v___x_77_, 1, v_mctx_74_);
lean_ctor_set(v___x_77_, 2, v_lctx_75_);
lean_ctor_set(v___x_77_, 3, v_options_76_);
v___x_78_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
lean_ctor_set(v___x_78_, 1, v_msgData_62_);
v___x_79_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__1_spec__4___boxed(lean_object* v_msgData_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__1_spec__4(v_msgData_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__1___redArg(lean_object* v_msg_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v_ref_93_; lean_object* v___x_94_; lean_object* v_a_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_103_; 
v_ref_93_ = lean_ctor_get(v___y_90_, 2);
v___x_94_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__1_spec__4(v_msg_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
v_a_95_ = lean_ctor_get(v___x_94_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_103_ == 0)
{
v___x_97_ = v___x_94_;
v_isShared_98_ = v_isSharedCheck_103_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_a_95_);
lean_dec(v___x_94_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_103_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_99_; lean_object* v___x_101_; 
lean_inc(v_ref_93_);
v___x_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_99_, 0, v_ref_93_);
lean_ctor_set(v___x_99_, 1, v_a_95_);
if (v_isShared_98_ == 0)
{
lean_ctor_set_tag(v___x_97_, 1);
lean_ctor_set(v___x_97_, 0, v___x_99_);
v___x_101_ = v___x_97_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_99_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__1___redArg___boxed(lean_object* v_msg_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__1___redArg(v_msg_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__6___redArg___lam__0(lean_object* v_k_111_, lean_object* v___y_112_, lean_object* v_b_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v___x_119_; 
lean_inc(v___y_117_);
lean_inc_ref(v___y_116_);
lean_inc(v___y_115_);
lean_inc_ref(v___y_114_);
lean_inc(v___y_112_);
v___x_119_ = lean_apply_7(v_k_111_, v_b_113_, v___y_112_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, lean_box(0));
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__6___redArg___lam__0___boxed(lean_object* v_k_120_, lean_object* v___y_121_, lean_object* v_b_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__6___redArg___lam__0(v_k_120_, v___y_121_, v_b_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
lean_dec(v___y_121_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__7___redArg(lean_object* v_name_129_, lean_object* v_type_130_, lean_object* v_val_131_, lean_object* v_k_132_, uint8_t v_nondep_133_, uint8_t v_kind_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v___f_141_; lean_object* v___x_142_; 
lean_inc(v___y_135_);
v___f_141_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_141_, 0, v_k_132_);
lean_closure_set(v___f_141_, 1, v___y_135_);
v___x_142_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_129_, v_type_130_, v_val_131_, v___f_141_, v_nondep_133_, v_kind_134_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
if (lean_obj_tag(v___x_142_) == 0)
{
return v___x_142_;
}
else
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
v_a_143_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_150_ == 0)
{
v___x_145_ = v___x_142_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v___x_142_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_a_143_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__7___redArg___boxed(lean_object* v_name_151_, lean_object* v_type_152_, lean_object* v_val_153_, lean_object* v_k_154_, lean_object* v_nondep_155_, lean_object* v_kind_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
uint8_t v_nondep_boxed_163_; uint8_t v_kind_boxed_164_; lean_object* v_res_165_; 
v_nondep_boxed_163_ = lean_unbox(v_nondep_155_);
v_kind_boxed_164_ = lean_unbox(v_kind_156_);
v_res_165_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__7___redArg(v_name_151_, v_type_152_, v_val_153_, v_k_154_, v_nondep_boxed_163_, v_kind_boxed_164_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec(v___y_157_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__6___redArg(lean_object* v_name_166_, uint8_t v_bi_167_, lean_object* v_type_168_, lean_object* v_k_169_, uint8_t v_kind_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v___f_177_; lean_object* v___x_178_; 
lean_inc(v___y_171_);
v___f_177_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_177_, 0, v_k_169_);
lean_closure_set(v___f_177_, 1, v___y_171_);
v___x_178_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_166_, v_bi_167_, v_type_168_, v___f_177_, v_kind_170_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
if (lean_obj_tag(v___x_178_) == 0)
{
return v___x_178_;
}
else
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___x_178_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_178_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__6___redArg___boxed(lean_object* v_name_187_, lean_object* v_bi_188_, lean_object* v_type_189_, lean_object* v_k_190_, lean_object* v_kind_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
uint8_t v_bi_boxed_198_; uint8_t v_kind_boxed_199_; lean_object* v_res_200_; 
v_bi_boxed_198_ = lean_unbox(v_bi_188_);
v_kind_boxed_199_ = lean_unbox(v_kind_191_);
v_res_200_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__6___redArg(v_name_187_, v_bi_boxed_198_, v_type_189_, v_k_190_, v_kind_boxed_199_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__2___redArg(lean_object* v_a_201_, lean_object* v_b_202_, lean_object* v_x_203_){
_start:
{
if (lean_obj_tag(v_x_203_) == 0)
{
lean_dec(v_b_202_);
lean_dec_ref(v_a_201_);
return v_x_203_;
}
else
{
lean_object* v_key_204_; lean_object* v_value_205_; lean_object* v_tail_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_218_; 
v_key_204_ = lean_ctor_get(v_x_203_, 0);
v_value_205_ = lean_ctor_get(v_x_203_, 1);
v_tail_206_ = lean_ctor_get(v_x_203_, 2);
v_isSharedCheck_218_ = !lean_is_exclusive(v_x_203_);
if (v_isSharedCheck_218_ == 0)
{
v___x_208_ = v_x_203_;
v_isShared_209_ = v_isSharedCheck_218_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_tail_206_);
lean_inc(v_value_205_);
lean_inc(v_key_204_);
lean_dec(v_x_203_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_218_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
uint8_t v___x_210_; 
v___x_210_ = l_Lean_ExprStructEq_beq(v_key_204_, v_a_201_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_211_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__2___redArg(v_a_201_, v_b_202_, v_tail_206_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 2, v___x_211_);
v___x_213_ = v___x_208_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_key_204_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_value_205_);
lean_ctor_set(v_reuseFailAlloc_214_, 2, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
else
{
lean_object* v___x_216_; 
lean_dec(v_value_205_);
lean_dec(v_key_204_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 1, v_b_202_);
lean_ctor_set(v___x_208_, 0, v_a_201_);
v___x_216_ = v___x_208_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_a_201_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_b_202_);
lean_ctor_set(v_reuseFailAlloc_217_, 2, v_tail_206_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__1_spec__5_spec__11___redArg(lean_object* v_x_219_, lean_object* v_x_220_){
_start:
{
if (lean_obj_tag(v_x_220_) == 0)
{
return v_x_219_;
}
else
{
lean_object* v_key_221_; lean_object* v_value_222_; lean_object* v_tail_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_246_; 
v_key_221_ = lean_ctor_get(v_x_220_, 0);
v_value_222_ = lean_ctor_get(v_x_220_, 1);
v_tail_223_ = lean_ctor_get(v_x_220_, 2);
v_isSharedCheck_246_ = !lean_is_exclusive(v_x_220_);
if (v_isSharedCheck_246_ == 0)
{
v___x_225_ = v_x_220_;
v_isShared_226_ = v_isSharedCheck_246_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_tail_223_);
lean_inc(v_value_222_);
lean_inc(v_key_221_);
lean_dec(v_x_220_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_246_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; uint64_t v___x_228_; uint64_t v___x_229_; uint64_t v___x_230_; uint64_t v_fold_231_; uint64_t v___x_232_; uint64_t v___x_233_; uint64_t v___x_234_; size_t v___x_235_; size_t v___x_236_; size_t v___x_237_; size_t v___x_238_; size_t v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_227_ = lean_array_get_size(v_x_219_);
v___x_228_ = l_Lean_ExprStructEq_hash(v_key_221_);
v___x_229_ = 32ULL;
v___x_230_ = lean_uint64_shift_right(v___x_228_, v___x_229_);
v_fold_231_ = lean_uint64_xor(v___x_228_, v___x_230_);
v___x_232_ = 16ULL;
v___x_233_ = lean_uint64_shift_right(v_fold_231_, v___x_232_);
v___x_234_ = lean_uint64_xor(v_fold_231_, v___x_233_);
v___x_235_ = lean_uint64_to_usize(v___x_234_);
v___x_236_ = lean_usize_of_nat(v___x_227_);
v___x_237_ = ((size_t)1ULL);
v___x_238_ = lean_usize_sub(v___x_236_, v___x_237_);
v___x_239_ = lean_usize_land(v___x_235_, v___x_238_);
v___x_240_ = lean_array_uget_borrowed(v_x_219_, v___x_239_);
lean_inc(v___x_240_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 2, v___x_240_);
v___x_242_ = v___x_225_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_key_221_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v_value_222_);
lean_ctor_set(v_reuseFailAlloc_245_, 2, v___x_240_);
v___x_242_ = v_reuseFailAlloc_245_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_243_; 
v___x_243_ = lean_array_uset(v_x_219_, v___x_239_, v___x_242_);
v_x_219_ = v___x_243_;
v_x_220_ = v_tail_223_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__1_spec__5___redArg(lean_object* v_i_247_, lean_object* v_source_248_, lean_object* v_target_249_){
_start:
{
lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_250_ = lean_array_get_size(v_source_248_);
v___x_251_ = lean_nat_dec_lt(v_i_247_, v___x_250_);
if (v___x_251_ == 0)
{
lean_dec_ref(v_source_248_);
lean_dec(v_i_247_);
return v_target_249_;
}
else
{
lean_object* v_es_252_; lean_object* v___x_253_; lean_object* v_source_254_; lean_object* v_target_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v_es_252_ = lean_array_fget(v_source_248_, v_i_247_);
v___x_253_ = lean_box(0);
v_source_254_ = lean_array_fset(v_source_248_, v_i_247_, v___x_253_);
v_target_255_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__1_spec__5_spec__11___redArg(v_target_249_, v_es_252_);
v___x_256_ = lean_unsigned_to_nat(1u);
v___x_257_ = lean_nat_add(v_i_247_, v___x_256_);
lean_dec(v_i_247_);
v_i_247_ = v___x_257_;
v_source_248_ = v_source_254_;
v_target_249_ = v_target_255_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__1___redArg(lean_object* v_data_259_){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v_nbuckets_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_260_ = lean_array_get_size(v_data_259_);
v___x_261_ = lean_unsigned_to_nat(2u);
v_nbuckets_262_ = lean_nat_mul(v___x_260_, v___x_261_);
v___x_263_ = lean_unsigned_to_nat(0u);
v___x_264_ = lean_box(0);
v___x_265_ = lean_mk_array(v_nbuckets_262_, v___x_264_);
v___x_266_ = lean_array_propagate_mark(v_data_259_, v___x_265_);
v___x_267_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__1_spec__5___redArg(v___x_263_, v_data_259_, v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__0___redArg(lean_object* v_a_268_, lean_object* v_x_269_){
_start:
{
if (lean_obj_tag(v_x_269_) == 0)
{
uint8_t v___x_270_; 
v___x_270_ = 0;
return v___x_270_;
}
else
{
lean_object* v_key_271_; lean_object* v_tail_272_; uint8_t v___x_273_; 
v_key_271_ = lean_ctor_get(v_x_269_, 0);
v_tail_272_ = lean_ctor_get(v_x_269_, 2);
v___x_273_ = l_Lean_ExprStructEq_beq(v_key_271_, v_a_268_);
if (v___x_273_ == 0)
{
v_x_269_ = v_tail_272_;
goto _start;
}
else
{
return v___x_273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__0___redArg___boxed(lean_object* v_a_275_, lean_object* v_x_276_){
_start:
{
uint8_t v_res_277_; lean_object* v_r_278_; 
v_res_277_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__0___redArg(v_a_275_, v_x_276_);
lean_dec(v_x_276_);
lean_dec_ref(v_a_275_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0___redArg(lean_object* v_m_279_, lean_object* v_a_280_, lean_object* v_b_281_){
_start:
{
lean_object* v_size_282_; lean_object* v_buckets_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_326_; 
v_size_282_ = lean_ctor_get(v_m_279_, 0);
v_buckets_283_ = lean_ctor_get(v_m_279_, 1);
v_isSharedCheck_326_ = !lean_is_exclusive(v_m_279_);
if (v_isSharedCheck_326_ == 0)
{
v___x_285_ = v_m_279_;
v_isShared_286_ = v_isSharedCheck_326_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_buckets_283_);
lean_inc(v_size_282_);
lean_dec(v_m_279_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_326_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_287_; uint64_t v___x_288_; uint64_t v___x_289_; uint64_t v___x_290_; uint64_t v_fold_291_; uint64_t v___x_292_; uint64_t v___x_293_; uint64_t v___x_294_; size_t v___x_295_; size_t v___x_296_; size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; lean_object* v_bkt_300_; uint8_t v___x_301_; 
v___x_287_ = lean_array_get_size(v_buckets_283_);
v___x_288_ = l_Lean_ExprStructEq_hash(v_a_280_);
v___x_289_ = 32ULL;
v___x_290_ = lean_uint64_shift_right(v___x_288_, v___x_289_);
v_fold_291_ = lean_uint64_xor(v___x_288_, v___x_290_);
v___x_292_ = 16ULL;
v___x_293_ = lean_uint64_shift_right(v_fold_291_, v___x_292_);
v___x_294_ = lean_uint64_xor(v_fold_291_, v___x_293_);
v___x_295_ = lean_uint64_to_usize(v___x_294_);
v___x_296_ = lean_usize_of_nat(v___x_287_);
v___x_297_ = ((size_t)1ULL);
v___x_298_ = lean_usize_sub(v___x_296_, v___x_297_);
v___x_299_ = lean_usize_land(v___x_295_, v___x_298_);
v_bkt_300_ = lean_array_uget_borrowed(v_buckets_283_, v___x_299_);
v___x_301_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__0___redArg(v_a_280_, v_bkt_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v_size_x27_303_; lean_object* v___x_304_; lean_object* v_buckets_x27_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_302_ = lean_unsigned_to_nat(1u);
v_size_x27_303_ = lean_nat_add(v_size_282_, v___x_302_);
lean_dec(v_size_282_);
lean_inc(v_bkt_300_);
v___x_304_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_304_, 0, v_a_280_);
lean_ctor_set(v___x_304_, 1, v_b_281_);
lean_ctor_set(v___x_304_, 2, v_bkt_300_);
v_buckets_x27_305_ = lean_array_uset(v_buckets_283_, v___x_299_, v___x_304_);
v___x_306_ = lean_unsigned_to_nat(4u);
v___x_307_ = lean_nat_mul(v_size_x27_303_, v___x_306_);
v___x_308_ = lean_unsigned_to_nat(3u);
v___x_309_ = lean_nat_div(v___x_307_, v___x_308_);
lean_dec(v___x_307_);
v___x_310_ = lean_array_get_size(v_buckets_x27_305_);
v___x_311_ = lean_nat_dec_le(v___x_309_, v___x_310_);
lean_dec(v___x_309_);
if (v___x_311_ == 0)
{
lean_object* v_val_312_; lean_object* v___x_314_; 
v_val_312_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__1___redArg(v_buckets_x27_305_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 1, v_val_312_);
lean_ctor_set(v___x_285_, 0, v_size_x27_303_);
v___x_314_ = v___x_285_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_size_x27_303_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_val_312_);
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
lean_object* v___x_317_; 
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 1, v_buckets_x27_305_);
lean_ctor_set(v___x_285_, 0, v_size_x27_303_);
v___x_317_ = v___x_285_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_size_x27_303_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_buckets_x27_305_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
else
{
lean_object* v___x_319_; lean_object* v_buckets_x27_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_324_; 
lean_inc(v_bkt_300_);
v___x_319_ = lean_box(0);
v_buckets_x27_320_ = lean_array_uset(v_buckets_283_, v___x_299_, v___x_319_);
v___x_321_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__2___redArg(v_a_280_, v_b_281_, v_bkt_300_);
v___x_322_ = lean_array_uset(v_buckets_x27_320_, v___x_299_, v___x_321_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 1, v___x_322_);
v___x_324_ = v___x_285_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_size_282_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v___x_322_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___lam__0(lean_object* v_xs_327_, uint8_t v_isType_328_, lean_object* v_e_329_, lean_object* v_a_330_, lean_object* v_b_331_, lean_object* v_x_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = lean_array_push(v_xs_327_, v_x_332_);
if (v_isType_328_ == 0)
{
uint8_t v___x_340_; lean_object* v___x_341_; 
v___x_340_ = l_Lean_Expr_isForall(v_e_329_);
v___x_341_ = l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders(v_a_330_, v___x_339_, v___x_340_, v_b_331_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
return v___x_341_;
}
else
{
lean_object* v___x_342_; 
v___x_342_ = l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders(v_a_330_, v___x_339_, v_isType_328_, v_b_331_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
return v___x_342_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___lam__0___boxed(lean_object* v_xs_343_, lean_object* v_isType_344_, lean_object* v_e_345_, lean_object* v_a_346_, lean_object* v_b_347_, lean_object* v_x_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
uint8_t v_isType_boxed_355_; lean_object* v_res_356_; 
v_isType_boxed_355_ = lean_unbox(v_isType_344_);
v_res_356_ = l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___lam__0(v_xs_343_, v_isType_boxed_355_, v_e_345_, v_a_346_, v_b_347_, v_x_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
lean_dec(v___y_349_);
lean_dec_ref(v_e_345_);
return v_res_356_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___closed__1(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___closed__0));
v___x_359_ = l_Lean_stringToMessageData(v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___lam__1___boxed(lean_object* v_xs_360_, lean_object* v_a_361_, lean_object* v_isType_362_, lean_object* v_body_363_, lean_object* v_x_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
uint8_t v_isType_boxed_371_; lean_object* v_res_372_; 
v_isType_boxed_371_ = lean_unbox(v_isType_362_);
v_res_372_ = l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___lam__1(v_xs_360_, v_a_361_, v_isType_boxed_371_, v_body_363_, v_x_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v___y_365_);
return v_res_372_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit___closed__1(void){
_start:
{
lean_object* v___x_375_; lean_object* v_dummy_376_; 
v___x_375_ = lean_box(0);
v_dummy_376_ = l_Lean_Expr_sort___override(v___x_375_);
return v_dummy_376_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___closed__1(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___closed__0));
v___x_379_ = l_Lean_stringToMessageData(v___x_378_);
return v___x_379_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___closed__3(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___closed__2));
v___x_382_ = l_Lean_stringToMessageData(v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2(lean_object* v_a_383_, uint8_t v___x_384_, lean_object* v_a_385_, lean_object* v_as_386_, size_t v_sz_387_, size_t v_i_388_, lean_object* v_b_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v___y_397_; uint8_t v___x_419_; 
v___x_419_ = lean_usize_dec_lt(v_i_388_, v_sz_387_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; 
lean_dec_ref(v_a_385_);
lean_dec_ref(v_a_383_);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v_b_389_);
return v___x_420_;
}
else
{
lean_object* v_snd_421_; lean_object* v_fst_422_; lean_object* v_fst_423_; lean_object* v_snd_424_; lean_object* v_a_425_; lean_object* v___x_426_; 
v_snd_421_ = lean_ctor_get(v_b_389_, 1);
lean_inc(v_snd_421_);
v_fst_422_ = lean_ctor_get(v_b_389_, 0);
lean_inc(v_fst_422_);
lean_dec_ref(v_b_389_);
v_fst_423_ = lean_ctor_get(v_snd_421_, 0);
lean_inc(v_fst_423_);
v_snd_424_ = lean_ctor_get(v_snd_421_, 1);
lean_inc(v_snd_424_);
lean_dec(v_snd_421_);
v_a_425_ = lean_array_uget_borrowed(v_as_386_, v_i_388_);
lean_inc(v_a_425_);
lean_inc_ref(v_a_383_);
v___x_426_ = l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit(v_a_383_, v_a_425_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v_fType_x3f_440_; lean_object* v_j_441_; lean_object* v___y_442_; lean_object* v___y_443_; lean_object* v___y_444_; lean_object* v___y_445_; lean_object* v___y_446_; lean_object* v___x_449_; lean_object* v___y_451_; lean_object* v_j_452_; lean_object* v_fType_453_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v_fType_x3f_506_; lean_object* v_val_507_; lean_object* v_j_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_a_427_);
lean_dec_ref_known(v___x_426_, 1);
v___x_449_ = lean_array_get_size(v_fst_422_);
if (lean_obj_tag(v_fst_423_) == 0)
{
if (v___x_384_ == 0)
{
v_fType_x3f_440_ = v_fst_423_;
v_j_441_ = v_snd_424_;
v___y_442_ = v___y_390_;
v___y_443_ = v___y_391_;
v___y_444_ = v___y_392_;
v___y_445_ = v___y_393_;
v___y_446_ = v___y_394_;
goto v___jp_439_;
}
else
{
uint8_t v___x_526_; 
v___x_526_ = l_Lean_Expr_hasLooseBVars(v_a_425_);
if (v___x_526_ == 0)
{
v_fType_x3f_440_ = v_fst_423_;
v_j_441_ = v_snd_424_;
v___y_442_ = v___y_390_;
v___y_443_ = v___y_391_;
v___y_444_ = v___y_392_;
v___y_445_ = v___y_393_;
v___y_446_ = v___y_394_;
goto v___jp_439_;
}
else
{
lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec(v_snd_424_);
lean_inc_ref(v_a_385_);
v___x_527_ = l_Lean_mkAppN(v_a_385_, v_fst_422_);
lean_inc(v___y_394_);
lean_inc_ref(v___y_393_);
lean_inc(v___y_392_);
lean_inc_ref(v___y_391_);
v___x_528_ = lean_infer_type(v___x_527_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v___x_530_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc_n(v_a_529_, 2);
lean_dec_ref_known(v___x_528_, 1);
v___x_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_530_, 0, v_a_529_);
v_fType_x3f_506_ = v___x_530_;
v_val_507_ = v_a_529_;
v_j_508_ = v___x_449_;
v___y_509_ = v___y_390_;
v___y_510_ = v___y_391_;
v___y_511_ = v___y_392_;
v___y_512_ = v___y_393_;
v___y_513_ = v___y_394_;
goto v___jp_505_;
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec(v_a_427_);
lean_dec(v_fst_422_);
lean_dec_ref(v_a_385_);
lean_dec_ref(v_a_383_);
v_a_531_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_528_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_528_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
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
}
}
else
{
lean_object* v_val_539_; 
v_val_539_ = lean_ctor_get(v_fst_423_, 0);
lean_inc(v_val_539_);
v_fType_x3f_506_ = v_fst_423_;
v_val_507_ = v_val_539_;
v_j_508_ = v_snd_424_;
v___y_509_ = v___y_390_;
v___y_510_ = v___y_391_;
v___y_511_ = v___y_392_;
v___y_512_ = v___y_393_;
v___y_513_ = v___y_394_;
goto v___jp_505_;
}
v___jp_428_:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_436_, 0, v___y_429_);
v___x_437_ = lean_box(0);
v___x_438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___lam__0(v_fst_422_, v_a_427_, v___x_437_, v___x_436_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
v___y_397_ = v___x_438_;
goto v___jp_396_;
}
v___jp_439_:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = lean_box(0);
v___x_448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___lam__0(v_fst_422_, v_a_427_, v___x_447_, v_fType_x3f_440_, v_j_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
v___y_397_ = v___x_448_;
goto v___jp_396_;
}
v___jp_450_:
{
if (lean_obj_tag(v_fType_453_) == 7)
{
lean_object* v_binderType_459_; lean_object* v_body_460_; lean_object* v___x_461_; 
lean_dec(v___y_451_);
v_binderType_459_ = lean_ctor_get(v_fType_453_, 1);
lean_inc_ref(v_binderType_459_);
v_body_460_ = lean_ctor_get(v_fType_453_, 2);
lean_inc_ref(v_body_460_);
lean_dec_ref_known(v_fType_453_, 3);
lean_inc(v___y_458_);
lean_inc_ref(v___y_457_);
lean_inc(v___y_456_);
lean_inc_ref(v___y_455_);
lean_inc(v_a_427_);
v___x_461_ = lean_infer_type(v_a_427_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_a_462_);
lean_dec_ref_known(v___x_461_, 1);
v___x_463_ = lean_expr_instantiate_rev_range(v_binderType_459_, v_j_452_, v___x_449_, v_fst_422_);
lean_dec_ref(v_binderType_459_);
v___x_464_ = l_Lean_Meta_isExprDefEq(v___x_463_, v_a_462_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; uint8_t v___x_466_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_465_);
lean_dec_ref_known(v___x_464_, 1);
v___x_466_ = lean_unbox(v_a_465_);
lean_dec(v_a_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___closed__1);
v___x_468_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__1___redArg(v___x_467_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_dec_ref_known(v___x_468_, 1);
v___y_429_ = v_body_460_;
v___y_430_ = v_j_452_;
v___y_431_ = v___y_454_;
v___y_432_ = v___y_455_;
v___y_433_ = v___y_456_;
v___y_434_ = v___y_457_;
v___y_435_ = v___y_458_;
goto v___jp_428_;
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
lean_dec_ref(v_body_460_);
lean_dec(v_j_452_);
lean_dec(v_a_427_);
lean_dec(v_fst_422_);
lean_dec_ref(v_a_385_);
lean_dec_ref(v_a_383_);
v_a_469_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_468_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_468_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
else
{
v___y_429_ = v_body_460_;
v___y_430_ = v_j_452_;
v___y_431_ = v___y_454_;
v___y_432_ = v___y_455_;
v___y_433_ = v___y_456_;
v___y_434_ = v___y_457_;
v___y_435_ = v___y_458_;
goto v___jp_428_;
}
}
else
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
lean_dec_ref(v_body_460_);
lean_dec(v_j_452_);
lean_dec(v_a_427_);
lean_dec(v_fst_422_);
lean_dec_ref(v_a_385_);
lean_dec_ref(v_a_383_);
v_a_477_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_484_ == 0)
{
v___x_479_ = v___x_464_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_464_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_477_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
lean_dec_ref(v_body_460_);
lean_dec_ref(v_binderType_459_);
lean_dec(v_j_452_);
lean_dec(v_a_427_);
lean_dec(v_fst_422_);
lean_dec_ref(v_a_385_);
lean_dec_ref(v_a_383_);
v_a_485_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_461_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_461_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
else
{
lean_object* v___x_493_; lean_object* v___x_494_; 
lean_dec_ref(v_fType_453_);
v___x_493_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___closed__3);
v___x_494_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__1___redArg(v___x_493_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v_a_495_; lean_object* v___x_496_; 
v_a_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_a_495_);
lean_dec_ref_known(v___x_494_, 1);
v___x_496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___lam__0(v_fst_422_, v_a_427_, v_a_495_, v___y_451_, v_j_452_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
v___y_397_ = v___x_496_;
goto v___jp_396_;
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_dec(v_j_452_);
lean_dec(v___y_451_);
lean_dec(v_a_427_);
lean_dec(v_fst_422_);
lean_dec_ref(v_a_385_);
lean_dec_ref(v_a_383_);
v_a_497_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_494_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_494_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
v___jp_505_:
{
uint8_t v___x_514_; 
v___x_514_ = l_Lean_Expr_isForall(v_val_507_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_expr_instantiate_rev_range(v_val_507_, v_j_508_, v___x_449_, v_fst_422_);
lean_dec(v_j_508_);
lean_dec_ref(v_val_507_);
lean_inc(v___y_513_);
lean_inc_ref(v___y_512_);
lean_inc(v___y_511_);
lean_inc_ref(v___y_510_);
v___x_516_ = lean_whnf(v___x_515_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; 
v_a_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_a_517_);
lean_dec_ref_known(v___x_516_, 1);
v___y_451_ = v_fType_x3f_506_;
v_j_452_ = v___x_449_;
v_fType_453_ = v_a_517_;
v___y_454_ = v___y_509_;
v___y_455_ = v___y_510_;
v___y_456_ = v___y_511_;
v___y_457_ = v___y_512_;
v___y_458_ = v___y_513_;
goto v___jp_450_;
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec(v_fType_x3f_506_);
lean_dec(v_a_427_);
lean_dec(v_fst_422_);
lean_dec_ref(v_a_385_);
lean_dec_ref(v_a_383_);
v_a_518_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_516_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_516_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
else
{
v___y_451_ = v_fType_x3f_506_;
v_j_452_ = v_j_508_;
v_fType_453_ = v_val_507_;
v___y_454_ = v___y_509_;
v___y_455_ = v___y_510_;
v___y_456_ = v___y_511_;
v___y_457_ = v___y_512_;
v___y_458_ = v___y_513_;
goto v___jp_450_;
}
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_dec(v_snd_424_);
lean_dec(v_fst_423_);
lean_dec(v_fst_422_);
lean_dec_ref(v_a_385_);
lean_dec_ref(v_a_383_);
v_a_540_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_426_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_426_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
v___jp_396_:
{
if (lean_obj_tag(v___y_397_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_410_; 
v_a_398_ = lean_ctor_get(v___y_397_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___y_397_);
if (v_isSharedCheck_410_ == 0)
{
v___x_400_ = v___y_397_;
v_isShared_401_ = v_isSharedCheck_410_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___y_397_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_410_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
if (lean_obj_tag(v_a_398_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_404_; 
lean_dec_ref(v_a_385_);
lean_dec_ref(v_a_383_);
v_a_402_ = lean_ctor_get(v_a_398_, 0);
lean_inc(v_a_402_);
lean_dec_ref_known(v_a_398_, 1);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v_a_402_);
v___x_404_ = v___x_400_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
else
{
lean_object* v_a_406_; size_t v___x_407_; size_t v___x_408_; 
lean_del_object(v___x_400_);
v_a_406_ = lean_ctor_get(v_a_398_, 0);
lean_inc(v_a_406_);
lean_dec_ref_known(v_a_398_, 1);
v___x_407_ = ((size_t)1ULL);
v___x_408_ = lean_usize_add(v_i_388_, v___x_407_);
v_i_388_ = v___x_408_;
v_b_389_ = v_a_406_;
goto _start;
}
}
}
else
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
lean_dec_ref(v_a_385_);
lean_dec_ref(v_a_383_);
v_a_411_ = lean_ctor_get(v___y_397_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___y_397_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___y_397_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___y_397_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__4(lean_object* v_a_548_, uint8_t v___x_549_, lean_object* v_x_550_, lean_object* v_x_551_, lean_object* v_x_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
if (lean_obj_tag(v_x_550_) == 5)
{
lean_object* v_fn_559_; lean_object* v_arg_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v_fn_559_ = lean_ctor_get(v_x_550_, 0);
lean_inc_ref(v_fn_559_);
v_arg_560_ = lean_ctor_get(v_x_550_, 1);
lean_inc_ref(v_arg_560_);
lean_dec_ref_known(v_x_550_, 2);
v___x_561_ = lean_array_set(v_x_551_, v_x_552_, v_arg_560_);
v___x_562_ = lean_unsigned_to_nat(1u);
v___x_563_ = lean_nat_sub(v_x_552_, v___x_562_);
lean_dec(v_x_552_);
v_x_550_ = v_fn_559_;
v_x_551_ = v___x_561_;
v_x_552_ = v___x_563_;
goto _start;
}
else
{
lean_object* v___x_565_; 
lean_dec(v_x_552_);
lean_inc_ref(v_x_550_);
lean_inc_ref(v_a_548_);
v___x_565_ = l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit(v_a_548_, v_x_550_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v_fType_x3f_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; uint8_t v___x_600_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_a_566_);
lean_dec_ref_known(v___x_565_, 1);
v___x_567_ = lean_array_get_size(v_x_551_);
v___x_568_ = lean_mk_empty_array_with_capacity(v___x_567_);
v___x_600_ = l_Lean_Expr_hasLooseBVars(v_x_550_);
lean_dec_ref(v_x_550_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; 
v___x_601_ = lean_box(0);
v_fType_x3f_570_ = v___x_601_;
v___y_571_ = v___y_553_;
v___y_572_ = v___y_554_;
v___y_573_ = v___y_555_;
v___y_574_ = v___y_556_;
v___y_575_ = v___y_557_;
goto v___jp_569_;
}
else
{
lean_object* v___x_602_; 
lean_inc(v___y_557_);
lean_inc_ref(v___y_556_);
lean_inc(v___y_555_);
lean_inc_ref(v___y_554_);
lean_inc(v_a_566_);
v___x_602_ = lean_infer_type(v_a_566_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_602_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_602_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
lean_ctor_set_tag(v___x_605_, 1);
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
v_fType_x3f_570_ = v___x_608_;
v___y_571_ = v___y_553_;
v___y_572_ = v___y_554_;
v___y_573_ = v___y_555_;
v___y_574_ = v___y_556_;
v___y_575_ = v___y_557_;
goto v___jp_569_;
}
}
}
else
{
lean_dec_ref(v___x_568_);
lean_dec(v_a_566_);
lean_dec_ref(v_x_551_);
lean_dec_ref(v_a_548_);
return v___x_602_;
}
}
v___jp_569_:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; size_t v_sz_579_; size_t v___x_580_; lean_object* v___x_581_; 
v___x_576_ = lean_unsigned_to_nat(0u);
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v_fType_x3f_570_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_568_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v_sz_579_ = lean_array_size(v_x_551_);
v___x_580_ = ((size_t)0ULL);
lean_inc(v_a_566_);
v___x_581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2(v_a_548_, v___x_549_, v_a_566_, v_x_551_, v_sz_579_, v___x_580_, v___x_578_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
lean_dec_ref(v_x_551_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_591_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_591_ == 0)
{
v___x_584_ = v___x_581_;
v_isShared_585_ = v_isSharedCheck_591_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_591_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v_fst_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
v_fst_586_ = lean_ctor_get(v_a_582_, 0);
lean_inc(v_fst_586_);
lean_dec(v_a_582_);
v___x_587_ = l_Lean_mkAppN(v_a_566_, v_fst_586_);
lean_dec(v_fst_586_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_587_);
v___x_589_ = v___x_584_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_dec(v_a_566_);
v_a_592_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_581_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_581_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
}
else
{
lean_dec_ref(v_x_551_);
lean_dec_ref(v_x_550_);
lean_dec_ref(v_a_548_);
return v___x_565_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit___closed__3(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit___closed__2));
v___x_613_ = l_Lean_stringToMessageData(v___x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit(lean_object* v_a_614_, lean_object* v_e_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_r_623_; lean_object* v___y_624_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; uint8_t v___x_647_; 
v___x_647_ = l_Lean_Expr_hasLooseBVars(v_e_615_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; 
lean_dec_ref(v_a_614_);
v___x_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_648_, 0, v_e_615_);
return v___x_648_;
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_st_ref_get(v_a_616_);
v___x_650_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__3___redArg(v___x_649_, v_e_615_);
lean_dec(v___x_649_);
if (lean_obj_tag(v___x_650_) == 1)
{
lean_object* v_val_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
lean_dec_ref(v_e_615_);
lean_dec_ref(v_a_614_);
v_val_651_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_650_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_val_651_);
lean_dec(v___x_650_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set_tag(v___x_653_, 0);
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_val_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
else
{
lean_dec(v___x_650_);
switch(lean_obj_tag(v_e_615_))
{
case 0:
{
v_r_623_ = v_a_614_;
v___y_624_ = v_a_616_;
goto v___jp_622_;
}
case 5:
{
lean_object* v_dummy_659_; lean_object* v_nargs_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v_dummy_659_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit___closed__1, &l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit___closed__1_once, _init_l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit___closed__1);
v_nargs_660_ = l_Lean_Expr_getAppNumArgs(v_e_615_);
lean_inc(v_nargs_660_);
v___x_661_ = lean_mk_array(v_nargs_660_, v_dummy_659_);
v___x_662_ = lean_unsigned_to_nat(1u);
v___x_663_ = lean_nat_sub(v_nargs_660_, v___x_662_);
lean_dec(v_nargs_660_);
lean_inc_ref(v_e_615_);
v___x_664_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__4(v_a_614_, v___x_647_, v_e_615_, v___x_661_, v___x_663_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
lean_dec_ref_known(v___x_664_, 1);
v_r_623_ = v_a_665_;
v___y_624_ = v_a_616_;
goto v___jp_622_;
}
else
{
lean_dec_ref_known(v_e_615_, 2);
return v___x_664_;
}
}
case 10:
{
lean_object* v_data_666_; lean_object* v_expr_667_; lean_object* v___x_668_; 
v_data_666_ = lean_ctor_get(v_e_615_, 0);
v_expr_667_ = lean_ctor_get(v_e_615_, 1);
lean_inc_ref(v_expr_667_);
v___x_668_ = l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit(v_a_614_, v_expr_667_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_670_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_668_, 1);
lean_inc(v_data_666_);
v___x_670_ = l_Lean_Expr_mdata___override(v_data_666_, v_a_669_);
v_r_623_ = v___x_670_;
v___y_624_ = v_a_616_;
goto v___jp_622_;
}
else
{
lean_dec_ref_known(v_e_615_, 2);
return v___x_668_;
}
}
case 11:
{
lean_object* v_typeName_671_; lean_object* v_idx_672_; lean_object* v_struct_673_; lean_object* v___x_674_; 
v_typeName_671_ = lean_ctor_get(v_e_615_, 0);
v_idx_672_ = lean_ctor_get(v_e_615_, 1);
v_struct_673_ = lean_ctor_get(v_e_615_, 2);
lean_inc_ref(v_struct_673_);
v___x_674_ = l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit(v_a_614_, v_struct_673_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_676_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc_n(v_a_675_, 2);
lean_dec_ref_known(v___x_674_, 1);
lean_inc(v_idx_672_);
lean_inc(v_typeName_671_);
v___x_676_ = l_Lean_Meta_checkProj(v_typeName_671_, v_idx_672_, v_a_675_, v_a_617_, v_a_618_, v_a_619_, v_a_620_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v___x_677_; 
lean_dec_ref_known(v___x_676_, 1);
lean_inc(v_idx_672_);
lean_inc(v_typeName_671_);
v___x_677_ = l_Lean_Expr_proj___override(v_typeName_671_, v_idx_672_, v_a_675_);
v_r_623_ = v___x_677_;
v___y_624_ = v_a_616_;
goto v___jp_622_;
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
lean_dec(v_a_675_);
lean_dec_ref_known(v_e_615_, 3);
v_a_678_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_676_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_676_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_678_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_615_, 3);
return v___x_674_;
}
}
case 6:
{
v___y_630_ = v_a_616_;
v___y_631_ = v_a_617_;
v___y_632_ = v_a_618_;
v___y_633_ = v_a_619_;
v___y_634_ = v_a_620_;
goto v___jp_629_;
}
case 7:
{
v___y_630_ = v_a_616_;
v___y_631_ = v_a_617_;
v___y_632_ = v_a_618_;
v___y_633_ = v_a_619_;
v___y_634_ = v_a_620_;
goto v___jp_629_;
}
case 8:
{
lean_object* v___x_686_; uint8_t v___x_687_; lean_object* v___x_688_; 
v___x_686_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit___closed__0));
v___x_687_ = 0;
lean_inc_ref(v_e_615_);
lean_inc_ref(v_a_614_);
v___x_688_ = l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders(v_a_614_, v___x_686_, v___x_687_, v_e_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v___x_689_; 
lean_dec_ref_known(v___x_688_, 1);
v___x_689_ = lean_expr_instantiate1(v_e_615_, v_a_614_);
lean_dec_ref(v_a_614_);
v_r_623_ = v___x_689_;
v___y_624_ = v_a_616_;
goto v___jp_622_;
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_dec_ref_known(v_e_615_, 4);
lean_dec_ref(v_a_614_);
v_a_690_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_688_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_688_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
default: 
{
lean_object* v___x_698_; lean_object* v___x_699_; 
lean_dec_ref(v_a_614_);
v___x_698_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit___closed__3, &l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit___closed__3_once, _init_l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit___closed__3);
v___x_699_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__1___redArg(v___x_698_, v_a_617_, v_a_618_, v_a_619_, v_a_620_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_700_);
lean_dec_ref_known(v___x_699_, 1);
v_r_623_ = v_a_700_;
v___y_624_ = v_a_616_;
goto v___jp_622_;
}
else
{
lean_dec_ref(v_e_615_);
return v___x_699_;
}
}
}
}
}
v___jp_622_:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_625_ = lean_st_ref_take(v___y_624_);
lean_inc_ref(v_r_623_);
v___x_626_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0___redArg(v___x_625_, v_e_615_, v_r_623_);
v___x_627_ = lean_st_ref_put(v___y_624_, v___x_626_);
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v_r_623_);
return v___x_628_;
}
v___jp_629_:
{
lean_object* v___x_635_; uint8_t v___x_636_; lean_object* v___x_637_; 
v___x_635_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit___closed__0));
v___x_636_ = 0;
lean_inc_ref(v_e_615_);
lean_inc_ref(v_a_614_);
v___x_637_ = l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders(v_a_614_, v___x_635_, v___x_636_, v_e_615_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v___x_638_; 
lean_dec_ref_known(v___x_637_, 1);
v___x_638_ = lean_expr_instantiate1(v_e_615_, v_a_614_);
lean_dec_ref(v_a_614_);
v_r_623_ = v___x_638_;
v___y_624_ = v___y_630_;
goto v___jp_622_;
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec_ref(v_e_615_);
lean_dec_ref(v_a_614_);
v_a_639_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_637_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_637_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
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
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___closed__3(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___closed__2));
v___x_703_ = l_Lean_stringToMessageData(v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders(lean_object* v_a_704_, lean_object* v_xs_705_, uint8_t v_isType_706_, lean_object* v_e_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
lean_object* v___y_715_; uint8_t v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v_n_727_; lean_object* v_d_728_; lean_object* v_b_729_; uint8_t v_bi_730_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; 
switch(lean_obj_tag(v_e_707_))
{
case 6:
{
lean_object* v_binderName_742_; lean_object* v_binderType_743_; lean_object* v_body_744_; uint8_t v_binderInfo_745_; 
v_binderName_742_ = lean_ctor_get(v_e_707_, 0);
v_binderType_743_ = lean_ctor_get(v_e_707_, 1);
v_body_744_ = lean_ctor_get(v_e_707_, 2);
v_binderInfo_745_ = lean_ctor_get_uint8(v_e_707_, sizeof(void*)*3 + 8);
lean_inc_ref(v_body_744_);
lean_inc_ref(v_binderType_743_);
lean_inc(v_binderName_742_);
v_n_727_ = v_binderName_742_;
v_d_728_ = v_binderType_743_;
v_b_729_ = v_body_744_;
v_bi_730_ = v_binderInfo_745_;
v___y_731_ = v_a_708_;
v___y_732_ = v_a_709_;
v___y_733_ = v_a_710_;
v___y_734_ = v_a_711_;
v___y_735_ = v_a_712_;
goto v___jp_726_;
}
case 7:
{
lean_object* v_binderName_746_; lean_object* v_binderType_747_; lean_object* v_body_748_; uint8_t v_binderInfo_749_; 
v_binderName_746_ = lean_ctor_get(v_e_707_, 0);
v_binderType_747_ = lean_ctor_get(v_e_707_, 1);
v_body_748_ = lean_ctor_get(v_e_707_, 2);
v_binderInfo_749_ = lean_ctor_get_uint8(v_e_707_, sizeof(void*)*3 + 8);
lean_inc_ref(v_body_748_);
lean_inc_ref(v_binderType_747_);
lean_inc(v_binderName_746_);
v_n_727_ = v_binderName_746_;
v_d_728_ = v_binderType_747_;
v_b_729_ = v_body_748_;
v_bi_730_ = v_binderInfo_749_;
v___y_731_ = v_a_708_;
v___y_732_ = v_a_709_;
v___y_733_ = v_a_710_;
v___y_734_ = v_a_711_;
v___y_735_ = v_a_712_;
goto v___jp_726_;
}
case 8:
{
lean_object* v_declName_750_; lean_object* v_type_751_; lean_object* v_value_752_; lean_object* v_body_753_; uint8_t v_nondep_754_; lean_object* v___x_755_; lean_object* v___f_756_; lean_object* v_t_757_; lean_object* v_v_758_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; uint8_t v___x_770_; 
v_declName_750_ = lean_ctor_get(v_e_707_, 0);
lean_inc(v_declName_750_);
v_type_751_ = lean_ctor_get(v_e_707_, 1);
lean_inc_ref(v_type_751_);
v_value_752_ = lean_ctor_get(v_e_707_, 2);
lean_inc_ref(v_value_752_);
v_body_753_ = lean_ctor_get(v_e_707_, 3);
lean_inc_ref(v_body_753_);
v_nondep_754_ = lean_ctor_get_uint8(v_e_707_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_707_, 4);
v___x_755_ = lean_box(v_isType_706_);
lean_inc_ref(v_xs_705_);
v___f_756_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___lam__1___boxed), 11, 4);
lean_closure_set(v___f_756_, 0, v_xs_705_);
lean_closure_set(v___f_756_, 1, v_a_704_);
lean_closure_set(v___f_756_, 2, v___x_755_);
lean_closure_set(v___f_756_, 3, v_body_753_);
v_t_757_ = lean_expr_instantiate_rev(v_type_751_, v_xs_705_);
lean_dec_ref(v_type_751_);
v_v_758_ = lean_expr_instantiate_rev(v_value_752_, v_xs_705_);
lean_dec_ref(v_xs_705_);
lean_dec_ref(v_value_752_);
v___x_770_ = l_Lean_Expr_hasLooseBVars(v_t_757_);
if (v___x_770_ == 0)
{
uint8_t v___x_771_; 
v___x_771_ = l_Lean_Expr_hasLooseBVars(v_v_758_);
if (v___x_771_ == 0)
{
v___y_760_ = v_a_708_;
v___y_761_ = v_a_709_;
v___y_762_ = v_a_710_;
v___y_763_ = v_a_711_;
v___y_764_ = v_a_712_;
goto v___jp_759_;
}
else
{
goto v___jp_767_;
}
}
else
{
goto v___jp_767_;
}
v___jp_759_:
{
uint8_t v___x_765_; lean_object* v___x_766_; 
v___x_765_ = 0;
v___x_766_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__7___redArg(v_declName_750_, v_t_757_, v_v_758_, v___f_756_, v_nondep_754_, v___x_765_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
return v___x_766_;
}
v___jp_767_:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___closed__1, &l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___closed__1_once, _init_l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___closed__1);
v___x_769_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__1___redArg(v___x_768_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_dec_ref_known(v___x_769_, 1);
v___y_760_ = v_a_708_;
v___y_761_ = v_a_709_;
v___y_762_ = v_a_710_;
v___y_763_ = v_a_711_;
v___y_764_ = v_a_712_;
goto v___jp_759_;
}
else
{
lean_dec_ref(v_v_758_);
lean_dec_ref(v_t_757_);
lean_dec_ref(v___f_756_);
lean_dec(v_declName_750_);
return v___x_769_;
}
}
}
default: 
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = lean_expr_instantiate_rev(v_e_707_, v_xs_705_);
lean_dec_ref(v_xs_705_);
lean_dec_ref(v_e_707_);
v___x_773_ = l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit(v_a_704_, v___x_772_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
if (lean_obj_tag(v___x_773_) == 0)
{
if (v_isType_706_ == 0)
{
lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_781_; 
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_781_ == 0)
{
lean_object* v_unused_782_; 
v_unused_782_ = lean_ctor_get(v___x_773_, 0);
lean_dec(v_unused_782_);
v___x_775_ = v___x_773_;
v_isShared_776_ = v_isSharedCheck_781_;
goto v_resetjp_774_;
}
else
{
lean_dec(v___x_773_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_781_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_777_; lean_object* v___x_779_; 
v___x_777_ = lean_box(0);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v___x_777_);
v___x_779_ = v___x_775_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_783_; lean_object* v___x_784_; 
v_a_783_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_783_);
lean_dec_ref_known(v___x_773_, 1);
lean_inc(v_a_712_);
lean_inc_ref(v_a_711_);
lean_inc(v_a_710_);
lean_inc_ref(v_a_709_);
v___x_784_ = lean_infer_type(v_a_783_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v___x_786_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_785_);
lean_dec_ref_known(v___x_784_, 1);
lean_inc(v_a_712_);
lean_inc_ref(v_a_711_);
lean_inc(v_a_710_);
lean_inc_ref(v_a_709_);
v___x_786_ = lean_whnf(v_a_785_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_798_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_798_ == 0)
{
v___x_789_ = v___x_786_;
v_isShared_790_ = v_isSharedCheck_798_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_786_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_798_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
uint8_t v___x_791_; 
v___x_791_ = l_Lean_Expr_isSort(v_a_787_);
lean_dec(v_a_787_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; lean_object* v___x_793_; 
lean_del_object(v___x_789_);
v___x_792_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___closed__3, &l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___closed__3_once, _init_l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___closed__3);
v___x_793_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__1___redArg(v___x_792_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
return v___x_793_;
}
else
{
lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_794_ = lean_box(0);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v___x_794_);
v___x_796_ = v___x_789_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_794_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
v_a_799_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_786_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_786_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
v_a_807_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_784_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_784_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
v_a_815_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_773_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_773_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
}
v___jp_714_:
{
uint8_t v___x_724_; lean_object* v___x_725_; 
v___x_724_ = 0;
v___x_725_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__6___redArg(v___y_717_, v___y_716_, v___y_715_, v___y_718_, v___x_724_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
return v___x_725_;
}
v___jp_726_:
{
lean_object* v___x_736_; lean_object* v___f_737_; lean_object* v_d_738_; uint8_t v___x_739_; 
v___x_736_ = lean_box(v_isType_706_);
lean_inc_ref(v_xs_705_);
v___f_737_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___lam__0___boxed), 12, 5);
lean_closure_set(v___f_737_, 0, v_xs_705_);
lean_closure_set(v___f_737_, 1, v___x_736_);
lean_closure_set(v___f_737_, 2, v_e_707_);
lean_closure_set(v___f_737_, 3, v_a_704_);
lean_closure_set(v___f_737_, 4, v_b_729_);
v_d_738_ = lean_expr_instantiate_rev(v_d_728_, v_xs_705_);
lean_dec_ref(v_xs_705_);
lean_dec_ref(v_d_728_);
v___x_739_ = l_Lean_Expr_hasLooseBVars(v_d_738_);
if (v___x_739_ == 0)
{
v___y_715_ = v_d_738_;
v___y_716_ = v_bi_730_;
v___y_717_ = v_n_727_;
v___y_718_ = v___f_737_;
v___y_719_ = v___y_731_;
v___y_720_ = v___y_732_;
v___y_721_ = v___y_733_;
v___y_722_ = v___y_734_;
v___y_723_ = v___y_735_;
goto v___jp_714_;
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___closed__1, &l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___closed__1_once, _init_l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___closed__1);
v___x_741_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__1___redArg(v___x_740_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_dec_ref_known(v___x_741_, 1);
v___y_715_ = v_d_738_;
v___y_716_ = v_bi_730_;
v___y_717_ = v_n_727_;
v___y_718_ = v___f_737_;
v___y_719_ = v___y_731_;
v___y_720_ = v___y_732_;
v___y_721_ = v___y_733_;
v___y_722_ = v___y_734_;
v___y_723_ = v___y_735_;
goto v___jp_714_;
}
else
{
lean_dec_ref(v_d_738_);
lean_dec_ref(v___f_737_);
lean_dec(v_n_727_);
return v___x_741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___lam__1(lean_object* v_xs_823_, lean_object* v_a_824_, uint8_t v_isType_825_, lean_object* v_body_826_, lean_object* v_x_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_array_push(v_xs_823_, v_x_827_);
v___x_835_ = l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders(v_a_824_, v___x_834_, v_isType_825_, v_body_826_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__4___boxed(lean_object* v_a_836_, lean_object* v___x_837_, lean_object* v_x_838_, lean_object* v_x_839_, lean_object* v_x_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
uint8_t v___x_14945__boxed_847_; lean_object* v_res_848_; 
v___x_14945__boxed_847_ = lean_unbox(v___x_837_);
v_res_848_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__4(v_a_836_, v___x_14945__boxed_847_, v_x_838_, v_x_839_, v_x_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders___boxed(lean_object* v_a_849_, lean_object* v_xs_850_, lean_object* v_isType_851_, lean_object* v_e_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
uint8_t v_isType_boxed_859_; lean_object* v_res_860_; 
v_isType_boxed_859_ = lean_unbox(v_isType_851_);
v_res_860_ = l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders(v_a_849_, v_xs_850_, v_isType_boxed_859_, v_e_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec(v_a_853_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit___boxed(lean_object* v_a_861_, lean_object* v_e_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit(v_a_861_, v_e_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_);
lean_dec(v_a_867_);
lean_dec_ref(v_a_866_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
lean_dec(v_a_863_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2___boxed(lean_object* v_a_870_, lean_object* v___x_871_, lean_object* v_a_872_, lean_object* v_as_873_, lean_object* v_sz_874_, lean_object* v_i_875_, lean_object* v_b_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
uint8_t v___x_15156__boxed_883_; size_t v_sz_boxed_884_; size_t v_i_boxed_885_; lean_object* v_res_886_; 
v___x_15156__boxed_883_ = lean_unbox(v___x_871_);
v_sz_boxed_884_ = lean_unbox_usize(v_sz_874_);
lean_dec(v_sz_874_);
v_i_boxed_885_ = lean_unbox_usize(v_i_875_);
lean_dec(v_i_875_);
v_res_886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__2(v_a_870_, v___x_15156__boxed_883_, v_a_872_, v_as_873_, v_sz_boxed_884_, v_i_boxed_885_, v_b_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v_as_873_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__6(lean_object* v_00_u03b1_887_, lean_object* v_name_888_, uint8_t v_bi_889_, lean_object* v_type_890_, lean_object* v_k_891_, uint8_t v_kind_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__6___redArg(v_name_888_, v_bi_889_, v_type_890_, v_k_891_, v_kind_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__6___boxed(lean_object* v_00_u03b1_900_, lean_object* v_name_901_, lean_object* v_bi_902_, lean_object* v_type_903_, lean_object* v_k_904_, lean_object* v_kind_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
uint8_t v_bi_boxed_912_; uint8_t v_kind_boxed_913_; lean_object* v_res_914_; 
v_bi_boxed_912_ = lean_unbox(v_bi_902_);
v_kind_boxed_913_ = lean_unbox(v_kind_905_);
v_res_914_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__6(v_00_u03b1_900_, v_name_901_, v_bi_boxed_912_, v_type_903_, v_k_904_, v_kind_boxed_913_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__7(lean_object* v_00_u03b1_915_, lean_object* v_name_916_, lean_object* v_type_917_, lean_object* v_val_918_, lean_object* v_k_919_, uint8_t v_nondep_920_, uint8_t v_kind_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__7___redArg(v_name_916_, v_type_917_, v_val_918_, v_k_919_, v_nondep_920_, v_kind_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__7___boxed(lean_object* v_00_u03b1_929_, lean_object* v_name_930_, lean_object* v_type_931_, lean_object* v_val_932_, lean_object* v_k_933_, lean_object* v_nondep_934_, lean_object* v_kind_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
uint8_t v_nondep_boxed_942_; uint8_t v_kind_boxed_943_; lean_object* v_res_944_; 
v_nondep_boxed_942_ = lean_unbox(v_nondep_934_);
v_kind_boxed_943_ = lean_unbox(v_kind_935_);
v_res_944_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visitBinders_spec__7(v_00_u03b1_929_, v_name_930_, v_type_931_, v_val_932_, v_k_933_, v_nondep_boxed_942_, v_kind_boxed_943_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0(lean_object* v_00_u03b2_945_, lean_object* v_m_946_, lean_object* v_a_947_, lean_object* v_b_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0___redArg(v_m_946_, v_a_947_, v_b_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__1(lean_object* v_00_u03b1_950_, lean_object* v_msg_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__1___redArg(v_msg_951_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__1___boxed(lean_object* v_00_u03b1_959_, lean_object* v_msg_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__1(v_00_u03b1_959_, v_msg_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__3(lean_object* v_00_u03b2_968_, lean_object* v_m_969_, lean_object* v_a_970_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__3___redArg(v_m_969_, v_a_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__3___boxed(lean_object* v_00_u03b2_972_, lean_object* v_m_973_, lean_object* v_a_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__3(v_00_u03b2_972_, v_m_973_, v_a_974_);
lean_dec_ref(v_a_974_);
lean_dec_ref(v_m_973_);
return v_res_975_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__0(lean_object* v_00_u03b2_976_, lean_object* v_a_977_, lean_object* v_x_978_){
_start:
{
uint8_t v___x_979_; 
v___x_979_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__0___redArg(v_a_977_, v_x_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_980_, lean_object* v_a_981_, lean_object* v_x_982_){
_start:
{
uint8_t v_res_983_; lean_object* v_r_984_; 
v_res_983_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__0(v_00_u03b2_980_, v_a_981_, v_x_982_);
lean_dec(v_x_982_);
lean_dec_ref(v_a_981_);
v_r_984_ = lean_box(v_res_983_);
return v_r_984_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__1(lean_object* v_00_u03b2_985_, lean_object* v_data_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__1___redArg(v_data_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__2(lean_object* v_00_u03b2_988_, lean_object* v_a_989_, lean_object* v_b_990_, lean_object* v_x_991_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__2___redArg(v_a_989_, v_b_990_, v_x_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__3_spec__7(lean_object* v_00_u03b2_993_, lean_object* v_a_994_, lean_object* v_x_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__3_spec__7___redArg(v_a_994_, v_x_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__3_spec__7___boxed(lean_object* v_00_u03b2_997_, lean_object* v_a_998_, lean_object* v_x_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__3_spec__7(v_00_u03b2_997_, v_a_998_, v_x_999_);
lean_dec(v_x_999_);
lean_dec_ref(v_a_998_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1001_, lean_object* v_i_1002_, lean_object* v_source_1003_, lean_object* v_target_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__1_spec__5___redArg(v_i_1002_, v_source_1003_, v_target_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_1006_, lean_object* v_x_1007_, lean_object* v_x_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__0_spec__1_spec__5_spec__11___redArg(v_x_1007_, v_x_1008_);
return v___x_1009_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = lean_box(0);
v___x_1011_ = lean_unsigned_to_nat(16u);
v___x_1012_ = lean_mk_array(v___x_1011_, v___x_1010_);
return v___x_1012_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1013_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___lam__0___closed__0);
v___x_1014_ = lean_unsigned_to_nat(0u);
v___x_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
lean_ctor_set(v___x_1015_, 1, v___x_1013_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___lam__0(lean_object* v_eAbst_1016_, lean_object* v_a_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1023_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___lam__0___closed__1);
v___x_1024_ = lean_box(0);
v___x_1025_ = lean_st_mk_ref(v___x_1023_);
v___x_1026_ = l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit(v_a_1017_, v_eAbst_1016_, v___x_1025_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1034_; 
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1034_ == 0)
{
lean_object* v_unused_1035_; 
v_unused_1035_ = lean_ctor_get(v___x_1026_, 0);
lean_dec(v_unused_1035_);
v___x_1028_ = v___x_1026_;
v_isShared_1029_ = v_isSharedCheck_1034_;
goto v_resetjp_1027_;
}
else
{
lean_dec(v___x_1026_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1034_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; lean_object* v___x_1032_; 
v___x_1030_ = lean_st_ref_get(v___x_1025_);
lean_dec(v___x_1025_);
lean_dec(v___x_1030_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1024_);
v___x_1032_ = v___x_1028_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1024_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
lean_dec(v___x_1025_);
v_a_1036_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_1026_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1026_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___lam__0___boxed(lean_object* v_eAbst_1044_, lean_object* v_a_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___lam__0(v_eAbst_1044_, v_a_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0_spec__0___redArg___lam__0(lean_object* v_k_1052_, lean_object* v_b_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v___x_1059_; 
lean_inc(v___y_1057_);
lean_inc_ref(v___y_1056_);
lean_inc(v___y_1055_);
lean_inc_ref(v___y_1054_);
v___x_1059_ = lean_apply_6(v_k_1052_, v_b_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, lean_box(0));
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_1060_, lean_object* v_b_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0_spec__0___redArg___lam__0(v_k_1060_, v_b_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0_spec__0___redArg(lean_object* v_name_1068_, uint8_t v_bi_1069_, lean_object* v_type_1070_, lean_object* v_k_1071_, uint8_t v_kind_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v___f_1078_; lean_object* v___x_1079_; 
v___f_1078_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1078_, 0, v_k_1071_);
v___x_1079_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1068_, v_bi_1069_, v_type_1070_, v___f_1078_, v_kind_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1079_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
v_a_1088_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1079_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1079_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_name_1096_, lean_object* v_bi_1097_, lean_object* v_type_1098_, lean_object* v_k_1099_, lean_object* v_kind_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
uint8_t v_bi_boxed_1106_; uint8_t v_kind_boxed_1107_; lean_object* v_res_1108_; 
v_bi_boxed_1106_ = lean_unbox(v_bi_1097_);
v_kind_boxed_1107_ = lean_unbox(v_kind_1100_);
v_res_1108_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0_spec__0___redArg(v_name_1096_, v_bi_boxed_1106_, v_type_1098_, v_k_1099_, v_kind_boxed_1107_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0___redArg(lean_object* v_name_1109_, lean_object* v_type_1110_, lean_object* v_k_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
uint8_t v___x_1117_; uint8_t v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = 0;
v___x_1118_ = 0;
v___x_1119_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0_spec__0___redArg(v_name_1109_, v___x_1117_, v_type_1110_, v_k_1111_, v___x_1118_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0___redArg___boxed(lean_object* v_name_1120_, lean_object* v_type_1121_, lean_object* v_k_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0___redArg(v_name_1120_, v_type_1121_, v_k_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f(lean_object* v_00_u03b1_1132_, lean_object* v_eAbst_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v___f_1139_; lean_object* v___x_1140_; 
v___f_1139_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1139_, 0, v_eAbst_1133_);
v___x_1140_ = l_Lean_Meta_saveState___redArg(v_a_1135_, v_a_1137_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v___y_1143_; lean_object* v___x_1185_; uint8_t v_transparency_1186_; uint8_t v___x_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1141_);
lean_dec_ref_known(v___x_1140_, 1);
v___x_1185_ = l_Lean_Meta_Context_config(v_a_1134_);
v_transparency_1186_ = lean_ctor_get_uint8(v___x_1185_, 9);
lean_dec_ref(v___x_1185_);
v___x_1187_ = 0;
v___x_1188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___closed__1));
v___x_1189_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1186_, v___x_1187_);
if (v___x_1189_ == 0)
{
lean_object* v_keyedConfig_1190_; uint8_t v_trackZetaDelta_1191_; lean_object* v_zetaDeltaSet_1192_; lean_object* v_lctx_1193_; lean_object* v_localInstances_1194_; lean_object* v_defEqCtx_x3f_1195_; lean_object* v_synthPendingDepth_1196_; lean_object* v_customCanUnfoldPredicate_x3f_1197_; uint8_t v_univApprox_1198_; uint8_t v_inTypeClassResolution_1199_; uint8_t v_cacheInferType_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v_keyedConfig_1190_ = lean_ctor_get(v_a_1134_, 0);
v_trackZetaDelta_1191_ = lean_ctor_get_uint8(v_a_1134_, sizeof(void*)*7);
v_zetaDeltaSet_1192_ = lean_ctor_get(v_a_1134_, 1);
v_lctx_1193_ = lean_ctor_get(v_a_1134_, 2);
v_localInstances_1194_ = lean_ctor_get(v_a_1134_, 3);
v_defEqCtx_x3f_1195_ = lean_ctor_get(v_a_1134_, 4);
v_synthPendingDepth_1196_ = lean_ctor_get(v_a_1134_, 5);
v_customCanUnfoldPredicate_x3f_1197_ = lean_ctor_get(v_a_1134_, 6);
v_univApprox_1198_ = lean_ctor_get_uint8(v_a_1134_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1199_ = lean_ctor_get_uint8(v_a_1134_, sizeof(void*)*7 + 2);
v_cacheInferType_1200_ = lean_ctor_get_uint8(v_a_1134_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1190_);
v___x_1201_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1187_, v_keyedConfig_1190_);
lean_inc(v_customCanUnfoldPredicate_x3f_1197_);
lean_inc(v_synthPendingDepth_1196_);
lean_inc(v_defEqCtx_x3f_1195_);
lean_inc_ref(v_localInstances_1194_);
lean_inc_ref(v_lctx_1193_);
lean_inc(v_zetaDeltaSet_1192_);
v___x_1202_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
lean_ctor_set(v___x_1202_, 1, v_zetaDeltaSet_1192_);
lean_ctor_set(v___x_1202_, 2, v_lctx_1193_);
lean_ctor_set(v___x_1202_, 3, v_localInstances_1194_);
lean_ctor_set(v___x_1202_, 4, v_defEqCtx_x3f_1195_);
lean_ctor_set(v___x_1202_, 5, v_synthPendingDepth_1196_);
lean_ctor_set(v___x_1202_, 6, v_customCanUnfoldPredicate_x3f_1197_);
lean_ctor_set_uint8(v___x_1202_, sizeof(void*)*7, v_trackZetaDelta_1191_);
lean_ctor_set_uint8(v___x_1202_, sizeof(void*)*7 + 1, v_univApprox_1198_);
lean_ctor_set_uint8(v___x_1202_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1199_);
lean_ctor_set_uint8(v___x_1202_, sizeof(void*)*7 + 3, v_cacheInferType_1200_);
v___x_1203_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0___redArg(v___x_1188_, v_00_u03b1_1132_, v___f_1139_, v___x_1202_, v_a_1135_, v_a_1136_, v_a_1137_);
lean_dec_ref_known(v___x_1202_, 7);
v___y_1143_ = v___x_1203_;
goto v___jp_1142_;
}
else
{
lean_object* v___x_1204_; 
v___x_1204_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0___redArg(v___x_1188_, v_00_u03b1_1132_, v___f_1139_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_);
v___y_1143_ = v___x_1204_;
goto v___jp_1142_;
}
v___jp_1142_:
{
if (lean_obj_tag(v___y_1143_) == 0)
{
lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1152_; 
lean_dec(v_a_1141_);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___y_1143_);
if (v_isSharedCheck_1152_ == 0)
{
lean_object* v_unused_1153_; 
v_unused_1153_ = lean_ctor_get(v___y_1143_, 0);
lean_dec(v_unused_1153_);
v___x_1145_ = v___y_1143_;
v_isShared_1146_ = v_isSharedCheck_1152_;
goto v_resetjp_1144_;
}
else
{
lean_dec(v___y_1143_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1152_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
uint8_t v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1147_ = 1;
v___x_1148_ = lean_box(v___x_1147_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1148_);
v___x_1150_ = v___x_1145_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1184_; 
v_a_1154_ = lean_ctor_get(v___y_1143_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___y_1143_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1156_ = v___y_1143_;
v_isShared_1157_ = v_isSharedCheck_1184_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___y_1143_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1184_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
uint8_t v___x_1158_; 
v___x_1158_ = l_Lean_Exception_isInterrupt(v_a_1154_);
if (v___x_1158_ == 0)
{
uint8_t v___x_1159_; 
lean_inc(v_a_1154_);
v___x_1159_ = l_Lean_Exception_isRuntime(v_a_1154_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; 
lean_del_object(v___x_1156_);
lean_dec(v_a_1154_);
v___x_1160_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1141_, v_a_1135_, v_a_1137_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1168_; 
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1168_ == 0)
{
lean_object* v_unused_1169_; 
v_unused_1169_ = lean_ctor_get(v___x_1160_, 0);
lean_dec(v_unused_1169_);
v___x_1162_ = v___x_1160_;
v_isShared_1163_ = v_isSharedCheck_1168_;
goto v_resetjp_1161_;
}
else
{
lean_dec(v___x_1160_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1168_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1164_ = lean_box(v___x_1159_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1164_);
v___x_1166_ = v___x_1162_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
v_a_1170_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1160_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1160_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
else
{
lean_object* v___x_1179_; 
lean_dec(v_a_1141_);
if (v_isShared_1157_ == 0)
{
v___x_1179_ = v___x_1156_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1154_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
else
{
lean_object* v___x_1182_; 
lean_dec(v_a_1141_);
if (v_isShared_1157_ == 0)
{
v___x_1182_ = v___x_1156_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1154_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
}
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
lean_dec_ref(v___f_1139_);
lean_dec_ref(v_00_u03b1_1132_);
v_a_1205_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1140_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1140_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___boxed(lean_object* v_00_u03b1_1213_, lean_object* v_eAbst_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f(v_00_u03b1_1213_, v_eAbst_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_);
lean_dec(v_a_1218_);
lean_dec_ref(v_a_1217_);
lean_dec(v_a_1216_);
lean_dec_ref(v_a_1215_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0_spec__0(lean_object* v_00_u03b1_1221_, lean_object* v_name_1222_, uint8_t v_bi_1223_, lean_object* v_type_1224_, lean_object* v_k_1225_, uint8_t v_kind_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0_spec__0___redArg(v_name_1222_, v_bi_1223_, v_type_1224_, v_k_1225_, v_kind_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1233_, lean_object* v_name_1234_, lean_object* v_bi_1235_, lean_object* v_type_1236_, lean_object* v_k_1237_, lean_object* v_kind_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
uint8_t v_bi_boxed_1244_; uint8_t v_kind_boxed_1245_; lean_object* v_res_1246_; 
v_bi_boxed_1244_ = lean_unbox(v_bi_1235_);
v_kind_boxed_1245_ = lean_unbox(v_kind_1238_);
v_res_1246_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0_spec__0(v_00_u03b1_1233_, v_name_1234_, v_bi_boxed_1244_, v_type_1236_, v_k_1237_, v_kind_boxed_1245_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0(lean_object* v_00_u03b1_1247_, lean_object* v_name_1248_, lean_object* v_type_1249_, lean_object* v_k_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0___redArg(v_name_1248_, v_type_1249_, v_k_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0___boxed(lean_object* v_00_u03b1_1257_, lean_object* v_name_1258_, lean_object* v_type_1259_, lean_object* v_k_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0(v_00_u03b1_1257_, v_name_1258_, v_type_1259_, v_k_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(lean_object* v_e_1267_, lean_object* v___y_1268_){
_start:
{
uint8_t v___x_1270_; 
v___x_1270_ = l_Lean_Expr_hasMVar(v_e_1267_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; 
v___x_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1271_, 0, v_e_1267_);
return v___x_1271_;
}
else
{
lean_object* v___x_1272_; lean_object* v_mctx_1273_; lean_object* v___x_1274_; lean_object* v_fst_1275_; lean_object* v_snd_1276_; lean_object* v___x_1277_; lean_object* v_cache_1278_; lean_object* v_zetaDeltaFVarIds_1279_; lean_object* v_postponed_1280_; lean_object* v_diag_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1290_; 
v___x_1272_ = lean_st_ref_get(v___y_1268_);
v_mctx_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc_ref(v_mctx_1273_);
lean_dec(v___x_1272_);
v___x_1274_ = l_Lean_instantiateMVarsCore(v_mctx_1273_, v_e_1267_);
v_fst_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_fst_1275_);
v_snd_1276_ = lean_ctor_get(v___x_1274_, 1);
lean_inc(v_snd_1276_);
lean_dec_ref(v___x_1274_);
v___x_1277_ = lean_st_ref_take(v___y_1268_);
v_cache_1278_ = lean_ctor_get(v___x_1277_, 1);
v_zetaDeltaFVarIds_1279_ = lean_ctor_get(v___x_1277_, 2);
v_postponed_1280_ = lean_ctor_get(v___x_1277_, 3);
v_diag_1281_ = lean_ctor_get(v___x_1277_, 4);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1290_ == 0)
{
lean_object* v_unused_1291_; 
v_unused_1291_ = lean_ctor_get(v___x_1277_, 0);
lean_dec(v_unused_1291_);
v___x_1283_ = v___x_1277_;
v_isShared_1284_ = v_isSharedCheck_1290_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_diag_1281_);
lean_inc(v_postponed_1280_);
lean_inc(v_zetaDeltaFVarIds_1279_);
lean_inc(v_cache_1278_);
lean_dec(v___x_1277_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1290_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v_snd_1276_);
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_snd_1276_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_cache_1278_);
lean_ctor_set(v_reuseFailAlloc_1289_, 2, v_zetaDeltaFVarIds_1279_);
lean_ctor_set(v_reuseFailAlloc_1289_, 3, v_postponed_1280_);
lean_ctor_set(v_reuseFailAlloc_1289_, 4, v_diag_1281_);
v___x_1286_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = lean_st_ref_put(v___y_1268_, v___x_1286_);
v___x_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1288_, 0, v_fst_1275_);
return v___x_1288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg___boxed(lean_object* v_e_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(v_e_1292_, v___y_1293_);
lean_dec(v___y_1293_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1(lean_object* v_e_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(v_e_1296_, v___y_1298_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___boxed(lean_object* v_e_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1(v_e_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
return v_res_1309_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__7(lean_object* v_opts_1310_, lean_object* v_opt_1311_){
_start:
{
lean_object* v_name_1312_; lean_object* v_defValue_1313_; lean_object* v_map_1314_; lean_object* v___x_1315_; 
v_name_1312_ = lean_ctor_get(v_opt_1311_, 0);
v_defValue_1313_ = lean_ctor_get(v_opt_1311_, 1);
v_map_1314_ = lean_ctor_get(v_opts_1310_, 0);
v___x_1315_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1314_, v_name_1312_);
if (lean_obj_tag(v___x_1315_) == 0)
{
uint8_t v___x_1316_; 
v___x_1316_ = lean_unbox(v_defValue_1313_);
return v___x_1316_;
}
else
{
lean_object* v_val_1317_; 
v_val_1317_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_val_1317_);
lean_dec_ref_known(v___x_1315_, 1);
if (lean_obj_tag(v_val_1317_) == 1)
{
uint8_t v_v_1318_; 
v_v_1318_ = lean_ctor_get_uint8(v_val_1317_, 0);
lean_dec_ref_known(v_val_1317_, 0);
return v_v_1318_;
}
else
{
uint8_t v___x_1319_; 
lean_dec(v_val_1317_);
v___x_1319_ = lean_unbox(v_defValue_1313_);
return v___x_1319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__7___boxed(lean_object* v_opts_1320_, lean_object* v_opt_1321_){
_start:
{
uint8_t v_res_1322_; lean_object* v_r_1323_; 
v_res_1322_ = l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__7(v_opts_1320_, v_opt_1321_);
lean_dec_ref(v_opt_1321_);
lean_dec_ref(v_opts_1320_);
v_r_1323_ = lean_box(v_res_1322_);
return v_r_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__8___redArg(lean_object* v_mvarId_1324_, lean_object* v_x_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1324_, v_x_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1331_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1331_);
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
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1347_; 
v_a_1340_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1342_ = v___x_1331_;
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1331_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1345_; 
if (v_isShared_1343_ == 0)
{
v___x_1345_ = v___x_1342_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1340_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__8___redArg___boxed(lean_object* v_mvarId_1348_, lean_object* v_x_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__8___redArg(v_mvarId_1348_, v_x_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__8(lean_object* v_00_u03b1_1356_, lean_object* v_mvarId_1357_, lean_object* v_x_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__8___redArg(v_mvarId_1357_, v_x_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__8___boxed(lean_object* v_00_u03b1_1365_, lean_object* v_mvarId_1366_, lean_object* v_x_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__8(v_00_u03b1_1365_, v_mvarId_1366_, v_x_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0(lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = lean_expr_instantiate1(v_a_1374_, v_a_1376_);
lean_inc(v___y_1380_);
lean_inc_ref(v___y_1379_);
lean_inc(v___y_1378_);
lean_inc_ref(v___y_1377_);
v___x_1383_ = lean_infer_type(v___x_1382_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1385_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref_known(v___x_1383_, 1);
v___x_1385_ = l_Lean_Meta_isExprDefEq(v_a_1384_, v_a_1375_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1385_;
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_dec_ref(v_a_1375_);
v_a_1386_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1383_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1383_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0___boxed(lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_MVarId_rewrite___lam__0(v_a_1394_, v_a_1395_, v_a_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec_ref(v_a_1396_);
lean_dec_ref(v_a_1394_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__3(size_t v_sz_1403_, size_t v_i_1404_, lean_object* v_bs_1405_){
_start:
{
uint8_t v___x_1406_; 
v___x_1406_ = lean_usize_dec_lt(v_i_1404_, v_sz_1403_);
if (v___x_1406_ == 0)
{
return v_bs_1405_;
}
else
{
lean_object* v_v_1407_; lean_object* v___x_1408_; lean_object* v_bs_x27_1409_; lean_object* v___x_1410_; size_t v___x_1411_; size_t v___x_1412_; lean_object* v___x_1413_; 
v_v_1407_ = lean_array_uget(v_bs_1405_, v_i_1404_);
v___x_1408_ = lean_unsigned_to_nat(0u);
v_bs_x27_1409_ = lean_array_uset(v_bs_1405_, v_i_1404_, v___x_1408_);
v___x_1410_ = l_Lean_Expr_mvarId_x21(v_v_1407_);
lean_dec(v_v_1407_);
v___x_1411_ = ((size_t)1ULL);
v___x_1412_ = lean_usize_add(v_i_1404_, v___x_1411_);
v___x_1413_ = lean_array_uset(v_bs_x27_1409_, v_i_1404_, v___x_1410_);
v_i_1404_ = v___x_1412_;
v_bs_1405_ = v___x_1413_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__3___boxed(lean_object* v_sz_1415_, lean_object* v_i_1416_, lean_object* v_bs_1417_){
_start:
{
size_t v_sz_boxed_1418_; size_t v_i_boxed_1419_; lean_object* v_res_1420_; 
v_sz_boxed_1418_ = lean_unbox_usize(v_sz_1415_);
lean_dec(v_sz_1415_);
v_i_boxed_1419_ = lean_unbox_usize(v_i_1416_);
lean_dec(v_i_1416_);
v_res_1420_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__3(v_sz_boxed_1418_, v_i_boxed_1419_, v_bs_1417_);
return v_res_1420_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__10___redArg(lean_object* v_keys_1421_, lean_object* v_i_1422_, lean_object* v_k_1423_){
_start:
{
lean_object* v___x_1424_; uint8_t v___x_1425_; 
v___x_1424_ = lean_array_get_size(v_keys_1421_);
v___x_1425_ = lean_nat_dec_lt(v_i_1422_, v___x_1424_);
if (v___x_1425_ == 0)
{
lean_dec(v_i_1422_);
return v___x_1425_;
}
else
{
lean_object* v_k_x27_1426_; uint8_t v___x_1427_; 
v_k_x27_1426_ = lean_array_fget_borrowed(v_keys_1421_, v_i_1422_);
v___x_1427_ = l_Lean_instBEqMVarId_beq(v_k_1423_, v_k_x27_1426_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = lean_unsigned_to_nat(1u);
v___x_1429_ = lean_nat_add(v_i_1422_, v___x_1428_);
lean_dec(v_i_1422_);
v_i_1422_ = v___x_1429_;
goto _start;
}
else
{
lean_dec(v_i_1422_);
return v___x_1425_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__10___redArg___boxed(lean_object* v_keys_1431_, lean_object* v_i_1432_, lean_object* v_k_1433_){
_start:
{
uint8_t v_res_1434_; lean_object* v_r_1435_; 
v_res_1434_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__10___redArg(v_keys_1431_, v_i_1432_, v_k_1433_);
lean_dec(v_k_1433_);
lean_dec_ref(v_keys_1431_);
v_r_1435_ = lean_box(v_res_1434_);
return v_r_1435_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(lean_object* v_x_1436_, size_t v_x_1437_, lean_object* v_x_1438_){
_start:
{
if (lean_obj_tag(v_x_1436_) == 0)
{
lean_object* v_es_1439_; lean_object* v___x_1440_; size_t v___x_1441_; size_t v___x_1442_; lean_object* v_j_1443_; lean_object* v___x_1444_; 
v_es_1439_ = lean_ctor_get(v_x_1436_, 0);
v___x_1440_ = lean_box(2);
v___x_1441_ = ((size_t)31ULL);
v___x_1442_ = lean_usize_land(v_x_1437_, v___x_1441_);
v_j_1443_ = lean_usize_to_nat(v___x_1442_);
v___x_1444_ = lean_array_get_borrowed(v___x_1440_, v_es_1439_, v_j_1443_);
lean_dec(v_j_1443_);
switch(lean_obj_tag(v___x_1444_))
{
case 0:
{
lean_object* v_key_1445_; uint8_t v___x_1446_; 
v_key_1445_ = lean_ctor_get(v___x_1444_, 0);
v___x_1446_ = l_Lean_instBEqMVarId_beq(v_x_1438_, v_key_1445_);
return v___x_1446_;
}
case 1:
{
lean_object* v_node_1447_; size_t v___x_1448_; size_t v___x_1449_; 
v_node_1447_ = lean_ctor_get(v___x_1444_, 0);
v___x_1448_ = ((size_t)5ULL);
v___x_1449_ = lean_usize_shift_right(v_x_1437_, v___x_1448_);
v_x_1436_ = v_node_1447_;
v_x_1437_ = v___x_1449_;
goto _start;
}
default: 
{
uint8_t v___x_1451_; 
v___x_1451_ = 0;
return v___x_1451_;
}
}
}
else
{
lean_object* v_ks_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
v_ks_1452_ = lean_ctor_get(v_x_1436_, 0);
v___x_1453_ = lean_unsigned_to_nat(0u);
v___x_1454_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__10___redArg(v_ks_1452_, v___x_1453_, v_x_1438_);
return v___x_1454_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_x_1455_, lean_object* v_x_1456_, lean_object* v_x_1457_){
_start:
{
size_t v_x_17860__boxed_1458_; uint8_t v_res_1459_; lean_object* v_r_1460_; 
v_x_17860__boxed_1458_ = lean_unbox_usize(v_x_1456_);
lean_dec(v_x_1456_);
v_res_1459_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(v_x_1455_, v_x_17860__boxed_1458_, v_x_1457_);
lean_dec(v_x_1457_);
lean_dec_ref(v_x_1455_);
v_r_1460_ = lean_box(v_res_1459_);
return v_r_1460_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(lean_object* v_x_1461_, lean_object* v_x_1462_){
_start:
{
uint64_t v___x_1463_; size_t v___x_1464_; uint8_t v___x_1465_; 
v___x_1463_ = l_Lean_instHashableMVarId_hash(v_x_1462_);
v___x_1464_ = lean_uint64_to_usize(v___x_1463_);
v___x_1465_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(v_x_1461_, v___x_1464_, v_x_1462_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg___boxed(lean_object* v_x_1466_, lean_object* v_x_1467_){
_start:
{
uint8_t v_res_1468_; lean_object* v_r_1469_; 
v_res_1468_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(v_x_1466_, v_x_1467_);
lean_dec(v_x_1467_);
lean_dec_ref(v_x_1466_);
v_r_1469_ = lean_box(v_res_1468_);
return v_r_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(lean_object* v_mvarId_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v___x_1473_; lean_object* v_mctx_1474_; lean_object* v_eAssignment_1475_; uint8_t v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1473_ = lean_st_ref_get(v___y_1471_);
v_mctx_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc_ref(v_mctx_1474_);
lean_dec(v___x_1473_);
v_eAssignment_1475_ = lean_ctor_get(v_mctx_1474_, 8);
lean_inc_ref(v_eAssignment_1475_);
lean_dec_ref(v_mctx_1474_);
v___x_1476_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(v_eAssignment_1475_, v_mvarId_1470_);
lean_dec_ref(v_eAssignment_1475_);
v___x_1477_ = lean_box(v___x_1476_);
v___x_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg___boxed(lean_object* v_mvarId_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(v_mvarId_1479_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec(v_mvarId_1479_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(lean_object* v_as_1483_, size_t v_i_1484_, size_t v_stop_1485_, lean_object* v_b_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_a_1493_; uint8_t v___x_1497_; 
v___x_1497_ = lean_usize_dec_eq(v_i_1484_, v_stop_1485_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = lean_array_uget_borrowed(v_as_1483_, v_i_1484_);
v___x_1499_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(v___x_1498_, v___y_1488_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; uint8_t v___x_1501_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_a_1500_);
lean_dec_ref_known(v___x_1499_, 1);
v___x_1501_ = lean_unbox(v_a_1500_);
lean_dec(v_a_1500_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; 
lean_inc(v___x_1498_);
v___x_1502_ = lean_array_push(v_b_1486_, v___x_1498_);
v_a_1493_ = v___x_1502_;
goto v___jp_1492_;
}
else
{
v_a_1493_ = v_b_1486_;
goto v___jp_1492_;
}
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
lean_dec_ref(v_b_1486_);
v_a_1503_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1499_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1499_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
else
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1511_, 0, v_b_1486_);
return v___x_1511_;
}
v___jp_1492_:
{
size_t v___x_1494_; size_t v___x_1495_; 
v___x_1494_ = ((size_t)1ULL);
v___x_1495_ = lean_usize_add(v_i_1484_, v___x_1494_);
v_i_1484_ = v___x_1495_;
v_b_1486_ = v_a_1493_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6___boxed(lean_object* v_as_1512_, lean_object* v_i_1513_, lean_object* v_stop_1514_, lean_object* v_b_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
size_t v_i_boxed_1521_; size_t v_stop_boxed_1522_; lean_object* v_res_1523_; 
v_i_boxed_1521_ = lean_unbox_usize(v_i_1513_);
lean_dec(v_i_1513_);
v_stop_boxed_1522_ = lean_unbox_usize(v_stop_1514_);
lean_dec(v_stop_1514_);
v_res_1523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(v_as_1512_, v_i_boxed_1521_, v_stop_boxed_1522_, v_b_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec_ref(v_as_1512_);
return v_res_1523_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__5(lean_object* v_a_1524_, lean_object* v_as_1525_, size_t v_i_1526_, size_t v_stop_1527_){
_start:
{
uint8_t v___x_1528_; 
v___x_1528_ = lean_usize_dec_eq(v_i_1526_, v_stop_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; uint8_t v___x_1530_; 
v___x_1529_ = lean_array_uget_borrowed(v_as_1525_, v_i_1526_);
v___x_1530_ = l_Lean_instBEqMVarId_beq(v_a_1524_, v___x_1529_);
if (v___x_1530_ == 0)
{
size_t v___x_1531_; size_t v___x_1532_; 
v___x_1531_ = ((size_t)1ULL);
v___x_1532_ = lean_usize_add(v_i_1526_, v___x_1531_);
v_i_1526_ = v___x_1532_;
goto _start;
}
else
{
return v___x_1530_;
}
}
else
{
uint8_t v___x_1534_; 
v___x_1534_ = 0;
return v___x_1534_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__5___boxed(lean_object* v_a_1535_, lean_object* v_as_1536_, lean_object* v_i_1537_, lean_object* v_stop_1538_){
_start:
{
size_t v_i_boxed_1539_; size_t v_stop_boxed_1540_; uint8_t v_res_1541_; lean_object* v_r_1542_; 
v_i_boxed_1539_ = lean_unbox_usize(v_i_1537_);
lean_dec(v_i_1537_);
v_stop_boxed_1540_ = lean_unbox_usize(v_stop_1538_);
lean_dec(v_stop_1538_);
v_res_1541_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__5(v_a_1535_, v_as_1536_, v_i_boxed_1539_, v_stop_boxed_1540_);
lean_dec_ref(v_as_1536_);
lean_dec(v_a_1535_);
v_r_1542_ = lean_box(v_res_1541_);
return v_r_1542_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_MVarId_rewrite_spec__4(lean_object* v_as_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; uint8_t v___x_1547_; 
v___x_1545_ = lean_unsigned_to_nat(0u);
v___x_1546_ = lean_array_get_size(v_as_1543_);
v___x_1547_ = lean_nat_dec_lt(v___x_1545_, v___x_1546_);
if (v___x_1547_ == 0)
{
return v___x_1547_;
}
else
{
size_t v___x_1548_; size_t v___x_1549_; uint8_t v___x_1550_; 
v___x_1548_ = ((size_t)0ULL);
v___x_1549_ = lean_usize_of_nat(v___x_1546_);
v___x_1550_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__5(v_a_1544_, v_as_1543_, v___x_1548_, v___x_1549_);
return v___x_1550_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_MVarId_rewrite_spec__4___boxed(lean_object* v_as_1551_, lean_object* v_a_1552_){
_start:
{
uint8_t v_res_1553_; lean_object* v_r_1554_; 
v_res_1553_ = l_Array_contains___at___00Lean_MVarId_rewrite_spec__4(v_as_1551_, v_a_1552_);
lean_dec(v_a_1552_);
lean_dec_ref(v_as_1551_);
v_r_1554_ = lean_box(v_res_1553_);
return v_r_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5(lean_object* v_a_1555_, lean_object* v_as_1556_, size_t v_i_1557_, size_t v_stop_1558_, lean_object* v_b_1559_){
_start:
{
lean_object* v___y_1561_; uint8_t v___x_1565_; 
v___x_1565_ = lean_usize_dec_eq(v_i_1557_, v_stop_1558_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; uint8_t v___x_1567_; 
v___x_1566_ = lean_array_uget_borrowed(v_as_1556_, v_i_1557_);
v___x_1567_ = l_Array_contains___at___00Lean_MVarId_rewrite_spec__4(v_a_1555_, v___x_1566_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; 
lean_inc(v___x_1566_);
v___x_1568_ = lean_array_push(v_b_1559_, v___x_1566_);
v___y_1561_ = v___x_1568_;
goto v___jp_1560_;
}
else
{
v___y_1561_ = v_b_1559_;
goto v___jp_1560_;
}
}
else
{
return v_b_1559_;
}
v___jp_1560_:
{
size_t v___x_1562_; size_t v___x_1563_; 
v___x_1562_ = ((size_t)1ULL);
v___x_1563_ = lean_usize_add(v_i_1557_, v___x_1562_);
v_i_1557_ = v___x_1563_;
v_b_1559_ = v___y_1561_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5___boxed(lean_object* v_a_1569_, lean_object* v_as_1570_, lean_object* v_i_1571_, lean_object* v_stop_1572_, lean_object* v_b_1573_){
_start:
{
size_t v_i_boxed_1574_; size_t v_stop_boxed_1575_; lean_object* v_res_1576_; 
v_i_boxed_1574_ = lean_unbox_usize(v_i_1571_);
lean_dec(v_i_1571_);
v_stop_boxed_1575_ = lean_unbox_usize(v_stop_1572_);
lean_dec(v_stop_1572_);
v_res_1576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5(v_a_1569_, v_as_1570_, v_i_boxed_1574_, v_stop_boxed_1575_, v_b_1573_);
lean_dec_ref(v_as_1570_);
lean_dec_ref(v_a_1569_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(lean_object* v_msg_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v_ref_1583_; lean_object* v___x_1584_; lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1593_; 
v_ref_1583_ = lean_ctor_get(v___y_1580_, 2);
v___x_1584_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_visit_spec__1_spec__4(v_msg_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1593_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1593_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1589_; lean_object* v___x_1591_; 
lean_inc(v_ref_1583_);
v___x_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1589_, 0, v_ref_1583_);
lean_ctor_set(v___x_1589_, 1, v_a_1585_);
if (v_isShared_1588_ == 0)
{
lean_ctor_set_tag(v___x_1587_, 1);
lean_ctor_set(v___x_1587_, 0, v___x_1589_);
v___x_1591_ = v___x_1587_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg___boxed(lean_object* v_msg_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(v_msg_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
return v_res_1600_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__0));
v___x_1603_ = l_Lean_stringToMessageData(v___x_1602_);
return v___x_1603_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__2));
v___x_1606_ = l_Lean_stringToMessageData(v___x_1605_);
return v___x_1606_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__8(void){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__7));
v___x_1614_ = l_Lean_stringToMessageData(v___x_1613_);
return v___x_1614_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__10(void){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__9));
v___x_1617_ = l_Lean_stringToMessageData(v___x_1616_);
return v___x_1617_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__12(void){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__11));
v___x_1620_ = l_Lean_stringToMessageData(v___x_1619_);
return v___x_1620_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__14(void){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__13));
v___x_1623_ = l_Lean_stringToMessageData(v___x_1622_);
return v___x_1623_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__16(void){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__15));
v___x_1626_ = l_Lean_stringToMessageData(v___x_1625_);
return v___x_1626_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__18(void){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__17));
v___x_1629_ = l_Lean_stringToMessageData(v___x_1628_);
return v___x_1629_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__20(void){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__19));
v___x_1632_ = l_Lean_stringToMessageData(v___x_1631_);
return v___x_1632_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__25(void){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__24));
v___x_1640_ = l_Lean_stringToMessageData(v___x_1639_);
return v___x_1640_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__29(void){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__28));
v___x_1646_ = l_Lean_stringToMessageData(v___x_1645_);
return v___x_1646_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__31(void){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__30));
v___x_1649_ = l_Lean_stringToMessageData(v___x_1648_);
return v___x_1649_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__33(void){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__32));
v___x_1652_ = l_Lean_stringToMessageData(v___x_1651_);
return v___x_1652_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__35(void){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__34));
v___x_1655_ = l_Lean_stringToMessageData(v___x_1654_);
return v___x_1655_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__37(void){
_start:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1657_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__36));
v___x_1658_ = l_Lean_stringToMessageData(v___x_1657_);
return v___x_1658_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__44(void){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1667_ = lean_box(0);
v___x_1668_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__43));
v___x_1669_ = l_Lean_mkConst(v___x_1668_, v___x_1667_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1(lean_object* v_mvarId_1670_, lean_object* v___x_1671_, lean_object* v_heq_1672_, lean_object* v_e_1673_, lean_object* v_config_1674_, uint8_t v_symm_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___x_1709_; 
lean_inc(v___x_1671_);
lean_inc(v_mvarId_1670_);
v___x_1709_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1670_, v___x_1671_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v___x_1710_; 
lean_dec_ref_known(v___x_1709_, 1);
lean_inc(v___y_1679_);
lean_inc_ref(v___y_1678_);
lean_inc(v___y_1677_);
lean_inc_ref(v___y_1676_);
lean_inc_ref(v_heq_1672_);
v___x_1710_ = lean_infer_type(v_heq_1672_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v___x_1712_; lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_2241_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_a_1711_);
lean_dec_ref_known(v___x_1710_, 1);
v___x_1712_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(v_a_1711_, v___y_1677_);
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_1715_ = v___x_1712_;
v_isShared_1716_ = v_isSharedCheck_2241_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1712_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_2241_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1717_; uint8_t v___x_1718_; lean_object* v___x_1719_; 
v___x_1717_ = lean_box(0);
v___x_1718_ = 0;
v___x_1719_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_1713_, v___x_1717_, v___x_1718_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_2232_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_1722_ = v___x_1719_;
v_isShared_1723_ = v_isSharedCheck_2232_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1719_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_2232_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v_snd_1724_; lean_object* v_fst_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_2231_; 
v_snd_1724_ = lean_ctor_get(v_a_1720_, 1);
v_fst_1725_ = lean_ctor_get(v_a_1720_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v_a_1720_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_1727_ = v_a_1720_;
v_isShared_1728_ = v_isSharedCheck_2231_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_snd_1724_);
lean_inc(v_fst_1725_);
lean_dec(v_a_1720_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_2231_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v_fst_1729_; lean_object* v_snd_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_2230_; 
v_fst_1729_ = lean_ctor_get(v_snd_1724_, 0);
v_snd_1730_ = lean_ctor_get(v_snd_1724_, 1);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_snd_1724_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_1732_ = v_snd_1724_;
v_isShared_1733_ = v_isSharedCheck_2230_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_snd_1730_);
lean_inc(v_fst_1729_);
lean_dec(v_snd_1724_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_2230_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; size_t v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v_a_1743_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; uint8_t v___y_1775_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v_a_1917_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v_eNew_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v___y_2028_; lean_object* v___y_2126_; lean_object* v_heq_2127_; lean_object* v_heqType_2128_; lean_object* v_lhs_2129_; lean_object* v_rhs_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v_heq_2154_; lean_object* v_heqType_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; uint8_t v___x_2214_; 
lean_inc_ref(v_heq_1672_);
v___x_2211_ = l_Lean_mkAppN(v_heq_1672_, v_fst_1725_);
v___x_2212_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__41));
v___x_2213_ = lean_unsigned_to_nat(2u);
v___x_2214_ = l_Lean_Expr_isAppOfArity(v_snd_1730_, v___x_2212_, v___x_2213_);
if (v___x_2214_ == 0)
{
v_heq_2154_ = v___x_2211_;
v_heqType_2155_ = v_snd_1730_;
v___y_2156_ = v___y_1676_;
v___y_2157_ = v___y_1677_;
v___y_2158_ = v___y_1678_;
v___y_2159_ = v___y_1679_;
goto v___jp_2153_;
}
else
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2215_ = l_Lean_Expr_appFn_x21(v_snd_1730_);
v___x_2216_ = l_Lean_Expr_appArg_x21(v___x_2215_);
lean_dec_ref(v___x_2215_);
v___x_2217_ = l_Lean_Expr_appArg_x21(v_snd_1730_);
lean_dec(v_snd_1730_);
lean_inc_ref(v___x_2217_);
lean_inc_ref(v___x_2216_);
v___x_2218_ = l_Lean_Meta_mkEq(v___x_2216_, v___x_2217_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_object* v_a_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_a_2219_);
lean_dec_ref_known(v___x_2218_, 1);
v___x_2220_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__44, &l_Lean_MVarId_rewrite___lam__1___closed__44_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__44);
v___x_2221_ = l_Lean_mkApp3(v___x_2220_, v___x_2216_, v___x_2217_, v___x_2211_);
v_heq_2154_ = v___x_2221_;
v_heqType_2155_ = v_a_2219_;
v___y_2156_ = v___y_1676_;
v___y_2157_ = v___y_1677_;
v___y_2158_ = v___y_1678_;
v___y_2159_ = v___y_1679_;
goto v___jp_2153_;
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_dec_ref(v___x_2217_);
lean_dec_ref(v___x_2216_);
lean_dec_ref(v___x_2211_);
lean_del_object(v___x_1732_);
lean_dec(v_fst_1729_);
lean_del_object(v___x_1727_);
lean_dec(v_fst_1725_);
lean_del_object(v___x_1722_);
lean_del_object(v___x_1715_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec_ref(v_config_1674_);
lean_dec_ref(v_e_1673_);
lean_dec_ref(v_heq_1672_);
lean_dec(v___x_1671_);
lean_dec(v_mvarId_1670_);
v_a_2222_ = lean_ctor_get(v___x_2218_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2218_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2218_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
v___jp_1734_:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_Meta_appendParentTag(v_mvarId_1670_, v_fst_1725_, v_fst_1729_, v___y_1740_, v___y_1736_, v___y_1735_, v___y_1742_);
lean_dec(v_fst_1729_);
lean_dec(v_fst_1725_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v___x_1745_; 
lean_dec_ref_known(v___x_1744_, 1);
v___x_1745_ = l_Lean_Meta_getMVarsNoDelayed(v_heq_1672_, v___y_1740_, v___y_1736_, v___y_1735_, v___y_1742_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1740_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_a_1746_);
lean_dec_ref_known(v___x_1745_, 1);
v___x_1747_ = lean_array_get_size(v_a_1746_);
v___x_1748_ = lean_mk_empty_array_with_capacity(v___y_1737_);
v___x_1749_ = lean_nat_dec_lt(v___y_1737_, v___x_1747_);
if (v___x_1749_ == 0)
{
lean_dec(v_a_1746_);
v___y_1701_ = v___y_1738_;
v___y_1702_ = v_a_1743_;
v___y_1703_ = v___y_1741_;
v___y_1704_ = v___x_1748_;
goto v___jp_1700_;
}
else
{
size_t v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = lean_usize_of_nat(v___x_1747_);
v___x_1751_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5(v_a_1743_, v_a_1746_, v___y_1739_, v___x_1750_, v___x_1748_);
lean_dec(v_a_1746_);
v___y_1701_ = v___y_1738_;
v___y_1702_ = v_a_1743_;
v___y_1703_ = v___y_1741_;
v___y_1704_ = v___x_1751_;
goto v___jp_1700_;
}
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
lean_dec_ref(v_a_1743_);
lean_dec_ref(v___y_1741_);
lean_dec_ref(v___y_1738_);
v_a_1752_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1745_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1745_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
lean_dec_ref(v_a_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec_ref(v_heq_1672_);
v_a_1760_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___x_1744_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1744_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
v___jp_1768_:
{
uint8_t v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = 0;
lean_inc(v_fst_1729_);
lean_inc(v_mvarId_1670_);
v___x_1777_ = l_Lean_Meta_postprocessAppMVars(v___x_1671_, v_mvarId_1670_, v_fst_1725_, v_fst_1729_, v___y_1775_, v___x_1776_, v___y_1772_, v___y_1770_, v___y_1769_, v___y_1774_);
if (lean_obj_tag(v___x_1777_) == 0)
{
size_t v_sz_1778_; size_t v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
lean_dec_ref_known(v___x_1777_, 1);
v_sz_1778_ = lean_array_size(v_fst_1725_);
v___x_1779_ = ((size_t)0ULL);
lean_inc(v_fst_1725_);
v___x_1780_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__3(v_sz_1778_, v___x_1779_, v_fst_1725_);
v___x_1781_ = lean_unsigned_to_nat(0u);
v___x_1782_ = lean_array_get_size(v___x_1780_);
v___x_1783_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__4));
v___x_1784_ = lean_nat_dec_lt(v___x_1781_, v___x_1782_);
if (v___x_1784_ == 0)
{
lean_dec_ref(v___x_1780_);
v___y_1735_ = v___y_1769_;
v___y_1736_ = v___y_1770_;
v___y_1737_ = v___x_1781_;
v___y_1738_ = v___y_1771_;
v___y_1739_ = v___x_1779_;
v___y_1740_ = v___y_1772_;
v___y_1741_ = v___y_1773_;
v___y_1742_ = v___y_1774_;
v_a_1743_ = v___x_1783_;
goto v___jp_1734_;
}
else
{
size_t v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = lean_usize_of_nat(v___x_1782_);
v___x_1786_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(v___x_1780_, v___x_1779_, v___x_1785_, v___x_1783_, v___y_1772_, v___y_1770_, v___y_1769_, v___y_1774_);
lean_dec_ref(v___x_1780_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_a_1787_);
lean_dec_ref_known(v___x_1786_, 1);
v___y_1735_ = v___y_1769_;
v___y_1736_ = v___y_1770_;
v___y_1737_ = v___x_1781_;
v___y_1738_ = v___y_1771_;
v___y_1739_ = v___x_1779_;
v___y_1740_ = v___y_1772_;
v___y_1741_ = v___y_1773_;
v___y_1742_ = v___y_1774_;
v_a_1743_ = v_a_1787_;
goto v___jp_1734_;
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v_fst_1729_);
lean_dec(v_fst_1725_);
lean_dec_ref(v_heq_1672_);
lean_dec(v_mvarId_1670_);
v_a_1788_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1786_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1786_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v_fst_1729_);
lean_dec(v_fst_1725_);
lean_dec_ref(v_heq_1672_);
lean_dec(v_mvarId_1670_);
v_a_1796_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1777_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1777_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
v___jp_1804_:
{
lean_object* v___x_1816_; 
lean_inc_ref(v___y_1808_);
v___x_1816_ = l_Lean_Meta_getLevel(v___y_1808_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1817_; lean_object* v___x_1818_; 
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
lean_inc(v_a_1817_);
lean_dec_ref_known(v___x_1816_, 1);
lean_inc_ref(v___y_1810_);
v___x_1818_ = l_Lean_Meta_getLevel(v___y_1810_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1823_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_a_1819_);
lean_dec_ref_known(v___x_1818_, 1);
v___x_1820_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__6));
v___x_1821_ = lean_box(0);
if (v_isShared_1733_ == 0)
{
lean_ctor_set_tag(v___x_1732_, 1);
lean_ctor_set(v___x_1732_, 1, v___x_1821_);
lean_ctor_set(v___x_1732_, 0, v_a_1819_);
v___x_1823_ = v___x_1732_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1819_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v___x_1821_);
v___x_1823_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1825_; 
if (v_isShared_1728_ == 0)
{
lean_ctor_set_tag(v___x_1727_, 1);
lean_ctor_set(v___x_1727_, 1, v___x_1823_);
lean_ctor_set(v___x_1727_, 0, v_a_1817_);
v___x_1825_ = v___x_1727_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1817_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; uint8_t v___x_1830_; 
v___x_1826_ = l_Lean_Expr_const___override(v___x_1820_, v___x_1825_);
v___x_1827_ = l_Lean_mkApp6(v___x_1826_, v___y_1808_, v___y_1810_, v___y_1806_, v___y_1807_, v___y_1809_, v___y_1805_);
v___x_1828_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1814_);
v___x_1829_ = l_Lean_Meta_tactic_skipAssignedInstances;
v___x_1830_ = l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__7(v___x_1828_, v___x_1829_);
lean_dec_ref(v___x_1828_);
if (v___x_1830_ == 0)
{
uint8_t v___x_1831_; 
v___x_1831_ = 1;
v___y_1769_ = v___y_1814_;
v___y_1770_ = v___y_1813_;
v___y_1771_ = v___x_1827_;
v___y_1772_ = v___y_1812_;
v___y_1773_ = v___y_1811_;
v___y_1774_ = v___y_1815_;
v___y_1775_ = v___x_1831_;
goto v___jp_1768_;
}
else
{
uint8_t v___x_1832_; 
v___x_1832_ = 0;
v___y_1769_ = v___y_1814_;
v___y_1770_ = v___y_1813_;
v___y_1771_ = v___x_1827_;
v___y_1772_ = v___y_1812_;
v___y_1773_ = v___y_1811_;
v___y_1774_ = v___y_1815_;
v___y_1775_ = v___x_1832_;
goto v___jp_1768_;
}
}
}
}
else
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1842_; 
lean_dec(v_a_1817_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_del_object(v___x_1732_);
lean_dec(v_fst_1729_);
lean_del_object(v___x_1727_);
lean_dec(v_fst_1725_);
lean_dec_ref(v_heq_1672_);
lean_dec(v___x_1671_);
lean_dec(v_mvarId_1670_);
v_a_1835_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1837_ = v___x_1818_;
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1818_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1840_; 
if (v_isShared_1838_ == 0)
{
v___x_1840_ = v___x_1837_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1835_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
else
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_del_object(v___x_1732_);
lean_dec(v_fst_1729_);
lean_del_object(v___x_1727_);
lean_dec(v_fst_1725_);
lean_dec_ref(v_heq_1672_);
lean_dec(v___x_1671_);
lean_dec(v_mvarId_1670_);
v_a_1843_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1816_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1816_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
v___jp_1851_:
{
lean_object* v___x_1866_; 
lean_inc_ref(v___y_1859_);
v___x_1866_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f_spec__0___redArg(v___y_1860_, v___y_1859_, v___y_1855_, v___y_1865_, v___y_1857_, v___y_1852_, v___y_1854_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_a_1867_; uint8_t v___x_1868_; 
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
lean_inc(v_a_1867_);
lean_dec_ref_known(v___x_1866_, 1);
v___x_1868_ = lean_unbox(v_a_1867_);
lean_dec(v_a_1867_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1883_; 
v___x_1869_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__8, &l_Lean_MVarId_rewrite___lam__1___closed__8_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__8);
lean_inc_ref(v___y_1861_);
v___x_1870_ = l_Lean_MessageData_ofExpr(v___y_1861_);
v___x_1871_ = l_Lean_indentD(v___x_1870_);
v___x_1872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1869_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__10, &l_Lean_MVarId_rewrite___lam__1___closed__10_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__10);
v___x_1874_ = l_Lean_indentExpr(v___y_1862_);
v___x_1875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1873_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
v___x_1876_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__12, &l_Lean_MVarId_rewrite___lam__1___closed__12_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__12);
v___x_1877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1875_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
lean_inc_ref(v___y_1856_);
v___x_1878_ = l_Lean_indentExpr(v___y_1856_);
v___x_1879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1877_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
v___x_1880_ = l_Lean_MessageData_note(v___x_1879_);
v___x_1881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1872_);
lean_ctor_set(v___x_1881_, 1, v___x_1880_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set_tag(v___x_1715_, 1);
lean_ctor_set(v___x_1715_, 0, v___x_1881_);
v___x_1883_ = v___x_1715_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1881_);
v___x_1883_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1884_; 
lean_inc(v_mvarId_1670_);
lean_inc(v___x_1671_);
v___x_1884_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1671_, v_mvarId_1670_, v___x_1883_, v___y_1865_, v___y_1857_, v___y_1852_, v___y_1854_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_dec_ref_known(v___x_1884_, 1);
v___y_1805_ = v___y_1853_;
v___y_1806_ = v___y_1856_;
v___y_1807_ = v___y_1858_;
v___y_1808_ = v___y_1859_;
v___y_1809_ = v___y_1861_;
v___y_1810_ = v___y_1863_;
v___y_1811_ = v___y_1864_;
v___y_1812_ = v___y_1865_;
v___y_1813_ = v___y_1857_;
v___y_1814_ = v___y_1852_;
v___y_1815_ = v___y_1854_;
goto v___jp_1804_;
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
lean_dec_ref(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec_ref(v___y_1861_);
lean_dec_ref(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_del_object(v___x_1732_);
lean_dec(v_fst_1729_);
lean_del_object(v___x_1727_);
lean_dec(v_fst_1725_);
lean_dec_ref(v_heq_1672_);
lean_dec(v___x_1671_);
lean_dec(v_mvarId_1670_);
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1884_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1884_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_1862_);
lean_del_object(v___x_1715_);
v___y_1805_ = v___y_1853_;
v___y_1806_ = v___y_1856_;
v___y_1807_ = v___y_1858_;
v___y_1808_ = v___y_1859_;
v___y_1809_ = v___y_1861_;
v___y_1810_ = v___y_1863_;
v___y_1811_ = v___y_1864_;
v___y_1812_ = v___y_1865_;
v___y_1813_ = v___y_1857_;
v___y_1814_ = v___y_1852_;
v___y_1815_ = v___y_1854_;
goto v___jp_1804_;
}
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
lean_dec_ref(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec_ref(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_del_object(v___x_1732_);
lean_dec(v_fst_1729_);
lean_del_object(v___x_1727_);
lean_dec(v_fst_1725_);
lean_del_object(v___x_1715_);
lean_dec_ref(v_heq_1672_);
lean_dec(v___x_1671_);
lean_dec(v_mvarId_1670_);
v_a_1894_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1866_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1866_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
v___jp_1902_:
{
uint8_t v___x_1918_; 
v___x_1918_ = l_Lean_Exception_isInterrupt(v_a_1917_);
if (v___x_1918_ == 0)
{
uint8_t v___x_1919_; 
lean_inc_ref(v_a_1917_);
v___x_1919_ = l_Lean_Exception_isRuntime(v_a_1917_);
if (v___x_1919_ == 0)
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
lean_del_object(v___x_1722_);
v___x_1920_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__14, &l_Lean_MVarId_rewrite___lam__1___closed__14_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__14);
lean_inc_ref(v___y_1911_);
v___x_1921_ = l_Lean_MessageData_ofExpr(v___y_1911_);
v___x_1922_ = l_Lean_indentD(v___x_1921_);
v___x_1923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1920_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__16, &l_Lean_MVarId_rewrite___lam__1___closed__16_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__16);
v___x_1925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1923_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = l_Lean_Exception_toMessageData(v_a_1917_);
v___x_1927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1925_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___x_1928_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__18, &l_Lean_MVarId_rewrite___lam__1___closed__18_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__18);
v___x_1929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1927_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__6));
v___x_1931_ = l_Lean_MessageData_ofConstName(v___x_1930_, v___x_1919_);
v___x_1932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1929_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
v___x_1933_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__20, &l_Lean_MVarId_rewrite___lam__1___closed__20_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__20);
v___x_1934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1932_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
v___x_1935_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__23));
v___x_1936_ = l_Lean_MessageData_ofConstName(v___x_1935_, v___x_1919_);
v___x_1937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1934_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
v___x_1938_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__25, &l_Lean_MVarId_rewrite___lam__1___closed__25_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__25);
v___x_1939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1937_);
lean_ctor_set(v___x_1939_, 1, v___x_1938_);
v___x_1940_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__27));
v___x_1941_ = l_Lean_MessageData_ofConstName(v___x_1940_, v___x_1919_);
v___x_1942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1939_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
v___x_1943_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__29, &l_Lean_MVarId_rewrite___lam__1___closed__29_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__29);
v___x_1944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1942_);
lean_ctor_set(v___x_1944_, 1, v___x_1943_);
v___x_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
lean_inc(v_mvarId_1670_);
lean_inc(v___x_1671_);
v___x_1946_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1671_, v_mvarId_1670_, v___x_1945_, v___y_1916_, v___y_1908_, v___y_1903_, v___y_1905_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_dec_ref_known(v___x_1946_, 1);
v___y_1852_ = v___y_1903_;
v___y_1853_ = v___y_1904_;
v___y_1854_ = v___y_1905_;
v___y_1855_ = v___y_1906_;
v___y_1856_ = v___y_1907_;
v___y_1857_ = v___y_1908_;
v___y_1858_ = v___y_1909_;
v___y_1859_ = v___y_1910_;
v___y_1860_ = v___y_1912_;
v___y_1861_ = v___y_1911_;
v___y_1862_ = v___y_1913_;
v___y_1863_ = v___y_1914_;
v___y_1864_ = v___y_1915_;
v___y_1865_ = v___y_1916_;
goto v___jp_1851_;
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_dec_ref(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_del_object(v___x_1732_);
lean_dec(v_fst_1729_);
lean_del_object(v___x_1727_);
lean_dec(v_fst_1725_);
lean_del_object(v___x_1715_);
lean_dec_ref(v_heq_1672_);
lean_dec(v___x_1671_);
lean_dec(v_mvarId_1670_);
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1946_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1946_);
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
lean_object* v___x_1956_; 
lean_dec_ref(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_del_object(v___x_1732_);
lean_dec(v_fst_1729_);
lean_del_object(v___x_1727_);
lean_dec(v_fst_1725_);
lean_del_object(v___x_1715_);
lean_dec_ref(v_heq_1672_);
lean_dec(v___x_1671_);
lean_dec(v_mvarId_1670_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set_tag(v___x_1722_, 1);
lean_ctor_set(v___x_1722_, 0, v_a_1917_);
v___x_1956_ = v___x_1722_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1917_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
else
{
lean_object* v___x_1959_; 
lean_dec_ref(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_del_object(v___x_1732_);
lean_dec(v_fst_1729_);
lean_del_object(v___x_1727_);
lean_dec(v_fst_1725_);
lean_del_object(v___x_1715_);
lean_dec_ref(v_heq_1672_);
lean_dec(v___x_1671_);
lean_dec(v_mvarId_1670_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set_tag(v___x_1722_, 1);
lean_ctor_set(v___x_1722_, 0, v_a_1917_);
v___x_1959_ = v___x_1722_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1917_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
v___jp_1961_:
{
lean_object* v___x_1974_; 
lean_inc(v___y_1973_);
lean_inc_ref(v___y_1972_);
lean_inc(v___y_1971_);
lean_inc_ref(v___y_1970_);
lean_inc_ref(v___y_1967_);
v___x_1974_ = lean_infer_type(v___y_1967_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; lean_object* v___f_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc_n(v_a_1975_, 2);
lean_dec_ref_known(v___x_1974_, 1);
v___f_1976_ = lean_alloc_closure((void*)(l_Lean_MVarId_rewrite___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1976_, 0, v___y_1962_);
lean_closure_set(v___f_1976_, 1, v_a_1975_);
v___x_1977_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f___closed__1));
v___x_1978_ = 0;
lean_inc_ref(v___y_1968_);
lean_inc_ref_n(v___y_1966_, 2);
v___x_1979_ = l_Lean_mkLambda(v___x_1977_, v___x_1978_, v___y_1966_, v___y_1968_);
v___x_1980_ = l___private_Lean_Meta_Tactic_Rewrite_0__Lean_Meta_checkMotive_x3f(v___y_1966_, v___y_1968_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; uint8_t v___x_1982_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_a_1981_);
lean_dec_ref_known(v___x_1980_, 1);
v___x_1982_ = lean_unbox(v_a_1981_);
lean_dec(v_a_1981_);
if (v___x_1982_ == 0)
{
uint8_t v___x_1983_; lean_object* v___x_1984_; 
v___x_1983_ = 0;
lean_inc_ref(v___x_1979_);
v___x_1984_ = l_Lean_Meta_check(v___x_1979_, v___x_1983_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_dec_ref_known(v___x_1984_, 1);
lean_del_object(v___x_1722_);
v___y_1852_ = v___y_1972_;
v___y_1853_ = v___y_1963_;
v___y_1854_ = v___y_1973_;
v___y_1855_ = v___f_1976_;
v___y_1856_ = v___y_1964_;
v___y_1857_ = v___y_1971_;
v___y_1858_ = v___y_1965_;
v___y_1859_ = v___y_1966_;
v___y_1860_ = v___x_1977_;
v___y_1861_ = v___x_1979_;
v___y_1862_ = v___y_1967_;
v___y_1863_ = v_a_1975_;
v___y_1864_ = v_eNew_1969_;
v___y_1865_ = v___y_1970_;
goto v___jp_1851_;
}
else
{
lean_object* v_a_1985_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_a_1985_);
lean_dec_ref_known(v___x_1984_, 1);
v___y_1903_ = v___y_1972_;
v___y_1904_ = v___y_1963_;
v___y_1905_ = v___y_1973_;
v___y_1906_ = v___f_1976_;
v___y_1907_ = v___y_1964_;
v___y_1908_ = v___y_1971_;
v___y_1909_ = v___y_1965_;
v___y_1910_ = v___y_1966_;
v___y_1911_ = v___x_1979_;
v___y_1912_ = v___x_1977_;
v___y_1913_ = v___y_1967_;
v___y_1914_ = v_a_1975_;
v___y_1915_ = v_eNew_1969_;
v___y_1916_ = v___y_1970_;
v_a_1917_ = v_a_1985_;
goto v___jp_1902_;
}
}
else
{
lean_del_object(v___x_1722_);
v___y_1852_ = v___y_1972_;
v___y_1853_ = v___y_1963_;
v___y_1854_ = v___y_1973_;
v___y_1855_ = v___f_1976_;
v___y_1856_ = v___y_1964_;
v___y_1857_ = v___y_1971_;
v___y_1858_ = v___y_1965_;
v___y_1859_ = v___y_1966_;
v___y_1860_ = v___x_1977_;
v___y_1861_ = v___x_1979_;
v___y_1862_ = v___y_1967_;
v___y_1863_ = v_a_1975_;
v___y_1864_ = v_eNew_1969_;
v___y_1865_ = v___y_1970_;
goto v___jp_1851_;
}
}
else
{
lean_object* v_a_1986_; 
v_a_1986_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_a_1986_);
lean_dec_ref_known(v___x_1980_, 1);
v___y_1903_ = v___y_1972_;
v___y_1904_ = v___y_1963_;
v___y_1905_ = v___y_1973_;
v___y_1906_ = v___f_1976_;
v___y_1907_ = v___y_1964_;
v___y_1908_ = v___y_1971_;
v___y_1909_ = v___y_1965_;
v___y_1910_ = v___y_1966_;
v___y_1911_ = v___x_1979_;
v___y_1912_ = v___x_1977_;
v___y_1913_ = v___y_1967_;
v___y_1914_ = v_a_1975_;
v___y_1915_ = v_eNew_1969_;
v___y_1916_ = v___y_1970_;
v_a_1917_ = v_a_1986_;
goto v___jp_1902_;
}
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec_ref(v_eNew_1969_);
lean_dec_ref(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_del_object(v___x_1732_);
lean_dec(v_fst_1729_);
lean_del_object(v___x_1727_);
lean_dec(v_fst_1725_);
lean_del_object(v___x_1722_);
lean_del_object(v___x_1715_);
lean_dec_ref(v_heq_1672_);
lean_dec(v___x_1671_);
lean_dec(v_mvarId_1670_);
v_a_1987_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1974_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1974_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
v___jp_1995_:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v_a_2008_; uint8_t v___x_2009_; 
v___x_2006_ = lean_expr_instantiate1(v___y_1996_, v___y_1999_);
v___x_2007_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(v___x_2006_, v___y_2003_);
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2008_);
lean_dec_ref(v___x_2007_);
v___x_2009_ = l_Lean_Expr_hasBinderNameHint(v___y_1999_);
if (v___x_2009_ == 0)
{
lean_inc_ref(v___y_1996_);
v___y_1962_ = v___y_1996_;
v___y_1963_ = v___y_1997_;
v___y_1964_ = v___y_1998_;
v___y_1965_ = v___y_1999_;
v___y_1966_ = v___y_2000_;
v___y_1967_ = v___y_2001_;
v___y_1968_ = v___y_1996_;
v_eNew_1969_ = v_a_2008_;
v___y_1970_ = v___y_2002_;
v___y_1971_ = v___y_2003_;
v___y_1972_ = v___y_2004_;
v___y_1973_ = v___y_2005_;
goto v___jp_1961_;
}
else
{
lean_object* v___x_2010_; 
v___x_2010_ = l_Lean_Expr_resolveBinderNameHint(v_a_2008_, v___y_2004_, v___y_2005_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref_known(v___x_2010_, 1);
lean_inc_ref(v___y_1996_);
v___y_1962_ = v___y_1996_;
v___y_1963_ = v___y_1997_;
v___y_1964_ = v___y_1998_;
v___y_1965_ = v___y_1999_;
v___y_1966_ = v___y_2000_;
v___y_1967_ = v___y_2001_;
v___y_1968_ = v___y_1996_;
v_eNew_1969_ = v_a_2011_;
v___y_1970_ = v___y_2002_;
v___y_1971_ = v___y_2003_;
v___y_1972_ = v___y_2004_;
v___y_1973_ = v___y_2005_;
goto v___jp_1961_;
}
else
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_del_object(v___x_1732_);
lean_dec(v_fst_1729_);
lean_del_object(v___x_1727_);
lean_dec(v_fst_1725_);
lean_del_object(v___x_1722_);
lean_del_object(v___x_1715_);
lean_dec_ref(v_heq_1672_);
lean_dec(v___x_1671_);
lean_dec(v_mvarId_1670_);
v_a_2012_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_2010_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_2010_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
}
v___jp_2020_:
{
lean_object* v___x_2029_; lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2124_; 
v___x_2029_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(v_e_1673_, v___y_2026_);
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2032_ = v___x_2029_;
v_isShared_2033_ = v_isSharedCheck_2124_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2029_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2124_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
uint8_t v_transparency_2034_; uint8_t v_offsetCnstrs_2035_; lean_object* v_occs_2036_; lean_object* v___x_2037_; uint8_t v_foApprox_2038_; uint8_t v_ctxApprox_2039_; uint8_t v_quasiPatternApprox_2040_; uint8_t v_constApprox_2041_; uint8_t v_isDefEqStuckEx_2042_; uint8_t v_unificationHints_2043_; uint8_t v_proofIrrelevance_2044_; uint8_t v_assignSyntheticOpaque_2045_; uint8_t v_etaStruct_2046_; uint8_t v_univApprox_2047_; uint8_t v_iota_2048_; uint8_t v_beta_2049_; uint8_t v_proj_2050_; uint8_t v_zeta_2051_; uint8_t v_zetaDelta_2052_; uint8_t v_zetaUnused_2053_; uint8_t v_zetaHave_2054_; uint8_t v_canUnfoldPredicateConfig_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2123_; 
v_transparency_2034_ = lean_ctor_get_uint8(v_config_1674_, sizeof(void*)*1);
v_offsetCnstrs_2035_ = lean_ctor_get_uint8(v_config_1674_, sizeof(void*)*1 + 1);
v_occs_2036_ = lean_ctor_get(v_config_1674_, 0);
lean_inc(v_occs_2036_);
lean_dec_ref(v_config_1674_);
v___x_2037_ = l_Lean_Meta_Context_config(v___y_2025_);
v_foApprox_2038_ = lean_ctor_get_uint8(v___x_2037_, 0);
v_ctxApprox_2039_ = lean_ctor_get_uint8(v___x_2037_, 1);
v_quasiPatternApprox_2040_ = lean_ctor_get_uint8(v___x_2037_, 2);
v_constApprox_2041_ = lean_ctor_get_uint8(v___x_2037_, 3);
v_isDefEqStuckEx_2042_ = lean_ctor_get_uint8(v___x_2037_, 4);
v_unificationHints_2043_ = lean_ctor_get_uint8(v___x_2037_, 5);
v_proofIrrelevance_2044_ = lean_ctor_get_uint8(v___x_2037_, 6);
v_assignSyntheticOpaque_2045_ = lean_ctor_get_uint8(v___x_2037_, 7);
v_etaStruct_2046_ = lean_ctor_get_uint8(v___x_2037_, 10);
v_univApprox_2047_ = lean_ctor_get_uint8(v___x_2037_, 11);
v_iota_2048_ = lean_ctor_get_uint8(v___x_2037_, 12);
v_beta_2049_ = lean_ctor_get_uint8(v___x_2037_, 13);
v_proj_2050_ = lean_ctor_get_uint8(v___x_2037_, 14);
v_zeta_2051_ = lean_ctor_get_uint8(v___x_2037_, 15);
v_zetaDelta_2052_ = lean_ctor_get_uint8(v___x_2037_, 16);
v_zetaUnused_2053_ = lean_ctor_get_uint8(v___x_2037_, 17);
v_zetaHave_2054_ = lean_ctor_get_uint8(v___x_2037_, 18);
v_canUnfoldPredicateConfig_2055_ = lean_ctor_get_uint8(v___x_2037_, 19);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2057_ = v___x_2037_;
v_isShared_2058_ = v_isSharedCheck_2123_;
goto v_resetjp_2056_;
}
else
{
lean_dec(v___x_2037_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2123_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
uint8_t v_trackZetaDelta_2059_; lean_object* v_zetaDeltaSet_2060_; lean_object* v_lctx_2061_; lean_object* v_localInstances_2062_; lean_object* v_defEqCtx_x3f_2063_; lean_object* v_synthPendingDepth_2064_; lean_object* v_customCanUnfoldPredicate_x3f_2065_; uint8_t v_univApprox_2066_; uint8_t v_inTypeClassResolution_2067_; uint8_t v_cacheInferType_2068_; lean_object* v___x_2070_; 
v_trackZetaDelta_2059_ = lean_ctor_get_uint8(v___y_2025_, sizeof(void*)*7);
v_zetaDeltaSet_2060_ = lean_ctor_get(v___y_2025_, 1);
v_lctx_2061_ = lean_ctor_get(v___y_2025_, 2);
v_localInstances_2062_ = lean_ctor_get(v___y_2025_, 3);
v_defEqCtx_x3f_2063_ = lean_ctor_get(v___y_2025_, 4);
v_synthPendingDepth_2064_ = lean_ctor_get(v___y_2025_, 5);
v_customCanUnfoldPredicate_x3f_2065_ = lean_ctor_get(v___y_2025_, 6);
v_univApprox_2066_ = lean_ctor_get_uint8(v___y_2025_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2067_ = lean_ctor_get_uint8(v___y_2025_, sizeof(void*)*7 + 2);
v_cacheInferType_2068_ = lean_ctor_get_uint8(v___y_2025_, sizeof(void*)*7 + 3);
if (v_isShared_2058_ == 0)
{
v___x_2070_ = v___x_2057_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2122_, 0, v_foApprox_2038_);
lean_ctor_set_uint8(v_reuseFailAlloc_2122_, 1, v_ctxApprox_2039_);
lean_ctor_set_uint8(v_reuseFailAlloc_2122_, 2, v_quasiPatternApprox_2040_);
lean_ctor_set_uint8(v_reuseFailAlloc_2122_, 3, v_constApprox_2041_);
lean_ctor_set_uint8(v_reuseFailAlloc_2122_, 4, v_isDefEqStuckEx_2042_);
lean_ctor_set_uint8(v_reuseFailAlloc_2122_, 5, v_unificationHints_2043_);
lean_ctor_set_uint8(v_reuseFailAlloc_2122_, 6, v_proofIrrelevance_2044_);
lean_ctor_set_uint8(v_reuseFailAlloc_2122_, 7, v_assignSyntheticOpaque_2045_);
lean_ctor_set_uint8(v_reuseFailAlloc_2122_, 10, v_etaStruct_2046_);
lean_ctor_set_uint8(v_reuseFailAlloc_2122_, 11, v_univApprox_2047_);
lean_ctor_set_uint8(v_reuseFailAlloc_2122_, 12, v_iota_2048_);
lean_ctor_set_uint8(v_reuseFailAlloc_2122_, 13, v_beta_2049_);
lean_ctor_set_uint8(v_reuseFailAlloc_2122_, 14, v_proj_2050_);
lean_ctor_set_uint8(v_reuseFailAlloc_2122_, 15, v_zeta_2051_);
lean_ctor_set_uint8(v_reuseFailAlloc_2122_, 16, v_zetaDelta_2052_);
lean_ctor_set_uint8(v_reuseFailAlloc_2122_, 17, v_zetaUnused_2053_);
lean_ctor_set_uint8(v_reuseFailAlloc_2122_, 18, v_zetaHave_2054_);
lean_ctor_set_uint8(v_reuseFailAlloc_2122_, 19, v_canUnfoldPredicateConfig_2055_);
v___x_2070_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
uint64_t v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
lean_ctor_set_uint8(v___x_2070_, 8, v_offsetCnstrs_2035_);
lean_ctor_set_uint8(v___x_2070_, 9, v_transparency_2034_);
v___x_2071_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2070_);
v___x_2072_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2072_, 0, v___x_2070_);
lean_ctor_set_uint64(v___x_2072_, sizeof(void*)*1, v___x_2071_);
lean_inc(v_customCanUnfoldPredicate_x3f_2065_);
lean_inc(v_synthPendingDepth_2064_);
lean_inc(v_defEqCtx_x3f_2063_);
lean_inc_ref(v_localInstances_2062_);
lean_inc_ref(v_lctx_2061_);
lean_inc(v_zetaDeltaSet_2060_);
v___x_2073_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2073_, 0, v___x_2072_);
lean_ctor_set(v___x_2073_, 1, v_zetaDeltaSet_2060_);
lean_ctor_set(v___x_2073_, 2, v_lctx_2061_);
lean_ctor_set(v___x_2073_, 3, v_localInstances_2062_);
lean_ctor_set(v___x_2073_, 4, v_defEqCtx_x3f_2063_);
lean_ctor_set(v___x_2073_, 5, v_synthPendingDepth_2064_);
lean_ctor_set(v___x_2073_, 6, v_customCanUnfoldPredicate_x3f_2065_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*7, v_trackZetaDelta_2059_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*7 + 1, v_univApprox_2066_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2067_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*7 + 3, v_cacheInferType_2068_);
lean_inc_ref(v___y_2022_);
lean_inc(v_a_2030_);
v___x_2074_ = l_Lean_Meta_kabstract(v_a_2030_, v___y_2022_, v_occs_2036_, v___x_2073_, v___y_2026_, v___y_2027_, v___y_2028_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; uint8_t v___x_2076_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2075_);
lean_dec_ref_known(v___x_2074_, 1);
v___x_2076_ = l_Lean_Expr_hasLooseBVars(v_a_2075_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; 
lean_inc_ref(v___y_2022_);
lean_inc(v_a_2030_);
v___x_2077_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_2030_, v___y_2022_, v___x_2073_, v___y_2026_, v___y_2027_, v___y_2028_);
lean_dec_ref_known(v___x_2073_, 7);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; lean_object* v_fst_2079_; lean_object* v_snd_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2105_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2078_);
lean_dec_ref_known(v___x_2077_, 1);
v_fst_2079_ = lean_ctor_get(v_a_2078_, 0);
v_snd_2080_ = lean_ctor_get(v_a_2078_, 1);
v_isSharedCheck_2105_ = !lean_is_exclusive(v_a_2078_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2082_ = v_a_2078_;
v_isShared_2083_ = v_isSharedCheck_2105_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_snd_2080_);
lean_inc(v_fst_2079_);
lean_dec(v_a_2078_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2105_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2087_; 
v___x_2084_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__31, &l_Lean_MVarId_rewrite___lam__1___closed__31_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__31);
v___x_2085_ = l_Lean_indentExpr(v_snd_2080_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set_tag(v___x_2082_, 7);
lean_ctor_set(v___x_2082_, 1, v___x_2085_);
lean_ctor_set(v___x_2082_, 0, v___x_2084_);
v___x_2087_ = v___x_2082_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_2084_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v___x_2085_);
v___x_2087_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2093_; 
v___x_2088_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__33, &l_Lean_MVarId_rewrite___lam__1___closed__33_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__33);
v___x_2089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2087_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
v___x_2090_ = l_Lean_indentExpr(v_fst_2079_);
v___x_2091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2089_);
lean_ctor_set(v___x_2091_, 1, v___x_2090_);
if (v_isShared_2033_ == 0)
{
lean_ctor_set_tag(v___x_2032_, 1);
lean_ctor_set(v___x_2032_, 0, v___x_2091_);
v___x_2093_ = v___x_2032_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
lean_object* v___x_2094_; 
lean_inc(v_mvarId_1670_);
lean_inc(v___x_1671_);
v___x_2094_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1671_, v_mvarId_1670_, v___x_2093_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_dec_ref_known(v___x_2094_, 1);
v___y_1996_ = v_a_2075_;
v___y_1997_ = v___y_2021_;
v___y_1998_ = v___y_2022_;
v___y_1999_ = v___y_2023_;
v___y_2000_ = v___y_2024_;
v___y_2001_ = v_a_2030_;
v___y_2002_ = v___y_2025_;
v___y_2003_ = v___y_2026_;
v___y_2004_ = v___y_2027_;
v___y_2005_ = v___y_2028_;
goto v___jp_1995_;
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_dec(v_a_2075_);
lean_dec(v_a_2030_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_del_object(v___x_1732_);
lean_dec(v_fst_1729_);
lean_del_object(v___x_1727_);
lean_dec(v_fst_1725_);
lean_del_object(v___x_1722_);
lean_del_object(v___x_1715_);
lean_dec_ref(v_heq_1672_);
lean_dec(v___x_1671_);
lean_dec(v_mvarId_1670_);
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
lean_dec(v_a_2075_);
lean_del_object(v___x_2032_);
lean_dec(v_a_2030_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_del_object(v___x_1732_);
lean_dec(v_fst_1729_);
lean_del_object(v___x_1727_);
lean_dec(v_fst_1725_);
lean_del_object(v___x_1722_);
lean_del_object(v___x_1715_);
lean_dec_ref(v_heq_1672_);
lean_dec(v___x_1671_);
lean_dec(v_mvarId_1670_);
v_a_2106_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2077_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2077_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2073_, 7);
lean_del_object(v___x_2032_);
v___y_1996_ = v_a_2075_;
v___y_1997_ = v___y_2021_;
v___y_1998_ = v___y_2022_;
v___y_1999_ = v___y_2023_;
v___y_2000_ = v___y_2024_;
v___y_2001_ = v_a_2030_;
v___y_2002_ = v___y_2025_;
v___y_2003_ = v___y_2026_;
v___y_2004_ = v___y_2027_;
v___y_2005_ = v___y_2028_;
goto v___jp_1995_;
}
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
lean_dec_ref_known(v___x_2073_, 7);
lean_del_object(v___x_2032_);
lean_dec(v_a_2030_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_del_object(v___x_1732_);
lean_dec(v_fst_1729_);
lean_del_object(v___x_1727_);
lean_dec(v_fst_1725_);
lean_del_object(v___x_1722_);
lean_del_object(v___x_1715_);
lean_dec_ref(v_heq_1672_);
lean_dec(v___x_1671_);
lean_dec(v_mvarId_1670_);
v_a_2114_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2074_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2074_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
}
}
}
v___jp_2125_:
{
lean_object* v___x_2135_; uint8_t v___x_2136_; 
v___x_2135_ = l_Lean_Expr_getAppFn(v_lhs_2129_);
v___x_2136_ = l_Lean_Expr_isMVar(v___x_2135_);
lean_dec_ref(v___x_2135_);
if (v___x_2136_ == 0)
{
lean_dec_ref(v_heqType_2128_);
v___y_2021_ = v_heq_2127_;
v___y_2022_ = v_lhs_2129_;
v___y_2023_ = v_rhs_2130_;
v___y_2024_ = v___y_2126_;
v___y_2025_ = v___y_2131_;
v___y_2026_ = v___y_2132_;
v___y_2027_ = v___y_2133_;
v___y_2028_ = v___y_2134_;
goto v___jp_2020_;
}
else
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_dec_ref(v_rhs_2130_);
lean_dec_ref(v_heq_2127_);
lean_dec_ref(v___y_2126_);
lean_del_object(v___x_1732_);
lean_dec(v_fst_1729_);
lean_del_object(v___x_1727_);
lean_dec(v_fst_1725_);
lean_del_object(v___x_1722_);
lean_del_object(v___x_1715_);
lean_dec_ref(v_config_1674_);
lean_dec_ref(v_e_1673_);
lean_dec_ref(v_heq_1672_);
lean_dec(v___x_1671_);
lean_dec(v_mvarId_1670_);
v___x_2137_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__35, &l_Lean_MVarId_rewrite___lam__1___closed__35_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__35);
v___x_2138_ = l_Lean_MessageData_ofExpr(v_lhs_2129_);
v___x_2139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2137_);
lean_ctor_set(v___x_2139_, 1, v___x_2138_);
v___x_2140_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__37, &l_Lean_MVarId_rewrite___lam__1___closed__37_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__37);
v___x_2141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2139_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
v___x_2142_ = l_Lean_indentExpr(v_heqType_2128_);
v___x_2143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2141_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(v___x_2143_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2144_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2144_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2145_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
v___jp_2153_:
{
lean_object* v___x_2160_; 
lean_inc_ref(v_heqType_2155_);
v___x_2160_ = l_Lean_Meta_matchEq_x3f(v_heqType_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_a_2161_);
lean_dec_ref_known(v___x_2160_, 1);
if (lean_obj_tag(v_a_2161_) == 0)
{
lean_object* v___x_2162_; 
lean_del_object(v___x_1732_);
lean_dec(v_fst_1729_);
lean_del_object(v___x_1727_);
lean_dec(v_fst_1725_);
lean_del_object(v___x_1722_);
lean_del_object(v___x_1715_);
lean_dec_ref(v_config_1674_);
lean_dec_ref(v_e_1673_);
lean_dec_ref(v_heq_1672_);
lean_dec(v___x_1671_);
lean_dec(v_mvarId_1670_);
lean_inc_ref(v_heqType_2155_);
v___x_2162_ = l_Lean_Meta_isProp(v_heqType_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; uint8_t v___x_2164_; 
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2163_);
lean_dec_ref_known(v___x_2162_, 1);
v___x_2164_ = lean_unbox(v_a_2163_);
lean_dec(v_a_2163_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; 
v___x_2165_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__38));
v___y_1682_ = v___y_2156_;
v___y_1683_ = v_heqType_2155_;
v___y_1684_ = v___y_2159_;
v___y_1685_ = v___y_2158_;
v___y_1686_ = v_heq_2154_;
v___y_1687_ = v___y_2157_;
v___y_1688_ = v___x_2165_;
goto v___jp_1681_;
}
else
{
lean_object* v___x_2166_; 
v___x_2166_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__39));
v___y_1682_ = v___y_2156_;
v___y_1683_ = v_heqType_2155_;
v___y_1684_ = v___y_2159_;
v___y_1685_ = v___y_2158_;
v___y_1686_ = v_heq_2154_;
v___y_1687_ = v___y_2157_;
v___y_1688_ = v___x_2166_;
goto v___jp_1681_;
}
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec_ref(v_heqType_2155_);
lean_dec_ref(v_heq_2154_);
v_a_2167_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2162_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2162_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
else
{
lean_object* v_val_2175_; lean_object* v_snd_2176_; 
v_val_2175_ = lean_ctor_get(v_a_2161_, 0);
lean_inc(v_val_2175_);
lean_dec_ref_known(v_a_2161_, 1);
v_snd_2176_ = lean_ctor_get(v_val_2175_, 1);
lean_inc(v_snd_2176_);
if (v_symm_1675_ == 0)
{
lean_object* v_fst_2177_; lean_object* v_fst_2178_; lean_object* v_snd_2179_; 
v_fst_2177_ = lean_ctor_get(v_val_2175_, 0);
lean_inc(v_fst_2177_);
lean_dec(v_val_2175_);
v_fst_2178_ = lean_ctor_get(v_snd_2176_, 0);
lean_inc(v_fst_2178_);
v_snd_2179_ = lean_ctor_get(v_snd_2176_, 1);
lean_inc(v_snd_2179_);
lean_dec(v_snd_2176_);
v___y_2126_ = v_fst_2177_;
v_heq_2127_ = v_heq_2154_;
v_heqType_2128_ = v_heqType_2155_;
v_lhs_2129_ = v_fst_2178_;
v_rhs_2130_ = v_snd_2179_;
v___y_2131_ = v___y_2156_;
v___y_2132_ = v___y_2157_;
v___y_2133_ = v___y_2158_;
v___y_2134_ = v___y_2159_;
goto v___jp_2125_;
}
else
{
lean_object* v_fst_2180_; lean_object* v_fst_2181_; lean_object* v_snd_2182_; lean_object* v___x_2183_; 
lean_dec_ref(v_heqType_2155_);
v_fst_2180_ = lean_ctor_get(v_val_2175_, 0);
lean_inc(v_fst_2180_);
lean_dec(v_val_2175_);
v_fst_2181_ = lean_ctor_get(v_snd_2176_, 0);
lean_inc(v_fst_2181_);
v_snd_2182_ = lean_ctor_get(v_snd_2176_, 1);
lean_inc(v_snd_2182_);
lean_dec(v_snd_2176_);
v___x_2183_ = l_Lean_Meta_mkEqSymm(v_heq_2154_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v___x_2185_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_a_2184_);
lean_dec_ref_known(v___x_2183_, 1);
lean_inc(v_fst_2181_);
lean_inc(v_snd_2182_);
v___x_2185_ = l_Lean_Meta_mkEq(v_snd_2182_, v_fst_2181_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2186_);
lean_dec_ref_known(v___x_2185_, 1);
v___y_2126_ = v_fst_2180_;
v_heq_2127_ = v_a_2184_;
v_heqType_2128_ = v_a_2186_;
v_lhs_2129_ = v_snd_2182_;
v_rhs_2130_ = v_fst_2181_;
v___y_2131_ = v___y_2156_;
v___y_2132_ = v___y_2157_;
v___y_2133_ = v___y_2158_;
v___y_2134_ = v___y_2159_;
goto v___jp_2125_;
}
else
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2194_; 
lean_dec(v_a_2184_);
lean_dec(v_snd_2182_);
lean_dec(v_fst_2181_);
lean_dec(v_fst_2180_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_del_object(v___x_1732_);
lean_dec(v_fst_1729_);
lean_del_object(v___x_1727_);
lean_dec(v_fst_1725_);
lean_del_object(v___x_1722_);
lean_del_object(v___x_1715_);
lean_dec_ref(v_config_1674_);
lean_dec_ref(v_e_1673_);
lean_dec_ref(v_heq_1672_);
lean_dec(v___x_1671_);
lean_dec(v_mvarId_1670_);
v_a_2187_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2189_ = v___x_2185_;
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2185_);
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
else
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2202_; 
lean_dec(v_snd_2182_);
lean_dec(v_fst_2181_);
lean_dec(v_fst_2180_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_del_object(v___x_1732_);
lean_dec(v_fst_1729_);
lean_del_object(v___x_1727_);
lean_dec(v_fst_1725_);
lean_del_object(v___x_1722_);
lean_del_object(v___x_1715_);
lean_dec_ref(v_config_1674_);
lean_dec_ref(v_e_1673_);
lean_dec_ref(v_heq_1672_);
lean_dec(v___x_1671_);
lean_dec(v_mvarId_1670_);
v_a_2195_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2197_ = v___x_2183_;
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2183_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2200_; 
if (v_isShared_2198_ == 0)
{
v___x_2200_ = v___x_2197_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_a_2195_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
}
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec_ref(v_heqType_2155_);
lean_dec_ref(v_heq_2154_);
lean_del_object(v___x_1732_);
lean_dec(v_fst_1729_);
lean_del_object(v___x_1727_);
lean_dec(v_fst_1725_);
lean_del_object(v___x_1722_);
lean_del_object(v___x_1715_);
lean_dec_ref(v_config_1674_);
lean_dec_ref(v_e_1673_);
lean_dec_ref(v_heq_1672_);
lean_dec(v___x_1671_);
lean_dec(v_mvarId_1670_);
v_a_2203_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2205_ = v___x_2160_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2160_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2203_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
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
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
lean_del_object(v___x_1715_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec_ref(v_config_1674_);
lean_dec_ref(v_e_1673_);
lean_dec_ref(v_heq_1672_);
lean_dec(v___x_1671_);
lean_dec(v_mvarId_1670_);
v_a_2233_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_1719_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_1719_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
}
else
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec_ref(v_config_1674_);
lean_dec_ref(v_e_1673_);
lean_dec_ref(v_heq_1672_);
lean_dec(v___x_1671_);
lean_dec(v_mvarId_1670_);
v_a_2242_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2244_ = v___x_1710_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_1710_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec_ref(v_config_1674_);
lean_dec_ref(v_e_1673_);
lean_dec_ref(v_heq_1672_);
lean_dec(v___x_1671_);
lean_dec(v_mvarId_1670_);
v_a_2250_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_1709_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_1709_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2250_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
v___jp_1681_:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1689_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__1, &l_Lean_MVarId_rewrite___lam__1___closed__1_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__1);
v___x_1690_ = lean_unsigned_to_nat(30u);
v___x_1691_ = l_Lean_inlineExpr(v___y_1686_, v___x_1690_);
v___x_1692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1689_);
lean_ctor_set(v___x_1692_, 1, v___x_1691_);
v___x_1693_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__3, &l_Lean_MVarId_rewrite___lam__1___closed__3_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__3);
v___x_1694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1692_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
lean_inc_ref(v___y_1688_);
v___x_1695_ = l_Lean_stringToMessageData(v___y_1688_);
v___x_1696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1694_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
v___x_1697_ = l_Lean_indentExpr(v___y_1683_);
v___x_1698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1696_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
v___x_1699_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(v___x_1698_, v___y_1682_, v___y_1687_, v___y_1685_, v___y_1684_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1682_);
return v___x_1699_;
}
v___jp_1700_:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1705_ = l_Array_append___redArg(v___y_1702_, v___y_1704_);
lean_dec_ref(v___y_1704_);
v___x_1706_ = lean_array_to_list(v___x_1705_);
v___x_1707_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1707_, 0, v___y_1703_);
lean_ctor_set(v___x_1707_, 1, v___y_1701_);
lean_ctor_set(v___x_1707_, 2, v___x_1706_);
v___x_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
return v___x_1708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1___boxed(lean_object* v_mvarId_2258_, lean_object* v___x_2259_, lean_object* v_heq_2260_, lean_object* v_e_2261_, lean_object* v_config_2262_, lean_object* v_symm_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
uint8_t v_symm_boxed_2269_; lean_object* v_res_2270_; 
v_symm_boxed_2269_ = lean_unbox(v_symm_2263_);
v_res_2270_ = l_Lean_MVarId_rewrite___lam__1(v_mvarId_2258_, v___x_2259_, v_heq_2260_, v_e_2261_, v_config_2262_, v_symm_boxed_2269_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite(lean_object* v_mvarId_2274_, lean_object* v_e_2275_, lean_object* v_heq_2276_, uint8_t v_symm_2277_, lean_object* v_config_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_){
_start:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___f_2286_; lean_object* v___x_2287_; 
v___x_2284_ = ((lean_object*)(l_Lean_MVarId_rewrite___closed__1));
v___x_2285_ = lean_box(v_symm_2277_);
lean_inc(v_mvarId_2274_);
v___f_2286_ = lean_alloc_closure((void*)(l_Lean_MVarId_rewrite___lam__1___boxed), 11, 6);
lean_closure_set(v___f_2286_, 0, v_mvarId_2274_);
lean_closure_set(v___f_2286_, 1, v___x_2284_);
lean_closure_set(v___f_2286_, 2, v_heq_2276_);
lean_closure_set(v___f_2286_, 3, v_e_2275_);
lean_closure_set(v___f_2286_, 4, v_config_2278_);
lean_closure_set(v___f_2286_, 5, v___x_2285_);
v___x_2287_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__8___redArg(v_mvarId_2274_, v___f_2286_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___boxed(lean_object* v_mvarId_2288_, lean_object* v_e_2289_, lean_object* v_heq_2290_, lean_object* v_symm_2291_, lean_object* v_config_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_){
_start:
{
uint8_t v_symm_boxed_2298_; lean_object* v_res_2299_; 
v_symm_boxed_2298_ = lean_unbox(v_symm_2291_);
v_res_2299_ = l_Lean_MVarId_rewrite(v_mvarId_2288_, v_e_2289_, v_heq_2290_, v_symm_boxed_2298_, v_config_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
lean_dec(v_a_2294_);
lean_dec_ref(v_a_2293_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0(lean_object* v_mvarId_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v___x_2306_; 
v___x_2306_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(v_mvarId_2300_, v___y_2302_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___boxed(lean_object* v_mvarId_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0(v_mvarId_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v_mvarId_2307_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2(lean_object* v_00_u03b1_2314_, lean_object* v_msg_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v___x_2321_; 
v___x_2321_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(v_msg_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___boxed(lean_object* v_00_u03b1_2322_, lean_object* v_msg_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2(v_00_u03b1_2322_, v_msg_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
return v_res_2329_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0(lean_object* v_00_u03b2_2330_, lean_object* v_x_2331_, lean_object* v_x_2332_){
_start:
{
uint8_t v___x_2333_; 
v___x_2333_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(v_x_2331_, v_x_2332_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2334_, lean_object* v_x_2335_, lean_object* v_x_2336_){
_start:
{
uint8_t v_res_2337_; lean_object* v_r_2338_; 
v_res_2337_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0(v_00_u03b2_2334_, v_x_2335_, v_x_2336_);
lean_dec(v_x_2336_);
lean_dec_ref(v_x_2335_);
v_r_2338_ = lean_box(v_res_2337_);
return v_r_2338_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_2339_, lean_object* v_x_2340_, size_t v_x_2341_, lean_object* v_x_2342_){
_start:
{
uint8_t v___x_2343_; 
v___x_2343_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(v_x_2340_, v_x_2341_, v_x_2342_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_2344_, lean_object* v_x_2345_, lean_object* v_x_2346_, lean_object* v_x_2347_){
_start:
{
size_t v_x_19447__boxed_2348_; uint8_t v_res_2349_; lean_object* v_r_2350_; 
v_x_19447__boxed_2348_ = lean_unbox_usize(v_x_2346_);
lean_dec(v_x_2346_);
v_res_2349_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4(v_00_u03b2_2344_, v_x_2345_, v_x_19447__boxed_2348_, v_x_2347_);
lean_dec(v_x_2347_);
lean_dec_ref(v_x_2345_);
v_r_2350_ = lean_box(v_res_2349_);
return v_r_2350_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__10(lean_object* v_00_u03b2_2351_, lean_object* v_keys_2352_, lean_object* v_vals_2353_, lean_object* v_heq_2354_, lean_object* v_i_2355_, lean_object* v_k_2356_){
_start:
{
uint8_t v___x_2357_; 
v___x_2357_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__10___redArg(v_keys_2352_, v_i_2355_, v_k_2356_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_00_u03b2_2358_, lean_object* v_keys_2359_, lean_object* v_vals_2360_, lean_object* v_heq_2361_, lean_object* v_i_2362_, lean_object* v_k_2363_){
_start:
{
uint8_t v_res_2364_; lean_object* v_r_2365_; 
v_res_2364_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__10(v_00_u03b2_2358_, v_keys_2359_, v_vals_2360_, v_heq_2361_, v_i_2362_, v_k_2363_);
lean_dec(v_k_2363_);
lean_dec_ref(v_vals_2360_);
lean_dec_ref(v_keys_2359_);
v_r_2365_ = lean_box(v_res_2364_);
return v_r_2365_;
}
}
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_MatchUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_KAbstract(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_BinderNameHint(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_MatchUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_KAbstract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_BinderNameHint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_MatchUtil(uint8_t builtin);
lean_object* initialize_Lean_Meta_KAbstract(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* initialize_Lean_Meta_BinderNameHint(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_MatchUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_KAbstract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_BinderNameHint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Rewrite(builtin);
}
#ifdef __cplusplus
}
#endif
