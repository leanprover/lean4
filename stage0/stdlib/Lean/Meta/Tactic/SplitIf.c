// Lean compiler output
// Module: Lean.Meta.Tactic.SplitIf
// Imports: public import Lean.Meta.Tactic.Cases public import Lean.Meta.Tactic.Simp.Rewrite import Lean.Meta.Tactic.Simp.Main
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_num_indices(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_mkPtrSet___redArg(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isExplicit(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isMatcherAppCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
lean_object* l_Lean_Expr_getBoundedAppFn(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isIte(lean_object*);
uint8_t l_Lean_Expr_isDIte(lean_object*);
lean_object* l_Lean_MVarId_byCasesDec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
extern lean_object* l_Lean_Meta_Simp_neutralConfig;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* lean_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Simprocs_addCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheorems_addConst(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpTarget(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instHashablePtr___lam__0___boxed(lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ite_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ite_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ite_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ite_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_match_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_match_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_match_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_match_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_both_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_both_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_both_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_both_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SplitKind_considerIte(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_considerIte___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SplitKind_considerMatch(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_considerMatch___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__1_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashablePtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___closed__0_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___closed__0_value),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___closed__0_value)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "split"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 90, 54, 167, 41, 130, 106, 252)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(146, 27, 182, 221, 54, 36, 194, 80)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "candidate:"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "backward"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 7, 10, 91, 49, 15, 80, 52)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 103, .m_capacity = 103, .m_length = 102, .m_data = "use the old semantics for the `split` tactic where nested `if-then-else` terms could be simplified too"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(32, 38, 242, 87, 165, 12, 140, 145)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(102, 141, 87, 76, 47, 100, 236, 116)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_backward_split;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1(lean_object*);
static lean_once_cell_t l_Lean_Meta_SplitIf_getSimpContext___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__0;
static lean_once_cell_t l_Lean_Meta_SplitIf_getSimpContext___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__1;
static lean_once_cell_t l_Lean_Meta_SplitIf_getSimpContext___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__2;
static lean_once_cell_t l_Lean_Meta_SplitIf_getSimpContext___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__3;
static lean_once_cell_t l_Lean_Meta_SplitIf_getSimpContext___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__4;
static lean_once_cell_t l_Lean_Meta_SplitIf_getSimpContext___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__5;
static const lean_string_object l_Lean_Meta_SplitIf_getSimpContext___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "if_pos"};
static const lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__6 = (const lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__6_value;
static const lean_ctor_object l_Lean_Meta_SplitIf_getSimpContext___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__6_value),LEAN_SCALAR_PTR_LITERAL(242, 79, 136, 209, 251, 93, 254, 106)}};
static const lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__7 = (const lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__7_value;
static const lean_string_object l_Lean_Meta_SplitIf_getSimpContext___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "if_neg"};
static const lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__8 = (const lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__8_value;
static const lean_ctor_object l_Lean_Meta_SplitIf_getSimpContext___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__8_value),LEAN_SCALAR_PTR_LITERAL(94, 43, 105, 241, 236, 232, 111, 225)}};
static const lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__9 = (const lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__9_value;
static const lean_string_object l_Lean_Meta_SplitIf_getSimpContext___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "dif_pos"};
static const lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__10 = (const lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__10_value;
static const lean_ctor_object l_Lean_Meta_SplitIf_getSimpContext___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__10_value),LEAN_SCALAR_PTR_LITERAL(38, 147, 143, 206, 51, 9, 8, 80)}};
static const lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__11 = (const lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__11_value;
static const lean_string_object l_Lean_Meta_SplitIf_getSimpContext___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "dif_neg"};
static const lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__12 = (const lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__12_value;
static const lean_ctor_object l_Lean_Meta_SplitIf_getSimpContext___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__12_value),LEAN_SCALAR_PTR_LITERAL(184, 114, 55, 245, 8, 138, 156, 111)}};
static const lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__13 = (const lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_getSimpContext(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_getSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "not_not_intro"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(141, 174, 41, 152, 198, 172, 7, 80)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "of_decide_eq_true"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(199, 143, 142, 104, 169, 34, 63, 25)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "splitIf"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(181, 95, 169, 53, 171, 116, 20, 182)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "discharge\? "};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__15;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "<not-available>"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__16_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__18;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__1_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ite_cond_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__4_value),LEAN_SCALAR_PTR_LITERAL(9, 208, 77, 228, 243, 158, 228, 162)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mpr_prop"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__1_value),LEAN_SCALAR_PTR_LITERAL(169, 177, 76, 157, 211, 15, 217, 219)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mpr_not"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__5_value),LEAN_SCALAR_PTR_LITERAL(121, 56, 250, 51, 9, 123, 141, 181)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "dite_cond_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__8_value),LEAN_SCALAR_PTR_LITERAL(124, 27, 93, 224, 42, 131, 56, 201)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__2_value),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__2_value;
static const lean_array_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__5_value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__6_value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__7_value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "SplitIf"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__8_value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(76, 221, 255, 40, 254, 93, 36, 145)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(77, 67, 39, 96, 166, 188, 81, 166)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__11_value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(56, 202, 4, 90, 23, 96, 207, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__12_value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(148, 235, 194, 225, 124, 161, 64, 247)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__13_value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(167, 120, 249, 182, 103, 12, 98, 131)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reduceIte'"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__14_value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(244, 195, 180, 159, 75, 12, 135, 86)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__4_value),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__17_value;
static const lean_array_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "reduceDIte'"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__14_value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__19_value),LEAN_SCALAR_PTR_LITERAL(167, 195, 231, 206, 69, 191, 167, 198)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "splitting on "};
static const lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1;
static const lean_string_object l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "could not find if to split:"};
static const lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_simpIfTarget_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_simpIfTarget_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_simpIfTarget_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_simpIfTarget_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_simpIfTarget_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_simpIfTarget___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_simpIfTarget___closed__0;
static lean_once_cell_t l_Lean_Meta_simpIfTarget___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_simpIfTarget___closed__1;
static lean_once_cell_t l_Lean_Meta_simpIfTarget___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_simpIfTarget___closed__2;
static lean_once_cell_t l_Lean_Meta_simpIfTarget___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_simpIfTarget___closed__3;
static lean_once_cell_t l_Lean_Meta_simpIfTarget___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_simpIfTarget___closed__4;
static lean_once_cell_t l_Lean_Meta_simpIfTarget___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_simpIfTarget___closed__5;
static lean_once_cell_t l_Lean_Meta_simpIfTarget___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_simpIfTarget___closed__6;
static const lean_string_object l_Lean_Meta_simpIfTarget___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Meta.Tactic.SplitIf"};
static const lean_object* l_Lean_Meta_simpIfTarget___closed__7 = (const lean_object*)&l_Lean_Meta_simpIfTarget___closed__7_value;
static const lean_string_object l_Lean_Meta_simpIfTarget___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.simpIfTarget"};
static const lean_object* l_Lean_Meta_simpIfTarget___closed__8 = (const lean_object*)&l_Lean_Meta_simpIfTarget___closed__8_value;
static const lean_string_object l_Lean_Meta_simpIfTarget___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Meta_simpIfTarget___closed__9 = (const lean_object*)&l_Lean_Meta_simpIfTarget___closed__9_value;
static lean_once_cell_t l_Lean_Meta_simpIfTarget___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_simpIfTarget___closed__10;
static const lean_array_object l_Lean_Meta_simpIfTarget___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_simpIfTarget___closed__11 = (const lean_object*)&l_Lean_Meta_simpIfTarget___closed__11_value;
static lean_once_cell_t l_Lean_Meta_simpIfTarget___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_simpIfTarget___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfTarget(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_simpIfLocalDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.simpIfLocalDecl"};
static const lean_object* l_Lean_Meta_simpIfLocalDecl___closed__0 = (const lean_object*)&l_Lean_Meta_simpIfLocalDecl___closed__0_value;
static lean_once_cell_t l_Lean_Meta_simpIfLocalDecl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_simpIfLocalDecl___closed__1;
static lean_once_cell_t l_Lean_Meta_simpIfLocalDecl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_simpIfLocalDecl___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfLocalDecl(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "failure"};
static const lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 90, 54, 167, 41, 130, 106, 252)}};
static const lean_ctor_object l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 82, 27, 41, 121, 237, 120, 228)}};
static const lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2;
static const lean_string_object l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "`split` tactic failed to simplify target using new hypotheses Goals:\n"};
static const lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4;
static const lean_string_object l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__13_value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(81, 137, 76, 163, 76, 115, 6, 53)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(60, 24, 105, 171, 156, 89, 145, 146)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(221, 224, 164, 228, 171, 225, 60, 201)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(181, 248, 17, 89, 207, 85, 0, 88)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(140, 203, 248, 13, 200, 236, 3, 225)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(79, 37, 36, 7, 71, 199, 210, 30)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Meta_SplitKind_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Meta_SplitKind_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Lean_Meta_SplitKind_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Meta_SplitKind_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Lean_Meta_SplitKind_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ite_elim___redArg(lean_object* v_ite_28_){
_start:
{
lean_inc(v_ite_28_);
return v_ite_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ite_elim___redArg___boxed(lean_object* v_ite_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Meta_SplitKind_ite_elim___redArg(v_ite_29_);
lean_dec(v_ite_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ite_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_ite_34_){
_start:
{
lean_inc(v_ite_34_);
return v_ite_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ite_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_ite_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Lean_Meta_SplitKind_ite_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_ite_38_);
lean_dec(v_ite_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_match_elim___redArg(lean_object* v_match_41_){
_start:
{
lean_inc(v_match_41_);
return v_match_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_match_elim___redArg___boxed(lean_object* v_match_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Meta_SplitKind_match_elim___redArg(v_match_42_);
lean_dec(v_match_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_match_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_match_47_){
_start:
{
lean_inc(v_match_47_);
return v_match_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_match_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_match_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Lean_Meta_SplitKind_match_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_match_51_);
lean_dec(v_match_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_both_elim___redArg(lean_object* v_both_54_){
_start:
{
lean_inc(v_both_54_);
return v_both_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_both_elim___redArg___boxed(lean_object* v_both_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Meta_SplitKind_both_elim___redArg(v_both_55_);
lean_dec(v_both_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_both_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_both_60_){
_start:
{
lean_inc(v_both_60_);
return v_both_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_both_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_both_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Lean_Meta_SplitKind_both_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_both_64_);
lean_dec(v_both_64_);
return v_res_66_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SplitKind_considerIte(uint8_t v_x_67_){
_start:
{
switch(v_x_67_)
{
case 0:
{
uint8_t v___x_68_; 
v___x_68_ = 1;
return v___x_68_;
}
case 2:
{
uint8_t v___x_69_; 
v___x_69_ = 1;
return v___x_69_;
}
default: 
{
uint8_t v___x_70_; 
v___x_70_ = 0;
return v___x_70_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_considerIte___boxed(lean_object* v_x_71_){
_start:
{
uint8_t v_x_26__boxed_72_; uint8_t v_res_73_; lean_object* v_r_74_; 
v_x_26__boxed_72_ = lean_unbox(v_x_71_);
v_res_73_ = l_Lean_Meta_SplitKind_considerIte(v_x_26__boxed_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SplitKind_considerMatch(uint8_t v_x_75_){
_start:
{
switch(v_x_75_)
{
case 1:
{
uint8_t v___x_76_; 
v___x_76_ = 1;
return v___x_76_;
}
case 2:
{
uint8_t v___x_77_; 
v___x_77_ = 1;
return v___x_77_;
}
default: 
{
uint8_t v___x_78_; 
v___x_78_ = 0;
return v___x_78_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_considerMatch___boxed(lean_object* v_x_79_){
_start:
{
uint8_t v_x_26__boxed_80_; uint8_t v_res_81_; lean_object* v_r_82_; 
v_x_26__boxed_80_ = lean_unbox(v_x_79_);
v_res_81_ = l_Lean_Meta_SplitKind_considerMatch(v_x_26__boxed_80_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg(lean_object* v_a_83_, lean_object* v_x_84_){
_start:
{
if (lean_obj_tag(v_x_84_) == 0)
{
uint8_t v___x_85_; 
v___x_85_ = 0;
return v___x_85_;
}
else
{
lean_object* v_key_86_; lean_object* v_tail_87_; uint8_t v___x_88_; 
v_key_86_ = lean_ctor_get(v_x_84_, 0);
v_tail_87_ = lean_ctor_get(v_x_84_, 2);
v___x_88_ = lean_expr_eqv(v_key_86_, v_a_83_);
if (v___x_88_ == 0)
{
v_x_84_ = v_tail_87_;
goto _start;
}
else
{
return v___x_88_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_90_, lean_object* v_x_91_){
_start:
{
uint8_t v_res_92_; lean_object* v_r_93_; 
v_res_92_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg(v_a_90_, v_x_91_);
lean_dec(v_x_91_);
lean_dec_ref(v_a_90_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(lean_object* v_m_94_, lean_object* v_a_95_){
_start:
{
lean_object* v_buckets_96_; lean_object* v___x_97_; uint64_t v___x_98_; uint64_t v___x_99_; uint64_t v___x_100_; uint64_t v_fold_101_; uint64_t v___x_102_; uint64_t v___x_103_; uint64_t v___x_104_; size_t v___x_105_; size_t v___x_106_; size_t v___x_107_; size_t v___x_108_; size_t v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v_buckets_96_ = lean_ctor_get(v_m_94_, 1);
v___x_97_ = lean_array_get_size(v_buckets_96_);
v___x_98_ = l_Lean_Expr_hash(v_a_95_);
v___x_99_ = 32ULL;
v___x_100_ = lean_uint64_shift_right(v___x_98_, v___x_99_);
v_fold_101_ = lean_uint64_xor(v___x_98_, v___x_100_);
v___x_102_ = 16ULL;
v___x_103_ = lean_uint64_shift_right(v_fold_101_, v___x_102_);
v___x_104_ = lean_uint64_xor(v_fold_101_, v___x_103_);
v___x_105_ = lean_uint64_to_usize(v___x_104_);
v___x_106_ = lean_usize_of_nat(v___x_97_);
v___x_107_ = ((size_t)1ULL);
v___x_108_ = lean_usize_sub(v___x_106_, v___x_107_);
v___x_109_ = lean_usize_land(v___x_105_, v___x_108_);
v___x_110_ = lean_array_uget_borrowed(v_buckets_96_, v___x_109_);
v___x_111_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg(v_a_95_, v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg___boxed(lean_object* v_m_112_, lean_object* v_a_113_){
_start:
{
uint8_t v_res_114_; lean_object* v_r_115_; 
v_res_114_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(v_m_112_, v_a_113_);
lean_dec_ref(v_a_113_);
lean_dec_ref(v_m_112_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg(lean_object* v_upperBound_124_, lean_object* v_args_125_, lean_object* v_a_126_, lean_object* v_b_127_){
_start:
{
uint8_t v___x_128_; 
v___x_128_ = lean_nat_dec_lt(v_a_126_, v_upperBound_124_);
if (v___x_128_ == 0)
{
lean_dec(v_a_126_);
lean_inc_ref(v_b_127_);
return v_b_127_;
}
else
{
lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_129_ = l_Lean_instInhabitedExpr;
v___x_130_ = lean_array_get_borrowed(v___x_129_, v_args_125_, v_a_126_);
v___x_131_ = l_Lean_Expr_hasLooseBVars(v___x_130_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_132_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0));
v___x_133_ = lean_unsigned_to_nat(1u);
v___x_134_ = lean_nat_add(v_a_126_, v___x_133_);
lean_dec(v_a_126_);
v_a_126_ = v___x_134_;
v_b_127_ = v___x_132_;
goto _start;
}
else
{
lean_object* v___x_136_; 
lean_dec(v_a_126_);
v___x_136_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__2));
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___boxed(lean_object* v_upperBound_137_, lean_object* v_args_138_, lean_object* v_a_139_, lean_object* v_b_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg(v_upperBound_137_, v_args_138_, v_a_139_, v_b_140_);
lean_dec_ref(v_b_140_);
lean_dec_ref(v_args_138_);
lean_dec(v_upperBound_137_);
return v_res_141_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0(void){
_start:
{
lean_object* v___x_142_; lean_object* v_dummy_143_; 
v___x_142_ = lean_box(0);
v_dummy_143_ = l_Lean_Expr_sort___override(v___x_142_);
return v_dummy_143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f(lean_object* v_env_150_, lean_object* v_ctx_151_, lean_object* v_e_152_){
_start:
{
lean_object* v_exceptionSet_153_; uint8_t v_kind_154_; lean_object* v_e_156_; lean_object* v___y_184_; lean_object* v___y_185_; uint8_t v___y_186_; uint8_t v___x_197_; 
v_exceptionSet_153_ = lean_ctor_get(v_ctx_151_, 0);
v_kind_154_ = lean_ctor_get_uint8(v_ctx_151_, sizeof(void*)*1);
v___x_197_ = l_Lean_Meta_SplitKind_considerIte(v_kind_154_);
if (v___x_197_ == 0)
{
goto v___jp_160_;
}
else
{
lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_198_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__2));
v___x_199_ = l_Lean_Expr_isAppOf(v_e_152_, v___x_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_200_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__4));
v___x_201_ = l_Lean_Expr_isAppOf(v_e_152_, v___x_200_);
if (v___x_201_ == 0)
{
goto v___jp_160_;
}
else
{
goto v___jp_189_;
}
}
else
{
goto v___jp_189_;
}
}
v___jp_155_:
{
uint8_t v___x_157_; 
v___x_157_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(v_exceptionSet_153_, v_e_156_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; 
v___x_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_158_, 0, v_e_156_);
return v___x_158_;
}
else
{
lean_object* v___x_159_; 
lean_dec_ref(v_e_156_);
v___x_159_ = lean_box(0);
return v___x_159_;
}
}
v___jp_160_:
{
uint8_t v___x_161_; 
v___x_161_ = l_Lean_Meta_SplitKind_considerMatch(v_kind_154_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; 
lean_dec_ref(v_e_152_);
lean_dec_ref(v_env_150_);
v___x_162_ = lean_box(0);
return v___x_162_;
}
else
{
lean_object* v___x_163_; 
v___x_163_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_150_, v_e_152_);
if (lean_obj_tag(v___x_163_) == 1)
{
lean_object* v_val_164_; lean_object* v_numDiscrs_165_; lean_object* v_nargs_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v_dummy_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v_args_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v_fst_176_; 
v_val_164_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_val_164_);
lean_dec_ref_known(v___x_163_, 1);
v_numDiscrs_165_ = lean_ctor_get(v_val_164_, 1);
v_nargs_166_ = l_Lean_Expr_getAppNumArgs(v_e_152_);
v___x_167_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_164_);
v___x_168_ = lean_nat_add(v___x_167_, v_numDiscrs_165_);
v_dummy_169_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0);
lean_inc(v_nargs_166_);
v___x_170_ = lean_mk_array(v_nargs_166_, v_dummy_169_);
v___x_171_ = lean_unsigned_to_nat(1u);
v___x_172_ = lean_nat_sub(v_nargs_166_, v___x_171_);
lean_dec(v_nargs_166_);
lean_inc_ref(v_e_152_);
v_args_173_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_152_, v___x_170_, v___x_172_);
v___x_174_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0));
v___x_175_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg(v___x_168_, v_args_173_, v___x_167_, v___x_174_);
lean_dec(v___x_168_);
v_fst_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_fst_176_);
lean_dec_ref(v___x_175_);
if (lean_obj_tag(v_fst_176_) == 0)
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_177_ = lean_array_get_size(v_args_173_);
lean_dec_ref(v_args_173_);
v___x_178_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_164_);
lean_dec(v_val_164_);
v___x_179_ = lean_nat_sub(v___x_177_, v___x_178_);
lean_dec(v___x_178_);
v___x_180_ = l_Lean_Expr_getBoundedAppFn(v___x_179_, v_e_152_);
lean_dec_ref(v_e_152_);
v_e_156_ = v___x_180_;
goto v___jp_155_;
}
else
{
lean_object* v_val_181_; 
lean_dec_ref(v_args_173_);
lean_dec(v_val_164_);
lean_dec_ref(v_e_152_);
v_val_181_ = lean_ctor_get(v_fst_176_, 0);
lean_inc(v_val_181_);
lean_dec_ref_known(v_fst_176_, 1);
return v_val_181_;
}
}
else
{
lean_object* v___x_182_; 
lean_dec(v___x_163_);
lean_dec_ref(v_e_152_);
v___x_182_ = lean_box(0);
return v___x_182_;
}
}
}
v___jp_183_:
{
if (v___y_186_ == 0)
{
lean_dec(v___y_185_);
goto v___jp_160_;
}
else
{
lean_object* v___x_187_; lean_object* v___x_188_; 
lean_dec_ref(v_env_150_);
v___x_187_ = lean_nat_sub(v___y_185_, v___y_184_);
lean_dec(v___y_185_);
v___x_188_ = l_Lean_Expr_getBoundedAppFn(v___x_187_, v_e_152_);
lean_dec_ref(v_e_152_);
v_e_156_ = v___x_188_;
goto v___jp_155_;
}
}
v___jp_189_:
{
lean_object* v_numArgs_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v_numArgs_190_ = l_Lean_Expr_getAppNumArgs(v_e_152_);
v___x_191_ = lean_unsigned_to_nat(5u);
v___x_192_ = lean_nat_dec_le(v___x_191_, v_numArgs_190_);
if (v___x_192_ == 0)
{
v___y_184_ = v___x_191_;
v___y_185_ = v_numArgs_190_;
v___y_186_ = v___x_192_;
goto v___jp_183_;
}
else
{
lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; uint8_t v___x_196_; 
v___x_193_ = lean_unsigned_to_nat(3u);
v___x_194_ = l_Lean_Expr_getRevArg_x21(v_e_152_, v___x_193_);
v___x_195_ = l_Lean_Expr_hasLooseBVars(v___x_194_);
lean_dec_ref(v___x_194_);
v___x_196_ = lean_bool_not(v___x_195_);
v___y_184_ = v___x_191_;
v___y_185_ = v_numArgs_190_;
v___y_186_ = v___x_196_;
goto v___jp_183_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___boxed(lean_object* v_env_202_, lean_object* v_ctx_203_, lean_object* v_e_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f(v_env_202_, v_ctx_203_, v_e_204_);
lean_dec_ref(v_ctx_203_);
return v_res_205_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0(lean_object* v_00_u03b2_206_, lean_object* v_m_207_, lean_object* v_a_208_){
_start:
{
uint8_t v___x_209_; 
v___x_209_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(v_m_207_, v_a_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___boxed(lean_object* v_00_u03b2_210_, lean_object* v_m_211_, lean_object* v_a_212_){
_start:
{
uint8_t v_res_213_; lean_object* v_r_214_; 
v_res_213_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0(v_00_u03b2_210_, v_m_211_, v_a_212_);
lean_dec_ref(v_a_212_);
lean_dec_ref(v_m_211_);
v_r_214_ = lean_box(v_res_213_);
return v_r_214_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1(lean_object* v_upperBound_215_, lean_object* v_args_216_, lean_object* v_inst_217_, lean_object* v_R_218_, lean_object* v_a_219_, lean_object* v_b_220_, lean_object* v_c_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg(v_upperBound_215_, v_args_216_, v_a_219_, v_b_220_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___boxed(lean_object* v_upperBound_223_, lean_object* v_args_224_, lean_object* v_inst_225_, lean_object* v_R_226_, lean_object* v_a_227_, lean_object* v_b_228_, lean_object* v_c_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1(v_upperBound_223_, v_args_224_, v_inst_225_, v_R_226_, v_a_227_, v_b_228_, v_c_229_);
lean_dec_ref(v_b_228_);
lean_dec_ref(v_args_224_);
lean_dec(v_upperBound_223_);
return v_res_230_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0(lean_object* v_00_u03b2_231_, lean_object* v_a_232_, lean_object* v_x_233_){
_start:
{
uint8_t v___x_234_; 
v___x_234_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg(v_a_232_, v_x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_235_, lean_object* v_a_236_, lean_object* v_x_237_){
_start:
{
uint8_t v_res_238_; lean_object* v_r_239_; 
v_res_238_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0(v_00_u03b2_235_, v_a_236_, v_x_237_);
lean_dec(v_x_237_);
lean_dec_ref(v_a_236_);
v_r_239_ = lean_box(v_res_238_);
return v_r_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___redArg(lean_object* v_e_244_, lean_object* v_a_245_){
_start:
{
lean_object* v___f_247_; lean_object* v___f_248_; uint8_t v___x_249_; 
v___f_247_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__0));
v___f_248_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__1));
lean_inc_ref(v_e_244_);
v___x_249_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_247_, v___f_248_, v_a_245_, v_e_244_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_250_ = lean_box(0);
v___x_251_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_247_, v___f_248_, v_a_245_, v_e_244_, v___x_250_);
v___x_252_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__2));
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
lean_ctor_set(v___x_253_, 1, v___x_251_);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
return v___x_254_;
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
lean_dec_ref(v_e_244_);
v___x_255_ = lean_box(0);
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
lean_ctor_set(v___x_256_, 1, v_a_245_);
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
return v___x_257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___redArg___boxed(lean_object* v_e_258_, lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_Meta_FindSplitImpl_checkVisited___redArg(v_e_258_, v_a_259_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited(lean_object* v_e_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v___f_270_; lean_object* v___f_271_; uint8_t v___x_272_; 
v___f_270_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__0));
v___f_271_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__1));
lean_inc_ref(v_e_262_);
v___x_272_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_270_, v___f_271_, v_a_264_, v_e_262_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_273_ = lean_box(0);
v___x_274_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_270_, v___f_271_, v_a_264_, v_e_262_, v___x_273_);
v___x_275_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__2));
v___x_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
lean_ctor_set(v___x_276_, 1, v___x_274_);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
return v___x_277_;
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
lean_dec_ref(v_e_262_);
v___x_278_ = lean_box(0);
v___x_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v_a_264_);
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___boxed(lean_object* v_e_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_Meta_FindSplitImpl_checkVisited(v_e_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
lean_dec(v_a_285_);
lean_dec_ref(v_a_284_);
lean_dec_ref(v_a_282_);
return v_res_289_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(lean_object* v_a_290_, lean_object* v_x_291_){
_start:
{
if (lean_obj_tag(v_x_291_) == 0)
{
uint8_t v___x_292_; 
v___x_292_ = 0;
return v___x_292_;
}
else
{
lean_object* v_key_293_; lean_object* v_tail_294_; size_t v___x_295_; size_t v___x_296_; uint8_t v___x_297_; 
v_key_293_ = lean_ctor_get(v_x_291_, 0);
v_tail_294_ = lean_ctor_get(v_x_291_, 2);
v___x_295_ = lean_ptr_addr(v_key_293_);
v___x_296_ = lean_ptr_addr(v_a_290_);
v___x_297_ = lean_usize_dec_eq(v___x_295_, v___x_296_);
if (v___x_297_ == 0)
{
v_x_291_ = v_tail_294_;
goto _start;
}
else
{
return v___x_297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg___boxed(lean_object* v_a_299_, lean_object* v_x_300_){
_start:
{
uint8_t v_res_301_; lean_object* v_r_302_; 
v_res_301_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(v_a_299_, v_x_300_);
lean_dec(v_x_300_);
lean_dec_ref(v_a_299_);
v_r_302_ = lean_box(v_res_301_);
return v_r_302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6_spec__7___redArg(lean_object* v_x_303_, lean_object* v_x_304_){
_start:
{
if (lean_obj_tag(v_x_304_) == 0)
{
return v_x_303_;
}
else
{
lean_object* v_key_305_; lean_object* v_value_306_; lean_object* v_tail_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_333_; 
v_key_305_ = lean_ctor_get(v_x_304_, 0);
v_value_306_ = lean_ctor_get(v_x_304_, 1);
v_tail_307_ = lean_ctor_get(v_x_304_, 2);
v_isSharedCheck_333_ = !lean_is_exclusive(v_x_304_);
if (v_isSharedCheck_333_ == 0)
{
v___x_309_ = v_x_304_;
v_isShared_310_ = v_isSharedCheck_333_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_tail_307_);
lean_inc(v_value_306_);
lean_inc(v_key_305_);
lean_dec(v_x_304_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_333_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_311_; size_t v___x_312_; uint64_t v___x_313_; uint64_t v___x_314_; uint64_t v___x_315_; uint64_t v___x_316_; uint64_t v___x_317_; uint64_t v_fold_318_; uint64_t v___x_319_; uint64_t v___x_320_; uint64_t v___x_321_; size_t v___x_322_; size_t v___x_323_; size_t v___x_324_; size_t v___x_325_; size_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_311_ = lean_array_get_size(v_x_303_);
v___x_312_ = lean_ptr_addr(v_key_305_);
v___x_313_ = lean_usize_to_uint64(v___x_312_);
v___x_314_ = 11ULL;
v___x_315_ = lean_uint64_mix_hash(v___x_313_, v___x_314_);
v___x_316_ = 32ULL;
v___x_317_ = lean_uint64_shift_right(v___x_315_, v___x_316_);
v_fold_318_ = lean_uint64_xor(v___x_315_, v___x_317_);
v___x_319_ = 16ULL;
v___x_320_ = lean_uint64_shift_right(v_fold_318_, v___x_319_);
v___x_321_ = lean_uint64_xor(v_fold_318_, v___x_320_);
v___x_322_ = lean_uint64_to_usize(v___x_321_);
v___x_323_ = lean_usize_of_nat(v___x_311_);
v___x_324_ = ((size_t)1ULL);
v___x_325_ = lean_usize_sub(v___x_323_, v___x_324_);
v___x_326_ = lean_usize_land(v___x_322_, v___x_325_);
v___x_327_ = lean_array_uget_borrowed(v_x_303_, v___x_326_);
lean_inc(v___x_327_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 2, v___x_327_);
v___x_329_ = v___x_309_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_key_305_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_value_306_);
lean_ctor_set(v_reuseFailAlloc_332_, 2, v___x_327_);
v___x_329_ = v_reuseFailAlloc_332_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_object* v___x_330_; 
v___x_330_ = lean_array_uset(v_x_303_, v___x_326_, v___x_329_);
v_x_303_ = v___x_330_;
v_x_304_ = v_tail_307_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6___redArg(lean_object* v_i_334_, lean_object* v_source_335_, lean_object* v_target_336_){
_start:
{
lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_337_ = lean_array_get_size(v_source_335_);
v___x_338_ = lean_nat_dec_lt(v_i_334_, v___x_337_);
if (v___x_338_ == 0)
{
lean_dec_ref(v_source_335_);
lean_dec(v_i_334_);
return v_target_336_;
}
else
{
lean_object* v_es_339_; lean_object* v___x_340_; lean_object* v_source_341_; lean_object* v_target_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_es_339_ = lean_array_fget(v_source_335_, v_i_334_);
v___x_340_ = lean_box(0);
v_source_341_ = lean_array_fset(v_source_335_, v_i_334_, v___x_340_);
v_target_342_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6_spec__7___redArg(v_target_336_, v_es_339_);
v___x_343_ = lean_unsigned_to_nat(1u);
v___x_344_ = lean_nat_add(v_i_334_, v___x_343_);
lean_dec(v_i_334_);
v_i_334_ = v___x_344_;
v_source_335_ = v_source_341_;
v_target_336_ = v_target_342_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5___redArg(lean_object* v_data_346_){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v_nbuckets_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_347_ = lean_array_get_size(v_data_346_);
v___x_348_ = lean_unsigned_to_nat(2u);
v_nbuckets_349_ = lean_nat_mul(v___x_347_, v___x_348_);
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = lean_box(0);
v___x_352_ = lean_mk_array(v_nbuckets_349_, v___x_351_);
v___x_353_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6___redArg(v___x_350_, v_data_346_, v___x_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4___redArg(lean_object* v_m_354_, lean_object* v_a_355_, lean_object* v_b_356_){
_start:
{
lean_object* v_size_357_; lean_object* v_buckets_358_; lean_object* v___x_359_; size_t v___x_360_; uint64_t v___x_361_; uint64_t v___x_362_; uint64_t v___x_363_; uint64_t v___x_364_; uint64_t v___x_365_; uint64_t v_fold_366_; uint64_t v___x_367_; uint64_t v___x_368_; uint64_t v___x_369_; size_t v___x_370_; size_t v___x_371_; size_t v___x_372_; size_t v___x_373_; size_t v___x_374_; lean_object* v_bkt_375_; uint8_t v___x_376_; 
v_size_357_ = lean_ctor_get(v_m_354_, 0);
v_buckets_358_ = lean_ctor_get(v_m_354_, 1);
v___x_359_ = lean_array_get_size(v_buckets_358_);
v___x_360_ = lean_ptr_addr(v_a_355_);
v___x_361_ = lean_usize_to_uint64(v___x_360_);
v___x_362_ = 11ULL;
v___x_363_ = lean_uint64_mix_hash(v___x_361_, v___x_362_);
v___x_364_ = 32ULL;
v___x_365_ = lean_uint64_shift_right(v___x_363_, v___x_364_);
v_fold_366_ = lean_uint64_xor(v___x_363_, v___x_365_);
v___x_367_ = 16ULL;
v___x_368_ = lean_uint64_shift_right(v_fold_366_, v___x_367_);
v___x_369_ = lean_uint64_xor(v_fold_366_, v___x_368_);
v___x_370_ = lean_uint64_to_usize(v___x_369_);
v___x_371_ = lean_usize_of_nat(v___x_359_);
v___x_372_ = ((size_t)1ULL);
v___x_373_ = lean_usize_sub(v___x_371_, v___x_372_);
v___x_374_ = lean_usize_land(v___x_370_, v___x_373_);
v_bkt_375_ = lean_array_uget_borrowed(v_buckets_358_, v___x_374_);
v___x_376_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(v_a_355_, v_bkt_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_397_; 
lean_inc_ref(v_buckets_358_);
lean_inc(v_size_357_);
v_isSharedCheck_397_ = !lean_is_exclusive(v_m_354_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; lean_object* v_unused_399_; 
v_unused_398_ = lean_ctor_get(v_m_354_, 1);
lean_dec(v_unused_398_);
v_unused_399_ = lean_ctor_get(v_m_354_, 0);
lean_dec(v_unused_399_);
v___x_378_ = v_m_354_;
v_isShared_379_ = v_isSharedCheck_397_;
goto v_resetjp_377_;
}
else
{
lean_dec(v_m_354_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_397_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_380_; lean_object* v_size_x27_381_; lean_object* v___x_382_; lean_object* v_buckets_x27_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_380_ = lean_unsigned_to_nat(1u);
v_size_x27_381_ = lean_nat_add(v_size_357_, v___x_380_);
lean_dec(v_size_357_);
lean_inc(v_bkt_375_);
v___x_382_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_382_, 0, v_a_355_);
lean_ctor_set(v___x_382_, 1, v_b_356_);
lean_ctor_set(v___x_382_, 2, v_bkt_375_);
v_buckets_x27_383_ = lean_array_uset(v_buckets_358_, v___x_374_, v___x_382_);
v___x_384_ = lean_unsigned_to_nat(4u);
v___x_385_ = lean_nat_mul(v_size_x27_381_, v___x_384_);
v___x_386_ = lean_unsigned_to_nat(3u);
v___x_387_ = lean_nat_div(v___x_385_, v___x_386_);
lean_dec(v___x_385_);
v___x_388_ = lean_array_get_size(v_buckets_x27_383_);
v___x_389_ = lean_nat_dec_le(v___x_387_, v___x_388_);
lean_dec(v___x_387_);
if (v___x_389_ == 0)
{
lean_object* v_val_390_; lean_object* v___x_392_; 
v_val_390_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5___redArg(v_buckets_x27_383_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 1, v_val_390_);
lean_ctor_set(v___x_378_, 0, v_size_x27_381_);
v___x_392_ = v___x_378_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_size_x27_381_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v_val_390_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
else
{
lean_object* v___x_395_; 
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 1, v_buckets_x27_383_);
lean_ctor_set(v___x_378_, 0, v_size_x27_381_);
v___x_395_ = v___x_378_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_size_x27_381_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_buckets_x27_383_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
else
{
lean_dec(v_b_356_);
lean_dec_ref(v_a_355_);
return v_m_354_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg(lean_object* v_m_400_, lean_object* v_a_401_){
_start:
{
lean_object* v_buckets_402_; lean_object* v___x_403_; size_t v___x_404_; uint64_t v___x_405_; uint64_t v___x_406_; uint64_t v___x_407_; uint64_t v___x_408_; uint64_t v___x_409_; uint64_t v_fold_410_; uint64_t v___x_411_; uint64_t v___x_412_; uint64_t v___x_413_; size_t v___x_414_; size_t v___x_415_; size_t v___x_416_; size_t v___x_417_; size_t v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v_buckets_402_ = lean_ctor_get(v_m_400_, 1);
v___x_403_ = lean_array_get_size(v_buckets_402_);
v___x_404_ = lean_ptr_addr(v_a_401_);
v___x_405_ = lean_usize_to_uint64(v___x_404_);
v___x_406_ = 11ULL;
v___x_407_ = lean_uint64_mix_hash(v___x_405_, v___x_406_);
v___x_408_ = 32ULL;
v___x_409_ = lean_uint64_shift_right(v___x_407_, v___x_408_);
v_fold_410_ = lean_uint64_xor(v___x_407_, v___x_409_);
v___x_411_ = 16ULL;
v___x_412_ = lean_uint64_shift_right(v_fold_410_, v___x_411_);
v___x_413_ = lean_uint64_xor(v_fold_410_, v___x_412_);
v___x_414_ = lean_uint64_to_usize(v___x_413_);
v___x_415_ = lean_usize_of_nat(v___x_403_);
v___x_416_ = ((size_t)1ULL);
v___x_417_ = lean_usize_sub(v___x_415_, v___x_416_);
v___x_418_ = lean_usize_land(v___x_414_, v___x_417_);
v___x_419_ = lean_array_uget_borrowed(v_buckets_402_, v___x_418_);
v___x_420_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(v_a_401_, v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg___boxed(lean_object* v_m_421_, lean_object* v_a_422_){
_start:
{
uint8_t v_res_423_; lean_object* v_r_424_; 
v_res_423_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg(v_m_421_, v_a_422_);
lean_dec_ref(v_a_422_);
lean_dec_ref(v_m_421_);
v_r_424_ = lean_box(v_res_423_);
return v_r_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_visit(lean_object* v_e_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___y_439_; uint8_t v___x_464_; 
v___x_464_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg(v_a_427_, v_e_425_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; lean_object* v_env_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_465_ = lean_st_ref_get(v_a_431_);
v_env_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc_ref(v_env_466_);
lean_dec(v___x_465_);
v___x_467_ = lean_box(0);
lean_inc_ref_n(v_e_425_, 2);
v___x_468_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4___redArg(v_a_427_, v_e_425_, v___x_467_);
v___x_469_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f(v_env_466_, v_a_426_, v_e_425_);
if (lean_obj_tag(v___x_469_) == 1)
{
lean_object* v___x_470_; lean_object* v___x_471_; 
lean_dec_ref(v_e_425_);
v___x_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
lean_ctor_set(v___x_470_, 1, v___x_468_);
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
return v___x_471_;
}
else
{
uint8_t v___x_472_; 
lean_dec(v___x_469_);
v___x_472_ = l_Lean_Expr_hasLooseBVars(v_e_425_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; 
lean_inc_ref(v_e_425_);
v___x_473_ = l_Lean_Meta_isProof(v_e_425_, v_a_428_, v_a_429_, v_a_430_, v_a_431_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_484_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_484_ == 0)
{
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_484_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_484_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
uint8_t v___x_478_; 
v___x_478_ = lean_unbox(v_a_474_);
lean_dec(v_a_474_);
if (v___x_478_ == 0)
{
lean_del_object(v___x_476_);
v___y_434_ = v_a_426_;
v___y_435_ = v___x_468_;
v___y_436_ = v_a_428_;
v___y_437_ = v_a_429_;
v___y_438_ = v_a_430_;
v___y_439_ = v_a_431_;
goto v___jp_433_;
}
else
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_482_; 
lean_dec_ref(v_e_425_);
v___x_479_ = lean_box(0);
v___x_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
lean_ctor_set(v___x_480_, 1, v___x_468_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_480_);
v___x_482_ = v___x_476_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
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
lean_dec_ref(v___x_468_);
lean_dec_ref(v_e_425_);
v_a_485_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_473_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_473_);
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
v___y_434_ = v_a_426_;
v___y_435_ = v___x_468_;
v___y_436_ = v_a_428_;
v___y_437_ = v_a_429_;
v___y_438_ = v_a_430_;
v___y_439_ = v_a_431_;
goto v___jp_433_;
}
}
}
else
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
lean_dec_ref(v_e_425_);
v___x_493_ = lean_box(0);
v___x_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
lean_ctor_set(v___x_494_, 1, v_a_427_);
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
v___jp_433_:
{
switch(lean_obj_tag(v_e_425_))
{
case 6:
{
lean_object* v_body_440_; 
v_body_440_ = lean_ctor_get(v_e_425_, 2);
lean_inc_ref(v_body_440_);
lean_dec_ref_known(v_e_425_, 3);
v_e_425_ = v_body_440_;
v_a_426_ = v___y_434_;
v_a_427_ = v___y_435_;
v_a_428_ = v___y_436_;
v_a_429_ = v___y_437_;
v_a_430_ = v___y_438_;
v_a_431_ = v___y_439_;
goto _start;
}
case 11:
{
lean_object* v_struct_442_; 
v_struct_442_ = lean_ctor_get(v_e_425_, 2);
lean_inc_ref(v_struct_442_);
lean_dec_ref_known(v_e_425_, 3);
v_e_425_ = v_struct_442_;
v_a_426_ = v___y_434_;
v_a_427_ = v___y_435_;
v_a_428_ = v___y_436_;
v_a_429_ = v___y_437_;
v_a_430_ = v___y_438_;
v_a_431_ = v___y_439_;
goto _start;
}
case 10:
{
lean_object* v_expr_444_; 
v_expr_444_ = lean_ctor_get(v_e_425_, 1);
lean_inc_ref(v_expr_444_);
lean_dec_ref_known(v_e_425_, 2);
v_e_425_ = v_expr_444_;
v_a_426_ = v___y_434_;
v_a_427_ = v___y_435_;
v_a_428_ = v___y_436_;
v_a_429_ = v___y_437_;
v_a_430_ = v___y_438_;
v_a_431_ = v___y_439_;
goto _start;
}
case 7:
{
lean_object* v_binderType_446_; lean_object* v_body_447_; lean_object* v___x_448_; 
v_binderType_446_ = lean_ctor_get(v_e_425_, 1);
lean_inc_ref(v_binderType_446_);
v_body_447_ = lean_ctor_get(v_e_425_, 2);
lean_inc_ref(v_body_447_);
lean_dec_ref_known(v_e_425_, 3);
v___x_448_ = l_Lean_Meta_FindSplitImpl_visit(v_binderType_446_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; lean_object* v_fst_450_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_a_449_);
v_fst_450_ = lean_ctor_get(v_a_449_, 0);
if (lean_obj_tag(v_fst_450_) == 0)
{
lean_object* v_snd_451_; 
lean_dec_ref_known(v___x_448_, 1);
v_snd_451_ = lean_ctor_get(v_a_449_, 1);
lean_inc(v_snd_451_);
lean_dec(v_a_449_);
v_e_425_ = v_body_447_;
v_a_426_ = v___y_434_;
v_a_427_ = v_snd_451_;
v_a_428_ = v___y_436_;
v_a_429_ = v___y_437_;
v_a_430_ = v___y_438_;
v_a_431_ = v___y_439_;
goto _start;
}
else
{
lean_dec(v_a_449_);
lean_dec_ref(v_body_447_);
return v___x_448_;
}
}
else
{
lean_dec_ref(v_body_447_);
return v___x_448_;
}
}
case 8:
{
lean_object* v_value_453_; lean_object* v_body_454_; lean_object* v___x_455_; 
v_value_453_ = lean_ctor_get(v_e_425_, 2);
lean_inc_ref(v_value_453_);
v_body_454_ = lean_ctor_get(v_e_425_, 3);
lean_inc_ref(v_body_454_);
lean_dec_ref_known(v_e_425_, 4);
v___x_455_ = l_Lean_Meta_FindSplitImpl_visit(v_value_453_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; lean_object* v_fst_457_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_a_456_);
v_fst_457_ = lean_ctor_get(v_a_456_, 0);
if (lean_obj_tag(v_fst_457_) == 0)
{
lean_object* v_snd_458_; 
lean_dec_ref_known(v___x_455_, 1);
v_snd_458_ = lean_ctor_get(v_a_456_, 1);
lean_inc(v_snd_458_);
lean_dec(v_a_456_);
v_e_425_ = v_body_454_;
v_a_426_ = v___y_434_;
v_a_427_ = v_snd_458_;
v_a_428_ = v___y_436_;
v_a_429_ = v___y_437_;
v_a_430_ = v___y_438_;
v_a_431_ = v___y_439_;
goto _start;
}
else
{
lean_dec(v_a_456_);
lean_dec_ref(v_body_454_);
return v___x_455_;
}
}
else
{
lean_dec_ref(v_body_454_);
return v___x_455_;
}
}
case 5:
{
lean_object* v___x_460_; 
v___x_460_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f(v_e_425_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
return v___x_460_;
}
default: 
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
lean_dec_ref(v_e_425_);
v___x_461_ = lean_box(0);
v___x_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v___y_435_);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
return v___x_463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(lean_object* v_upperBound_496_, lean_object* v_args_497_, lean_object* v_info_498_, lean_object* v_a_499_, lean_object* v_b_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v_a_509_; lean_object* v_snd_510_; lean_object* v_a_514_; lean_object* v_snd_515_; uint8_t v___x_519_; 
v___x_519_ = lean_nat_dec_lt(v_a_499_, v_upperBound_496_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; 
lean_dec(v_a_499_);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v_b_500_);
lean_ctor_set(v___x_520_, 1, v___y_502_);
v___x_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
return v___x_521_;
}
else
{
lean_object* v_paramInfo_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
lean_dec_ref(v_b_500_);
v_paramInfo_522_ = lean_ctor_get(v_info_498_, 0);
v___x_523_ = lean_box(0);
v___x_524_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0));
v___x_525_ = lean_array_fget_borrowed(v_args_497_, v_a_499_);
v___x_526_ = lean_array_get_size(v_paramInfo_522_);
v___x_527_ = lean_nat_dec_lt(v_a_499_, v___x_526_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; 
lean_inc(v___x_525_);
v___x_528_ = l_Lean_Meta_FindSplitImpl_visit(v___x_525_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v_fst_530_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_a_529_);
lean_dec_ref_known(v___x_528_, 1);
v_fst_530_ = lean_ctor_get(v_a_529_, 0);
if (lean_obj_tag(v_fst_530_) == 1)
{
lean_object* v_snd_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_539_; 
lean_inc_ref(v_fst_530_);
lean_dec(v_a_499_);
v_snd_531_ = lean_ctor_get(v_a_529_, 1);
v_isSharedCheck_539_ = !lean_is_exclusive(v_a_529_);
if (v_isSharedCheck_539_ == 0)
{
lean_object* v_unused_540_; 
v_unused_540_ = lean_ctor_get(v_a_529_, 0);
lean_dec(v_unused_540_);
v___x_533_ = v_a_529_;
v_isShared_534_ = v_isSharedCheck_539_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_snd_531_);
lean_dec(v_a_529_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_539_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_535_, 0, v_fst_530_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 1, v___x_523_);
lean_ctor_set(v___x_533_, 0, v___x_535_);
v___x_537_ = v___x_533_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v___x_523_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
v_a_509_ = v___x_537_;
v_snd_510_ = v_snd_531_;
goto v___jp_508_;
}
}
}
else
{
lean_object* v_snd_541_; 
v_snd_541_ = lean_ctor_get(v_a_529_, 1);
lean_inc(v_snd_541_);
lean_dec(v_a_529_);
v_a_514_ = v___x_524_;
v_snd_515_ = v_snd_541_;
goto v___jp_513_;
}
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
lean_dec(v_a_499_);
v_a_542_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_528_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_528_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
else
{
lean_object* v___x_550_; uint8_t v_isProp_551_; 
v___x_550_ = lean_array_fget_borrowed(v_paramInfo_522_, v_a_499_);
v_isProp_551_ = lean_ctor_get_uint8(v___x_550_, sizeof(void*)*1 + 2);
if (v_isProp_551_ == 0)
{
uint8_t v___x_552_; 
v___x_552_ = l_Lean_Meta_ParamInfo_isExplicit(v___x_550_);
if (v___x_552_ == 0)
{
v_a_514_ = v___x_524_;
v_snd_515_ = v___y_502_;
goto v___jp_513_;
}
else
{
lean_object* v___x_553_; 
lean_inc(v___x_525_);
v___x_553_ = l_Lean_Meta_FindSplitImpl_visit(v___x_525_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v_fst_555_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref_known(v___x_553_, 1);
v_fst_555_ = lean_ctor_get(v_a_554_, 0);
if (lean_obj_tag(v_fst_555_) == 1)
{
lean_object* v_snd_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_564_; 
lean_inc_ref(v_fst_555_);
lean_dec(v_a_499_);
v_snd_556_ = lean_ctor_get(v_a_554_, 1);
v_isSharedCheck_564_ = !lean_is_exclusive(v_a_554_);
if (v_isSharedCheck_564_ == 0)
{
lean_object* v_unused_565_; 
v_unused_565_ = lean_ctor_get(v_a_554_, 0);
lean_dec(v_unused_565_);
v___x_558_ = v_a_554_;
v_isShared_559_ = v_isSharedCheck_564_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_snd_556_);
lean_dec(v_a_554_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_564_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_560_, 0, v_fst_555_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 1, v___x_523_);
lean_ctor_set(v___x_558_, 0, v___x_560_);
v___x_562_ = v___x_558_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v___x_523_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
v_a_509_ = v___x_562_;
v_snd_510_ = v_snd_556_;
goto v___jp_508_;
}
}
}
else
{
lean_object* v_snd_566_; 
v_snd_566_ = lean_ctor_get(v_a_554_, 1);
lean_inc(v_snd_566_);
lean_dec(v_a_554_);
v_a_514_ = v___x_524_;
v_snd_515_ = v_snd_566_;
goto v___jp_513_;
}
}
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
lean_dec(v_a_499_);
v_a_567_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_553_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_553_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
else
{
v_a_514_ = v___x_524_;
v_snd_515_ = v___y_502_;
goto v___jp_513_;
}
}
}
v___jp_508_:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v_a_509_);
lean_ctor_set(v___x_511_, 1, v_snd_510_);
v___x_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
return v___x_512_;
}
v___jp_513_:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_unsigned_to_nat(1u);
v___x_517_ = lean_nat_add(v_a_499_, v___x_516_);
lean_dec(v_a_499_);
lean_inc_ref(v_a_514_);
v_a_499_ = v___x_517_;
v_b_500_ = v_a_514_;
v___y_502_ = v_snd_515_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1(lean_object* v_x_579_, lean_object* v_x_580_, lean_object* v_x_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v_info_590_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; 
if (lean_obj_tag(v_x_579_) == 5)
{
lean_object* v_fn_631_; lean_object* v_arg_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v_fn_631_ = lean_ctor_get(v_x_579_, 0);
lean_inc_ref(v_fn_631_);
v_arg_632_ = lean_ctor_get(v_x_579_, 1);
lean_inc_ref(v_arg_632_);
lean_dec_ref_known(v_x_579_, 2);
v___x_633_ = lean_array_set(v_x_580_, v_x_581_, v_arg_632_);
v___x_634_ = lean_unsigned_to_nat(1u);
v___x_635_ = lean_nat_sub(v_x_581_, v___x_634_);
lean_dec(v_x_581_);
v_x_579_ = v_fn_631_;
v_x_580_ = v___x_633_;
v_x_581_ = v___x_635_;
goto _start;
}
else
{
uint8_t v___x_637_; 
lean_dec(v_x_581_);
v___x_637_ = l_Lean_Expr_hasLooseBVars(v_x_579_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_box(0);
lean_inc_ref(v_x_579_);
v___x_639_ = l_Lean_Meta_getFunInfo(v_x_579_, v___x_638_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
lean_dec_ref_known(v___x_639_, 1);
v_info_590_ = v_a_640_;
v___y_591_ = v___y_582_;
v___y_592_ = v___y_583_;
v___y_593_ = v___y_584_;
v___y_594_ = v___y_585_;
v___y_595_ = v___y_586_;
v___y_596_ = v___y_587_;
goto v___jp_589_;
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_dec_ref(v___y_583_);
lean_dec_ref(v_x_580_);
lean_dec_ref(v_x_579_);
v_a_641_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_639_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_639_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
else
{
lean_object* v___x_649_; 
v___x_649_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___closed__1));
v_info_590_ = v___x_649_;
v___y_591_ = v___y_582_;
v___y_592_ = v___y_583_;
v___y_593_ = v___y_584_;
v___y_594_ = v___y_585_;
v___y_595_ = v___y_586_;
v___y_596_ = v___y_587_;
goto v___jp_589_;
}
}
v___jp_589_:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_597_ = lean_array_get_size(v_x_580_);
v___x_598_ = lean_unsigned_to_nat(0u);
v___x_599_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0));
v___x_600_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(v___x_597_, v_x_580_, v_info_590_, v___x_598_, v___x_599_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
lean_dec_ref(v_info_590_);
lean_dec_ref(v_x_580_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_622_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_622_ == 0)
{
v___x_603_ = v___x_600_;
v_isShared_604_ = v_isSharedCheck_622_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_600_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_622_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v_fst_605_; lean_object* v_fst_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_620_; 
v_fst_605_ = lean_ctor_get(v_a_601_, 0);
lean_inc(v_fst_605_);
v_fst_606_ = lean_ctor_get(v_fst_605_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v_fst_605_);
if (v_isSharedCheck_620_ == 0)
{
lean_object* v_unused_621_; 
v_unused_621_ = lean_ctor_get(v_fst_605_, 1);
lean_dec(v_unused_621_);
v___x_608_ = v_fst_605_;
v_isShared_609_ = v_isSharedCheck_620_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_fst_606_);
lean_dec(v_fst_605_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_620_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
if (lean_obj_tag(v_fst_606_) == 0)
{
lean_object* v_snd_610_; lean_object* v___x_611_; 
lean_del_object(v___x_608_);
lean_del_object(v___x_603_);
v_snd_610_ = lean_ctor_get(v_a_601_, 1);
lean_inc(v_snd_610_);
lean_dec(v_a_601_);
v___x_611_ = l_Lean_Meta_FindSplitImpl_visit(v_x_579_, v___y_591_, v_snd_610_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
return v___x_611_;
}
else
{
lean_object* v_snd_612_; lean_object* v_val_613_; lean_object* v___x_615_; 
lean_dec_ref(v_x_579_);
v_snd_612_ = lean_ctor_get(v_a_601_, 1);
lean_inc(v_snd_612_);
lean_dec(v_a_601_);
v_val_613_ = lean_ctor_get(v_fst_606_, 0);
lean_inc(v_val_613_);
lean_dec_ref_known(v_fst_606_, 1);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 1, v_snd_612_);
lean_ctor_set(v___x_608_, 0, v_val_613_);
v___x_615_ = v___x_608_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_val_613_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_snd_612_);
v___x_615_ = v_reuseFailAlloc_619_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_617_; 
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_615_);
v___x_617_ = v___x_603_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_615_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec_ref(v_x_579_);
v_a_623_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_600_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_600_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f(lean_object* v_e_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
lean_object* v_dummy_658_; lean_object* v_nargs_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v_dummy_658_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0);
v_nargs_659_ = l_Lean_Expr_getAppNumArgs(v_e_650_);
lean_inc(v_nargs_659_);
v___x_660_ = lean_mk_array(v_nargs_659_, v_dummy_658_);
v___x_661_ = lean_unsigned_to_nat(1u);
v___x_662_ = lean_nat_sub(v_nargs_659_, v___x_661_);
lean_dec(v_nargs_659_);
v___x_663_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1(v_e_650_, v___x_660_, v___x_662_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f___boxed(lean_object* v_e_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f(v_e_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_);
lean_dec(v_a_670_);
lean_dec_ref(v_a_669_);
lean_dec(v_a_668_);
lean_dec_ref(v_a_667_);
lean_dec_ref(v_a_665_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___boxed(lean_object* v_x_673_, lean_object* v_x_674_, lean_object* v_x_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1(v_x_673_, v_x_674_, v_x_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec_ref(v___y_676_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg___boxed(lean_object* v_upperBound_684_, lean_object* v_args_685_, lean_object* v_info_686_, lean_object* v_a_687_, lean_object* v_b_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(v_upperBound_684_, v_args_685_, v_info_686_, v_a_687_, v_b_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec_ref(v___y_689_);
lean_dec_ref(v_info_686_);
lean_dec_ref(v_args_685_);
lean_dec(v_upperBound_684_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_visit___boxed(lean_object* v_e_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_Meta_FindSplitImpl_visit(v_e_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_);
lean_dec(v_a_703_);
lean_dec_ref(v_a_702_);
lean_dec(v_a_701_);
lean_dec_ref(v_a_700_);
lean_dec_ref(v_a_698_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0(lean_object* v_upperBound_706_, lean_object* v_args_707_, lean_object* v_info_708_, lean_object* v_inst_709_, lean_object* v_R_710_, lean_object* v_a_711_, lean_object* v_b_712_, lean_object* v_c_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(v_upperBound_706_, v_args_707_, v_info_708_, v_a_711_, v_b_712_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___boxed(lean_object* v_upperBound_722_, lean_object* v_args_723_, lean_object* v_info_724_, lean_object* v_inst_725_, lean_object* v_R_726_, lean_object* v_a_727_, lean_object* v_b_728_, lean_object* v_c_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0(v_upperBound_722_, v_args_723_, v_info_724_, v_inst_725_, v_R_726_, v_a_727_, v_b_728_, v_c_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec_ref(v___y_730_);
lean_dec_ref(v_info_724_);
lean_dec_ref(v_args_723_);
lean_dec(v_upperBound_722_);
return v_res_737_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3(lean_object* v_00_u03b2_738_, lean_object* v_m_739_, lean_object* v_a_740_){
_start:
{
uint8_t v___x_741_; 
v___x_741_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg(v_m_739_, v_a_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___boxed(lean_object* v_00_u03b2_742_, lean_object* v_m_743_, lean_object* v_a_744_){
_start:
{
uint8_t v_res_745_; lean_object* v_r_746_; 
v_res_745_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3(v_00_u03b2_742_, v_m_743_, v_a_744_);
lean_dec_ref(v_a_744_);
lean_dec_ref(v_m_743_);
v_r_746_ = lean_box(v_res_745_);
return v_r_746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4(lean_object* v_00_u03b2_747_, lean_object* v_m_748_, lean_object* v_a_749_, lean_object* v_b_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4___redArg(v_m_748_, v_a_749_, v_b_750_);
return v___x_751_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3(lean_object* v_00_u03b2_752_, lean_object* v_a_753_, lean_object* v_x_754_){
_start:
{
uint8_t v___x_755_; 
v___x_755_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(v_a_753_, v_x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___boxed(lean_object* v_00_u03b2_756_, lean_object* v_a_757_, lean_object* v_x_758_){
_start:
{
uint8_t v_res_759_; lean_object* v_r_760_; 
v_res_759_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3(v_00_u03b2_756_, v_a_757_, v_x_758_);
lean_dec(v_x_758_);
lean_dec_ref(v_a_757_);
v_r_760_ = lean_box(v_res_759_);
return v_r_760_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5(lean_object* v_00_u03b2_761_, lean_object* v_data_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5___redArg(v_data_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_764_, lean_object* v_i_765_, lean_object* v_source_766_, lean_object* v_target_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6___redArg(v_i_765_, v_source_766_, v_target_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_769_, lean_object* v_x_770_, lean_object* v_x_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6_spec__7___redArg(v_x_770_, v_x_771_);
return v___x_772_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_unsigned_to_nat(64u);
v___x_774_ = l_Lean_mkPtrSet___redArg(v___x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1(uint8_t v_kind_775_, lean_object* v_exceptionSet_776_, lean_object* v_e_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_783_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_783_, 0, v_exceptionSet_776_);
lean_ctor_set_uint8(v___x_783_, sizeof(void*)*1, v_kind_775_);
v___x_784_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0);
v___x_785_ = l_Lean_Meta_FindSplitImpl_visit(v_e_777_, v___x_783_, v___x_784_, v_a_778_, v_a_779_, v_a_780_, v_a_781_);
lean_dec_ref_known(v___x_783_, 1);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_794_; 
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
lean_object* v_fst_790_; lean_object* v___x_792_; 
v_fst_790_ = lean_ctor_get(v_a_786_, 0);
lean_inc(v_fst_790_);
lean_dec(v_a_786_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v_fst_790_);
v___x_792_ = v___x_788_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_fst_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
v_a_795_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_785_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_785_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___boxed(lean_object* v_kind_803_, lean_object* v_exceptionSet_804_, lean_object* v_e_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_){
_start:
{
uint8_t v_kind_boxed_811_; lean_object* v_res_812_; 
v_kind_boxed_811_ = lean_unbox(v_kind_803_);
v_res_812_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1(v_kind_boxed_811_, v_exceptionSet_804_, v_e_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(lean_object* v_msgData_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v___x_819_; lean_object* v_env_820_; lean_object* v___x_821_; lean_object* v_mctx_822_; lean_object* v_lctx_823_; lean_object* v_options_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_819_ = lean_st_ref_get(v___y_817_);
v_env_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc_ref(v_env_820_);
lean_dec(v___x_819_);
v___x_821_ = lean_st_ref_get(v___y_815_);
v_mctx_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc_ref(v_mctx_822_);
lean_dec(v___x_821_);
v_lctx_823_ = lean_ctor_get(v___y_814_, 2);
v_options_824_ = lean_ctor_get(v___y_816_, 2);
lean_inc_ref(v_options_824_);
lean_inc_ref(v_lctx_823_);
v___x_825_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_825_, 0, v_env_820_);
lean_ctor_set(v___x_825_, 1, v_mctx_822_);
lean_ctor_set(v___x_825_, 2, v_lctx_823_);
lean_ctor_set(v___x_825_, 3, v_options_824_);
v___x_826_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
lean_ctor_set(v___x_826_, 1, v_msgData_813_);
v___x_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0___boxed(lean_object* v_msgData_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(v_msgData_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
return v_res_834_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_835_; double v___x_836_; 
v___x_835_ = lean_unsigned_to_nat(0u);
v___x_836_ = lean_float_of_nat(v___x_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(lean_object* v_cls_840_, lean_object* v_msg_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_ref_847_; lean_object* v___x_848_; lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_893_; 
v_ref_847_ = lean_ctor_get(v___y_844_, 5);
v___x_848_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(v_msg_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_893_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_893_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_893_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; lean_object* v_traceState_854_; lean_object* v_env_855_; lean_object* v_nextMacroScope_856_; lean_object* v_ngen_857_; lean_object* v_auxDeclNGen_858_; lean_object* v_cache_859_; lean_object* v_messages_860_; lean_object* v_infoState_861_; lean_object* v_snapshotTasks_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_892_; 
v___x_853_ = lean_st_ref_take(v___y_845_);
v_traceState_854_ = lean_ctor_get(v___x_853_, 4);
v_env_855_ = lean_ctor_get(v___x_853_, 0);
v_nextMacroScope_856_ = lean_ctor_get(v___x_853_, 1);
v_ngen_857_ = lean_ctor_get(v___x_853_, 2);
v_auxDeclNGen_858_ = lean_ctor_get(v___x_853_, 3);
v_cache_859_ = lean_ctor_get(v___x_853_, 5);
v_messages_860_ = lean_ctor_get(v___x_853_, 6);
v_infoState_861_ = lean_ctor_get(v___x_853_, 7);
v_snapshotTasks_862_ = lean_ctor_get(v___x_853_, 8);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_892_ == 0)
{
v___x_864_ = v___x_853_;
v_isShared_865_ = v_isSharedCheck_892_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_snapshotTasks_862_);
lean_inc(v_infoState_861_);
lean_inc(v_messages_860_);
lean_inc(v_cache_859_);
lean_inc(v_traceState_854_);
lean_inc(v_auxDeclNGen_858_);
lean_inc(v_ngen_857_);
lean_inc(v_nextMacroScope_856_);
lean_inc(v_env_855_);
lean_dec(v___x_853_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_892_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
uint64_t v_tid_866_; lean_object* v_traces_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_891_; 
v_tid_866_ = lean_ctor_get_uint64(v_traceState_854_, sizeof(void*)*1);
v_traces_867_ = lean_ctor_get(v_traceState_854_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v_traceState_854_);
if (v_isSharedCheck_891_ == 0)
{
v___x_869_ = v_traceState_854_;
v_isShared_870_ = v_isSharedCheck_891_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_traces_867_);
lean_dec(v_traceState_854_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_891_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_871_; double v___x_872_; uint8_t v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_871_ = lean_box(0);
v___x_872_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0);
v___x_873_ = 0;
v___x_874_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__1));
v___x_875_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_875_, 0, v_cls_840_);
lean_ctor_set(v___x_875_, 1, v___x_871_);
lean_ctor_set(v___x_875_, 2, v___x_874_);
lean_ctor_set_float(v___x_875_, sizeof(void*)*3, v___x_872_);
lean_ctor_set_float(v___x_875_, sizeof(void*)*3 + 8, v___x_872_);
lean_ctor_set_uint8(v___x_875_, sizeof(void*)*3 + 16, v___x_873_);
v___x_876_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__2));
v___x_877_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_877_, 0, v___x_875_);
lean_ctor_set(v___x_877_, 1, v_a_849_);
lean_ctor_set(v___x_877_, 2, v___x_876_);
lean_inc(v_ref_847_);
v___x_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_878_, 0, v_ref_847_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = l_Lean_PersistentArray_push___redArg(v_traces_867_, v___x_878_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v___x_879_);
v___x_881_ = v___x_869_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_879_);
lean_ctor_set_uint64(v_reuseFailAlloc_890_, sizeof(void*)*1, v_tid_866_);
v___x_881_ = v_reuseFailAlloc_890_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_883_; 
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 4, v___x_881_);
v___x_883_ = v___x_864_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_env_855_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_nextMacroScope_856_);
lean_ctor_set(v_reuseFailAlloc_889_, 2, v_ngen_857_);
lean_ctor_set(v_reuseFailAlloc_889_, 3, v_auxDeclNGen_858_);
lean_ctor_set(v_reuseFailAlloc_889_, 4, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_889_, 5, v_cache_859_);
lean_ctor_set(v_reuseFailAlloc_889_, 6, v_messages_860_);
lean_ctor_set(v_reuseFailAlloc_889_, 7, v_infoState_861_);
lean_ctor_set(v_reuseFailAlloc_889_, 8, v_snapshotTasks_862_);
v___x_883_ = v_reuseFailAlloc_889_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_884_ = lean_st_ref_set(v___y_845_, v___x_883_);
v___x_885_ = lean_box(0);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_885_);
v___x_887_ = v___x_851_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___boxed(lean_object* v_cls_894_, lean_object* v_msg_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v_cls_894_, v_msg_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
return v_res_901_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5(void){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_910_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__2));
v___x_911_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4));
v___x_912_ = l_Lean_Name_append(v___x_911_, v___x_910_);
return v___x_912_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7(void){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__6));
v___x_915_ = l_Lean_stringToMessageData(v___x_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f(uint8_t v_kind_916_, lean_object* v_exceptionSet_917_, lean_object* v_e_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1(v_kind_916_, v_exceptionSet_917_, v_e_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_a_925_);
if (lean_obj_tag(v_a_925_) == 1)
{
lean_object* v_options_926_; uint8_t v_hasTrace_927_; 
v_options_926_ = lean_ctor_get(v_a_921_, 2);
v_hasTrace_927_ = lean_ctor_get_uint8(v_options_926_, sizeof(void*)*1);
if (v_hasTrace_927_ == 0)
{
lean_dec_ref_known(v_a_925_, 1);
return v___x_924_;
}
else
{
lean_object* v_val_928_; lean_object* v_inheritedTraceOptions_929_; lean_object* v___x_930_; lean_object* v___x_931_; uint8_t v___x_932_; 
v_val_928_ = lean_ctor_get(v_a_925_, 0);
v_inheritedTraceOptions_929_ = lean_ctor_get(v_a_921_, 13);
v___x_930_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__2));
v___x_931_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5);
v___x_932_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_929_, v_options_926_, v___x_931_);
if (v___x_932_ == 0)
{
lean_dec_ref_known(v_a_925_, 1);
return v___x_924_;
}
else
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
lean_dec_ref_known(v___x_924_, 1);
v___x_933_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7);
lean_inc(v_val_928_);
v___x_934_ = l_Lean_indentExpr(v_val_928_);
v___x_935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_933_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_930_, v___x_935_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_943_ == 0)
{
lean_object* v_unused_944_; 
v_unused_944_ = lean_ctor_get(v___x_936_, 0);
lean_dec(v_unused_944_);
v___x_938_ = v___x_936_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_dec(v___x_936_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v_a_925_);
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_925_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_dec_ref_known(v_a_925_, 1);
v_a_945_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_936_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_936_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
}
}
else
{
lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_960_; 
lean_dec(v_a_925_);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_960_ == 0)
{
lean_object* v_unused_961_; 
v_unused_961_ = lean_ctor_get(v___x_924_, 0);
lean_dec(v_unused_961_);
v___x_954_ = v___x_924_;
v_isShared_955_ = v_isSharedCheck_960_;
goto v_resetjp_953_;
}
else
{
lean_dec(v___x_924_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_960_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; lean_object* v___x_958_; 
v___x_956_ = lean_box(0);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v___x_956_);
v___x_958_ = v___x_954_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_956_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
else
{
return v___x_924_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___boxed(lean_object* v_kind_962_, lean_object* v_exceptionSet_963_, lean_object* v_e_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
uint8_t v_kind_boxed_970_; lean_object* v_res_971_; 
v_kind_boxed_970_ = lean_unbox(v_kind_962_);
v_res_971_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f(v_kind_boxed_970_, v_exceptionSet_963_, v_e_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
lean_dec(v_a_968_);
lean_dec_ref(v_a_967_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(uint8_t v_kind_972_, lean_object* v_exceptionSet_973_, lean_object* v_e_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
lean_object* v___y_981_; lean_object* v___x_984_; 
lean_inc_ref(v_exceptionSet_973_);
v___x_984_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f(v_kind_972_, v_exceptionSet_973_, v_e_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
if (lean_obj_tag(v_a_985_) == 1)
{
lean_object* v_val_986_; uint8_t v___y_988_; uint8_t v___x_994_; 
v_val_986_ = lean_ctor_get(v_a_985_, 0);
lean_inc(v_val_986_);
lean_dec_ref_known(v_a_985_, 1);
v___x_994_ = l_Lean_Expr_isIte(v_val_986_);
if (v___x_994_ == 0)
{
uint8_t v___x_995_; 
v___x_995_ = l_Lean_Expr_isDIte(v_val_986_);
v___y_988_ = v___x_995_;
goto v___jp_987_;
}
else
{
v___y_988_ = v___x_994_;
goto v___jp_987_;
}
v___jp_987_:
{
if (v___y_988_ == 0)
{
lean_dec(v_val_986_);
lean_dec_ref(v_exceptionSet_973_);
return v___x_984_;
}
else
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
lean_dec_ref_known(v___x_984_, 1);
v___x_989_ = lean_unsigned_to_nat(3u);
v___x_990_ = l_Lean_Expr_getRevArg_x21(v_val_986_, v___x_989_);
v___x_991_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(v_kind_972_, v_exceptionSet_973_, v___x_990_, v_a_975_, v_a_976_, v_a_977_, v_a_978_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_a_992_);
lean_dec_ref_known(v___x_991_, 1);
if (lean_obj_tag(v_a_992_) == 0)
{
v___y_981_ = v_val_986_;
goto v___jp_980_;
}
else
{
lean_object* v_val_993_; 
lean_dec(v_val_986_);
v_val_993_ = lean_ctor_get(v_a_992_, 0);
lean_inc(v_val_993_);
lean_dec_ref_known(v_a_992_, 1);
v___y_981_ = v_val_993_;
goto v___jp_980_;
}
}
else
{
lean_dec(v_val_986_);
return v___x_991_;
}
}
}
}
else
{
lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1003_; 
lean_dec(v_a_985_);
lean_dec_ref(v_exceptionSet_973_);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1003_ == 0)
{
lean_object* v_unused_1004_; 
v_unused_1004_ = lean_ctor_get(v___x_984_, 0);
lean_dec(v_unused_1004_);
v___x_997_ = v___x_984_;
v_isShared_998_ = v_isSharedCheck_1003_;
goto v_resetjp_996_;
}
else
{
lean_dec(v___x_984_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1003_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; lean_object* v___x_1001_; 
v___x_999_ = lean_box(0);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v___x_999_);
v___x_1001_ = v___x_997_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
else
{
lean_dec_ref(v_exceptionSet_973_);
return v___x_984_;
}
v___jp_980_:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_982_, 0, v___y_981_);
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
return v___x_983_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go___boxed(lean_object* v_kind_1005_, lean_object* v_exceptionSet_1006_, lean_object* v_e_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_){
_start:
{
uint8_t v_kind_boxed_1013_; lean_object* v_res_1014_; 
v_kind_boxed_1013_ = lean_unbox(v_kind_1005_);
v_res_1014_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(v_kind_boxed_1013_, v_exceptionSet_1006_, v_e_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_);
lean_dec(v_a_1011_);
lean_dec_ref(v_a_1010_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(lean_object* v_e_1015_, lean_object* v___y_1016_){
_start:
{
uint8_t v___x_1018_; uint8_t v___x_1019_; 
v___x_1018_ = l_Lean_Expr_hasMVar(v_e_1015_);
v___x_1019_ = lean_bool_not(v___x_1018_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; lean_object* v_mctx_1021_; lean_object* v___x_1022_; lean_object* v_fst_1023_; lean_object* v_snd_1024_; lean_object* v___x_1025_; lean_object* v_cache_1026_; lean_object* v_zetaDeltaFVarIds_1027_; lean_object* v_postponed_1028_; lean_object* v_diag_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1038_; 
v___x_1020_ = lean_st_ref_get(v___y_1016_);
v_mctx_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc_ref(v_mctx_1021_);
lean_dec(v___x_1020_);
v___x_1022_ = l_Lean_instantiateMVarsCore(v_mctx_1021_, v_e_1015_);
v_fst_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_fst_1023_);
v_snd_1024_ = lean_ctor_get(v___x_1022_, 1);
lean_inc(v_snd_1024_);
lean_dec_ref(v___x_1022_);
v___x_1025_ = lean_st_ref_take(v___y_1016_);
v_cache_1026_ = lean_ctor_get(v___x_1025_, 1);
v_zetaDeltaFVarIds_1027_ = lean_ctor_get(v___x_1025_, 2);
v_postponed_1028_ = lean_ctor_get(v___x_1025_, 3);
v_diag_1029_ = lean_ctor_get(v___x_1025_, 4);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1038_ == 0)
{
lean_object* v_unused_1039_; 
v_unused_1039_ = lean_ctor_get(v___x_1025_, 0);
lean_dec(v_unused_1039_);
v___x_1031_ = v___x_1025_;
v_isShared_1032_ = v_isSharedCheck_1038_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_diag_1029_);
lean_inc(v_postponed_1028_);
lean_inc(v_zetaDeltaFVarIds_1027_);
lean_inc(v_cache_1026_);
lean_dec(v___x_1025_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1038_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 0, v_snd_1024_);
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_snd_1024_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_cache_1026_);
lean_ctor_set(v_reuseFailAlloc_1037_, 2, v_zetaDeltaFVarIds_1027_);
lean_ctor_set(v_reuseFailAlloc_1037_, 3, v_postponed_1028_);
lean_ctor_set(v_reuseFailAlloc_1037_, 4, v_diag_1029_);
v___x_1034_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = lean_st_ref_set(v___y_1016_, v___x_1034_);
v___x_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1036_, 0, v_fst_1023_);
return v___x_1036_;
}
}
}
else
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1040_, 0, v_e_1015_);
return v___x_1040_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg___boxed(lean_object* v_e_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_1041_, v___y_1042_);
lean_dec(v___y_1042_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0(lean_object* v_e_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_1045_, v___y_1047_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___boxed(lean_object* v_e_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0(v_e_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f(lean_object* v_e_1059_, uint8_t v_kind_1060_, lean_object* v_exceptionSet_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v___x_1067_; lean_object* v_a_1068_; lean_object* v___x_1069_; 
v___x_1067_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_1059_, v_a_1063_);
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1068_);
lean_dec_ref(v___x_1067_);
v___x_1069_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(v_kind_1060_, v_exceptionSet_1061_, v_a_1068_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f___boxed(lean_object* v_e_1070_, lean_object* v_kind_1071_, lean_object* v_exceptionSet_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_){
_start:
{
uint8_t v_kind_boxed_1078_; lean_object* v_res_1079_; 
v_kind_boxed_1078_ = lean_unbox(v_kind_1071_);
v_res_1079_ = l_Lean_Meta_findSplit_x3f(v_e_1070_, v_kind_boxed_1078_, v_exceptionSet_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
lean_dec(v_a_1076_);
lean_dec_ref(v_a_1075_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
return v_res_1079_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1080_ = lean_box(0);
v___x_1081_ = lean_unsigned_to_nat(16u);
v___x_1082_ = lean_mk_array(v___x_1081_, v___x_1080_);
return v___x_1082_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1083_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0);
v___x_1084_ = lean_unsigned_to_nat(0u);
v___x_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
lean_ctor_set(v___x_1085_, 1, v___x_1083_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(lean_object* v_e_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
uint8_t v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1092_ = 0;
v___x_1093_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1);
v___x_1094_ = l_Lean_Meta_findSplit_x3f(v_e_1086_, v___x_1092_, v___x_1093_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1119_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1097_ = v___x_1094_;
v_isShared_1098_ = v_isSharedCheck_1119_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1094_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1119_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
if (lean_obj_tag(v_a_1095_) == 1)
{
lean_object* v_val_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1114_; 
v_val_1099_ = lean_ctor_get(v_a_1095_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_a_1095_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1101_ = v_a_1095_;
v_isShared_1102_ = v_isSharedCheck_1114_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_val_1099_);
lean_dec(v_a_1095_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1114_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1109_; 
v___x_1103_ = lean_unsigned_to_nat(3u);
v___x_1104_ = l_Lean_Expr_getRevArg_x21(v_val_1099_, v___x_1103_);
v___x_1105_ = lean_unsigned_to_nat(2u);
v___x_1106_ = l_Lean_Expr_getRevArg_x21(v_val_1099_, v___x_1105_);
lean_dec(v_val_1099_);
v___x_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1104_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1107_);
v___x_1109_ = v___x_1101_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1107_);
v___x_1109_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1111_; 
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 0, v___x_1109_);
v___x_1111_ = v___x_1097_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1109_);
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
else
{
lean_object* v___x_1115_; lean_object* v___x_1117_; 
lean_dec(v_a_1095_);
v___x_1115_ = lean_box(0);
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 0, v___x_1115_);
v___x_1117_ = v___x_1097_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1115_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
v_a_1120_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1094_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1094_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___boxed(lean_object* v_e_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(v_e_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(lean_object* v_name_1135_, lean_object* v_decl_1136_, lean_object* v_ref_1137_){
_start:
{
lean_object* v_defValue_1139_; lean_object* v_descr_1140_; lean_object* v_deprecation_x3f_1141_; lean_object* v___x_1142_; uint8_t v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v_defValue_1139_ = lean_ctor_get(v_decl_1136_, 0);
v_descr_1140_ = lean_ctor_get(v_decl_1136_, 1);
v_deprecation_x3f_1141_ = lean_ctor_get(v_decl_1136_, 2);
v___x_1142_ = lean_alloc_ctor(1, 0, 1);
v___x_1143_ = lean_unbox(v_defValue_1139_);
lean_ctor_set_uint8(v___x_1142_, 0, v___x_1143_);
lean_inc(v_deprecation_x3f_1141_);
lean_inc_ref(v_descr_1140_);
lean_inc_n(v_name_1135_, 2);
v___x_1144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1144_, 0, v_name_1135_);
lean_ctor_set(v___x_1144_, 1, v_ref_1137_);
lean_ctor_set(v___x_1144_, 2, v___x_1142_);
lean_ctor_set(v___x_1144_, 3, v_descr_1140_);
lean_ctor_set(v___x_1144_, 4, v_deprecation_x3f_1141_);
v___x_1145_ = lean_register_option(v_name_1135_, v___x_1144_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1153_; 
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1153_ == 0)
{
lean_object* v_unused_1154_; 
v_unused_1154_ = lean_ctor_get(v___x_1145_, 0);
lean_dec(v_unused_1154_);
v___x_1147_ = v___x_1145_;
v_isShared_1148_ = v_isSharedCheck_1153_;
goto v_resetjp_1146_;
}
else
{
lean_dec(v___x_1145_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1153_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1149_; lean_object* v___x_1151_; 
lean_inc(v_defValue_1139_);
v___x_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1149_, 0, v_name_1135_);
lean_ctor_set(v___x_1149_, 1, v_defValue_1139_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1149_);
v___x_1151_ = v___x_1147_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
lean_dec(v_name_1135_);
v_a_1155_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1145_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1145_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1163_, lean_object* v_decl_1164_, lean_object* v_ref_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(v_name_1163_, v_decl_1164_, v_ref_1165_);
lean_dec_ref(v_decl_1164_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1186_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_));
v___x_1187_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_));
v___x_1188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_));
v___x_1189_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(v___x_1186_, v___x_1187_, v___x_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4____boxed(lean_object* v_a_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_();
return v_res_1191_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1192_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0);
v___x_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0(lean_object* v_00_u03b2_1195_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1);
return v___x_1196_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1197_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0);
v___x_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1(lean_object* v_00_u03b2_1200_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1);
return v___x_1201_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__0(void){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_1202_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__1(void){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0(lean_box(0));
return v___x_1203_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__2(void){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1(lean_box(0));
return v___x_1204_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__3(void){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1205_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__4(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__3, &l_Lean_Meta_SplitIf_getSimpContext___closed__3_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__3);
v___x_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
return v___x_1207_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__5(void){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v_s_1212_; 
v___x_1208_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__4, &l_Lean_Meta_SplitIf_getSimpContext___closed__4_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__4);
v___x_1209_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__2, &l_Lean_Meta_SplitIf_getSimpContext___closed__2_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__2);
v___x_1210_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__1, &l_Lean_Meta_SplitIf_getSimpContext___closed__1_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__1);
v___x_1211_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__0, &l_Lean_Meta_SplitIf_getSimpContext___closed__0_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__0);
v_s_1212_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_s_1212_, 0, v___x_1211_);
lean_ctor_set(v_s_1212_, 1, v___x_1211_);
lean_ctor_set(v_s_1212_, 2, v___x_1210_);
lean_ctor_set(v_s_1212_, 3, v___x_1209_);
lean_ctor_set(v_s_1212_, 4, v___x_1210_);
lean_ctor_set(v_s_1212_, 5, v___x_1208_);
return v_s_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_getSimpContext(lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v_s_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; uint8_t v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v_s_1230_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__5, &l_Lean_Meta_SplitIf_getSimpContext___closed__5_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__5);
v___x_1231_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__7));
v___x_1232_ = 1;
v___x_1233_ = 0;
v___x_1234_ = lean_unsigned_to_nat(1000u);
v___x_1235_ = l_Lean_Meta_SimpTheorems_addConst(v_s_1230_, v___x_1231_, v___x_1232_, v___x_1233_, v___x_1234_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_a_1236_);
lean_dec_ref_known(v___x_1235_, 1);
v___x_1237_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__9));
v___x_1238_ = l_Lean_Meta_SimpTheorems_addConst(v_a_1236_, v___x_1237_, v___x_1232_, v___x_1233_, v___x_1234_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref_known(v___x_1238_, 1);
v___x_1240_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__11));
v___x_1241_ = l_Lean_Meta_SimpTheorems_addConst(v_a_1239_, v___x_1240_, v___x_1232_, v___x_1233_, v___x_1234_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___x_1241_, 1);
v___x_1243_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__13));
v___x_1244_ = l_Lean_Meta_SimpTheorems_addConst(v_a_1242_, v___x_1243_, v___x_1232_, v___x_1233_, v___x_1234_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1246_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref_known(v___x_1244_, 1);
v___x_1246_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_1228_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1248_; lean_object* v_maxSteps_1249_; lean_object* v_maxDischargeDepth_1250_; uint8_t v_contextual_1251_; uint8_t v_memoize_1252_; uint8_t v_singlePass_1253_; uint8_t v_zeta_1254_; uint8_t v_beta_1255_; uint8_t v_eta_1256_; uint8_t v_etaStruct_1257_; uint8_t v_iota_1258_; uint8_t v_proj_1259_; uint8_t v_decide_1260_; uint8_t v_arith_1261_; uint8_t v_autoUnfold_1262_; uint8_t v_failIfUnchanged_1263_; uint8_t v_ground_1264_; uint8_t v_unfoldPartialApp_1265_; uint8_t v_zetaDelta_1266_; uint8_t v_index_1267_; uint8_t v_implicitDefEqProofs_1268_; uint8_t v_zetaUnused_1269_; uint8_t v_catchRuntime_1270_; uint8_t v_zetaHave_1271_; uint8_t v_congrConsts_1272_; uint8_t v_bitVecOfNat_1273_; uint8_t v_warnExponents_1274_; uint8_t v_suggestions_1275_; lean_object* v_maxSuggestions_1276_; uint8_t v_locals_1277_; uint8_t v_instances_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref_known(v___x_1246_, 1);
v___x_1248_ = l_Lean_Meta_Simp_neutralConfig;
v_maxSteps_1249_ = lean_ctor_get(v___x_1248_, 0);
v_maxDischargeDepth_1250_ = lean_ctor_get(v___x_1248_, 1);
v_contextual_1251_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*3);
v_memoize_1252_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*3 + 1);
v_singlePass_1253_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*3 + 2);
v_zeta_1254_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*3 + 3);
v_beta_1255_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*3 + 4);
v_eta_1256_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*3 + 5);
v_etaStruct_1257_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*3 + 6);
v_iota_1258_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*3 + 7);
v_proj_1259_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*3 + 8);
v_decide_1260_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*3 + 9);
v_arith_1261_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*3 + 10);
v_autoUnfold_1262_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*3 + 11);
v_failIfUnchanged_1263_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*3 + 13);
v_ground_1264_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_1265_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*3 + 15);
v_zetaDelta_1266_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*3 + 16);
v_index_1267_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_1268_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*3 + 18);
v_zetaUnused_1269_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*3 + 19);
v_catchRuntime_1270_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*3 + 20);
v_zetaHave_1271_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*3 + 21);
v_congrConsts_1272_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*3 + 23);
v_bitVecOfNat_1273_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*3 + 24);
v_warnExponents_1274_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*3 + 25);
v_suggestions_1275_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*3 + 26);
v_maxSuggestions_1276_ = lean_ctor_get(v___x_1248_, 2);
v_locals_1277_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*3 + 27);
v_instances_1278_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*3 + 28);
lean_inc(v_maxSuggestions_1276_);
lean_inc(v_maxDischargeDepth_1250_);
lean_inc(v_maxSteps_1249_);
v___x_1279_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1279_, 0, v_maxSteps_1249_);
lean_ctor_set(v___x_1279_, 1, v_maxDischargeDepth_1250_);
lean_ctor_set(v___x_1279_, 2, v_maxSuggestions_1276_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3, v_contextual_1251_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3 + 1, v_memoize_1252_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3 + 2, v_singlePass_1253_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3 + 3, v_zeta_1254_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3 + 4, v_beta_1255_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3 + 5, v_eta_1256_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3 + 6, v_etaStruct_1257_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3 + 7, v_iota_1258_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3 + 8, v_proj_1259_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3 + 9, v_decide_1260_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3 + 10, v_arith_1261_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3 + 11, v_autoUnfold_1262_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3 + 12, v___x_1233_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3 + 13, v_failIfUnchanged_1263_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3 + 14, v_ground_1264_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3 + 15, v_unfoldPartialApp_1265_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3 + 16, v_zetaDelta_1266_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3 + 17, v_index_1267_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_1268_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3 + 19, v_zetaUnused_1269_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3 + 20, v_catchRuntime_1270_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3 + 21, v_zetaHave_1271_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3 + 22, v___x_1232_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3 + 23, v_congrConsts_1272_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3 + 24, v_bitVecOfNat_1273_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3 + 25, v_warnExponents_1274_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3 + 26, v_suggestions_1275_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3 + 27, v_locals_1277_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3 + 28, v_instances_1278_);
v___x_1280_ = lean_unsigned_to_nat(1u);
v___x_1281_ = lean_mk_empty_array_with_capacity(v___x_1280_);
v___x_1282_ = lean_array_push(v___x_1281_, v_a_1245_);
v___x_1283_ = l_Lean_Options_empty;
v___x_1284_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1279_, v___x_1282_, v_a_1247_, v___x_1283_, v_a_1225_, v_a_1227_, v_a_1228_);
return v___x_1284_;
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec(v_a_1245_);
v_a_1285_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1246_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1246_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
else
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
v_a_1293_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1244_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1244_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
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
else
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
v_a_1301_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1241_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1241_);
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
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
v_a_1309_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1238_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1238_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
v_a_1317_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1235_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1235_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_getSimpContext___boxed(lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
lean_dec(v_a_1328_);
lean_dec_ref(v_a_1327_);
lean_dec(v_a_1326_);
lean_dec_ref(v_a_1325_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_1335_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v___x_1339_; lean_object* v_maxSteps_1340_; lean_object* v_maxDischargeDepth_1341_; uint8_t v_contextual_1342_; uint8_t v_memoize_1343_; uint8_t v_singlePass_1344_; uint8_t v_zeta_1345_; uint8_t v_beta_1346_; uint8_t v_eta_1347_; uint8_t v_etaStruct_1348_; uint8_t v_iota_1349_; uint8_t v_proj_1350_; uint8_t v_decide_1351_; uint8_t v_arith_1352_; uint8_t v_autoUnfold_1353_; uint8_t v_failIfUnchanged_1354_; uint8_t v_ground_1355_; uint8_t v_unfoldPartialApp_1356_; uint8_t v_zetaDelta_1357_; uint8_t v_index_1358_; uint8_t v_implicitDefEqProofs_1359_; uint8_t v_zetaUnused_1360_; uint8_t v_catchRuntime_1361_; uint8_t v_zetaHave_1362_; uint8_t v_congrConsts_1363_; uint8_t v_bitVecOfNat_1364_; uint8_t v_warnExponents_1365_; uint8_t v_suggestions_1366_; lean_object* v_maxSuggestions_1367_; uint8_t v_locals_1368_; uint8_t v_instances_1369_; uint8_t v___x_1370_; uint8_t v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
lean_dec_ref_known(v___x_1337_, 1);
v___x_1339_ = l_Lean_Meta_Simp_neutralConfig;
v_maxSteps_1340_ = lean_ctor_get(v___x_1339_, 0);
v_maxDischargeDepth_1341_ = lean_ctor_get(v___x_1339_, 1);
v_contextual_1342_ = lean_ctor_get_uint8(v___x_1339_, sizeof(void*)*3);
v_memoize_1343_ = lean_ctor_get_uint8(v___x_1339_, sizeof(void*)*3 + 1);
v_singlePass_1344_ = lean_ctor_get_uint8(v___x_1339_, sizeof(void*)*3 + 2);
v_zeta_1345_ = lean_ctor_get_uint8(v___x_1339_, sizeof(void*)*3 + 3);
v_beta_1346_ = lean_ctor_get_uint8(v___x_1339_, sizeof(void*)*3 + 4);
v_eta_1347_ = lean_ctor_get_uint8(v___x_1339_, sizeof(void*)*3 + 5);
v_etaStruct_1348_ = lean_ctor_get_uint8(v___x_1339_, sizeof(void*)*3 + 6);
v_iota_1349_ = lean_ctor_get_uint8(v___x_1339_, sizeof(void*)*3 + 7);
v_proj_1350_ = lean_ctor_get_uint8(v___x_1339_, sizeof(void*)*3 + 8);
v_decide_1351_ = lean_ctor_get_uint8(v___x_1339_, sizeof(void*)*3 + 9);
v_arith_1352_ = lean_ctor_get_uint8(v___x_1339_, sizeof(void*)*3 + 10);
v_autoUnfold_1353_ = lean_ctor_get_uint8(v___x_1339_, sizeof(void*)*3 + 11);
v_failIfUnchanged_1354_ = lean_ctor_get_uint8(v___x_1339_, sizeof(void*)*3 + 13);
v_ground_1355_ = lean_ctor_get_uint8(v___x_1339_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_1356_ = lean_ctor_get_uint8(v___x_1339_, sizeof(void*)*3 + 15);
v_zetaDelta_1357_ = lean_ctor_get_uint8(v___x_1339_, sizeof(void*)*3 + 16);
v_index_1358_ = lean_ctor_get_uint8(v___x_1339_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_1359_ = lean_ctor_get_uint8(v___x_1339_, sizeof(void*)*3 + 18);
v_zetaUnused_1360_ = lean_ctor_get_uint8(v___x_1339_, sizeof(void*)*3 + 19);
v_catchRuntime_1361_ = lean_ctor_get_uint8(v___x_1339_, sizeof(void*)*3 + 20);
v_zetaHave_1362_ = lean_ctor_get_uint8(v___x_1339_, sizeof(void*)*3 + 21);
v_congrConsts_1363_ = lean_ctor_get_uint8(v___x_1339_, sizeof(void*)*3 + 23);
v_bitVecOfNat_1364_ = lean_ctor_get_uint8(v___x_1339_, sizeof(void*)*3 + 24);
v_warnExponents_1365_ = lean_ctor_get_uint8(v___x_1339_, sizeof(void*)*3 + 25);
v_suggestions_1366_ = lean_ctor_get_uint8(v___x_1339_, sizeof(void*)*3 + 26);
v_maxSuggestions_1367_ = lean_ctor_get(v___x_1339_, 2);
v_locals_1368_ = lean_ctor_get_uint8(v___x_1339_, sizeof(void*)*3 + 27);
v_instances_1369_ = lean_ctor_get_uint8(v___x_1339_, sizeof(void*)*3 + 28);
v___x_1370_ = 0;
v___x_1371_ = 1;
lean_inc(v_maxSuggestions_1367_);
lean_inc(v_maxDischargeDepth_1341_);
lean_inc(v_maxSteps_1340_);
v___x_1372_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1372_, 0, v_maxSteps_1340_);
lean_ctor_set(v___x_1372_, 1, v_maxDischargeDepth_1341_);
lean_ctor_set(v___x_1372_, 2, v_maxSuggestions_1367_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3, v_contextual_1342_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 1, v_memoize_1343_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 2, v_singlePass_1344_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 3, v_zeta_1345_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 4, v_beta_1346_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 5, v_eta_1347_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 6, v_etaStruct_1348_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 7, v_iota_1349_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 8, v_proj_1350_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 9, v_decide_1351_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 10, v_arith_1352_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 11, v_autoUnfold_1353_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 12, v___x_1370_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 13, v_failIfUnchanged_1354_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 14, v_ground_1355_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 15, v_unfoldPartialApp_1356_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 16, v_zetaDelta_1357_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 17, v_index_1358_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_1359_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 19, v_zetaUnused_1360_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 20, v_catchRuntime_1361_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 21, v_zetaHave_1362_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 22, v___x_1371_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 23, v_congrConsts_1363_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 24, v_bitVecOfNat_1364_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 25, v_warnExponents_1365_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 26, v_suggestions_1366_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 27, v_locals_1368_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 28, v_instances_1369_);
v___x_1373_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg___closed__0));
v___x_1374_ = l_Lean_Options_empty;
v___x_1375_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1372_, v___x_1373_, v_a_1338_, v___x_1374_, v_a_1333_, v_a_1334_, v_a_1335_);
return v___x_1375_;
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
v_a_1376_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1337_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1337_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg___boxed(lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_1384_, v_a_1385_, v_a_1386_);
lean_dec(v_a_1386_);
lean_dec_ref(v_a_1385_);
lean_dec_ref(v_a_1384_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27(lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_1389_, v_a_1391_, v_a_1392_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___boxed(lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27(v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(lean_object* v_e_1401_, lean_object* v___y_1402_){
_start:
{
uint8_t v___x_1404_; uint8_t v___x_1405_; 
v___x_1404_ = l_Lean_Expr_hasMVar(v_e_1401_);
v___x_1405_ = lean_bool_not(v___x_1404_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; lean_object* v_mctx_1407_; lean_object* v___x_1408_; lean_object* v_fst_1409_; lean_object* v_snd_1410_; lean_object* v___x_1411_; lean_object* v_cache_1412_; lean_object* v_zetaDeltaFVarIds_1413_; lean_object* v_postponed_1414_; lean_object* v_diag_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1424_; 
v___x_1406_ = lean_st_ref_get(v___y_1402_);
v_mctx_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc_ref(v_mctx_1407_);
lean_dec(v___x_1406_);
v___x_1408_ = l_Lean_instantiateMVarsCore(v_mctx_1407_, v_e_1401_);
v_fst_1409_ = lean_ctor_get(v___x_1408_, 0);
lean_inc(v_fst_1409_);
v_snd_1410_ = lean_ctor_get(v___x_1408_, 1);
lean_inc(v_snd_1410_);
lean_dec_ref(v___x_1408_);
v___x_1411_ = lean_st_ref_take(v___y_1402_);
v_cache_1412_ = lean_ctor_get(v___x_1411_, 1);
v_zetaDeltaFVarIds_1413_ = lean_ctor_get(v___x_1411_, 2);
v_postponed_1414_ = lean_ctor_get(v___x_1411_, 3);
v_diag_1415_ = lean_ctor_get(v___x_1411_, 4);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1424_ == 0)
{
lean_object* v_unused_1425_; 
v_unused_1425_ = lean_ctor_get(v___x_1411_, 0);
lean_dec(v_unused_1425_);
v___x_1417_ = v___x_1411_;
v_isShared_1418_ = v_isSharedCheck_1424_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_diag_1415_);
lean_inc(v_postponed_1414_);
lean_inc(v_zetaDeltaFVarIds_1413_);
lean_inc(v_cache_1412_);
lean_dec(v___x_1411_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1424_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v_snd_1410_);
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_snd_1410_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_cache_1412_);
lean_ctor_set(v_reuseFailAlloc_1423_, 2, v_zetaDeltaFVarIds_1413_);
lean_ctor_set(v_reuseFailAlloc_1423_, 3, v_postponed_1414_);
lean_ctor_set(v_reuseFailAlloc_1423_, 4, v_diag_1415_);
v___x_1420_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = lean_st_ref_set(v___y_1402_, v___x_1420_);
v___x_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1422_, 0, v_fst_1409_);
return v___x_1422_;
}
}
}
else
{
lean_object* v___x_1426_; 
v___x_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1426_, 0, v_e_1401_);
return v___x_1426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg___boxed(lean_object* v_e_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_e_1427_, v___y_1428_);
lean_dec(v___y_1428_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0(lean_object* v_e_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_e_1431_, v___y_1436_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___boxed(lean_object* v_e_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0(v_e_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(lean_object* v_cls_1451_, lean_object* v_msg_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v_ref_1458_; lean_object* v___x_1459_; lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1504_; 
v_ref_1458_ = lean_ctor_get(v___y_1455_, 5);
v___x_1459_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(v_msg_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1462_ = v___x_1459_;
v_isShared_1463_ = v_isSharedCheck_1504_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1459_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1504_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1464_; lean_object* v_traceState_1465_; lean_object* v_env_1466_; lean_object* v_nextMacroScope_1467_; lean_object* v_ngen_1468_; lean_object* v_auxDeclNGen_1469_; lean_object* v_cache_1470_; lean_object* v_messages_1471_; lean_object* v_infoState_1472_; lean_object* v_snapshotTasks_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1503_; 
v___x_1464_ = lean_st_ref_take(v___y_1456_);
v_traceState_1465_ = lean_ctor_get(v___x_1464_, 4);
v_env_1466_ = lean_ctor_get(v___x_1464_, 0);
v_nextMacroScope_1467_ = lean_ctor_get(v___x_1464_, 1);
v_ngen_1468_ = lean_ctor_get(v___x_1464_, 2);
v_auxDeclNGen_1469_ = lean_ctor_get(v___x_1464_, 3);
v_cache_1470_ = lean_ctor_get(v___x_1464_, 5);
v_messages_1471_ = lean_ctor_get(v___x_1464_, 6);
v_infoState_1472_ = lean_ctor_get(v___x_1464_, 7);
v_snapshotTasks_1473_ = lean_ctor_get(v___x_1464_, 8);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1475_ = v___x_1464_;
v_isShared_1476_ = v_isSharedCheck_1503_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_snapshotTasks_1473_);
lean_inc(v_infoState_1472_);
lean_inc(v_messages_1471_);
lean_inc(v_cache_1470_);
lean_inc(v_traceState_1465_);
lean_inc(v_auxDeclNGen_1469_);
lean_inc(v_ngen_1468_);
lean_inc(v_nextMacroScope_1467_);
lean_inc(v_env_1466_);
lean_dec(v___x_1464_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1503_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
uint64_t v_tid_1477_; lean_object* v_traces_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1502_; 
v_tid_1477_ = lean_ctor_get_uint64(v_traceState_1465_, sizeof(void*)*1);
v_traces_1478_ = lean_ctor_get(v_traceState_1465_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v_traceState_1465_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1480_ = v_traceState_1465_;
v_isShared_1481_ = v_isSharedCheck_1502_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_traces_1478_);
lean_dec(v_traceState_1465_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1502_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; double v___x_1483_; uint8_t v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1492_; 
v___x_1482_ = lean_box(0);
v___x_1483_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0);
v___x_1484_ = 0;
v___x_1485_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__1));
v___x_1486_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1486_, 0, v_cls_1451_);
lean_ctor_set(v___x_1486_, 1, v___x_1482_);
lean_ctor_set(v___x_1486_, 2, v___x_1485_);
lean_ctor_set_float(v___x_1486_, sizeof(void*)*3, v___x_1483_);
lean_ctor_set_float(v___x_1486_, sizeof(void*)*3 + 8, v___x_1483_);
lean_ctor_set_uint8(v___x_1486_, sizeof(void*)*3 + 16, v___x_1484_);
v___x_1487_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__2));
v___x_1488_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1486_);
lean_ctor_set(v___x_1488_, 1, v_a_1460_);
lean_ctor_set(v___x_1488_, 2, v___x_1487_);
lean_inc(v_ref_1458_);
v___x_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1489_, 0, v_ref_1458_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
v___x_1490_ = l_Lean_PersistentArray_push___redArg(v_traces_1478_, v___x_1489_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v___x_1490_);
v___x_1492_ = v___x_1480_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1490_);
lean_ctor_set_uint64(v_reuseFailAlloc_1501_, sizeof(void*)*1, v_tid_1477_);
v___x_1492_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
lean_object* v___x_1494_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 4, v___x_1492_);
v___x_1494_ = v___x_1475_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_env_1466_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_nextMacroScope_1467_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_ngen_1468_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_auxDeclNGen_1469_);
lean_ctor_set(v_reuseFailAlloc_1500_, 4, v___x_1492_);
lean_ctor_set(v_reuseFailAlloc_1500_, 5, v_cache_1470_);
lean_ctor_set(v_reuseFailAlloc_1500_, 6, v_messages_1471_);
lean_ctor_set(v_reuseFailAlloc_1500_, 7, v_infoState_1472_);
lean_ctor_set(v_reuseFailAlloc_1500_, 8, v_snapshotTasks_1473_);
v___x_1494_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1498_; 
v___x_1495_ = lean_st_ref_set(v___y_1456_, v___x_1494_);
v___x_1496_ = lean_box(0);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 0, v___x_1496_);
v___x_1498_ = v___x_1462_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1496_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg___boxed(lean_object* v_cls_1505_, lean_object* v_msg_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v_cls_1505_, v_msg_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
return v_res_1512_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1519_ = lean_box(0);
v___x_1520_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__3));
v___x_1521_ = l_Lean_mkConst(v___x_1520_, v___x_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(lean_object* v_a_1522_, lean_object* v_numIndices_1523_, lean_object* v_as_1524_, lean_object* v_i_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v_zero_1531_; uint8_t v_isZero_1532_; 
v_zero_1531_ = lean_unsigned_to_nat(0u);
v_isZero_1532_ = lean_nat_dec_eq(v_i_1525_, v_zero_1531_);
if (v_isZero_1532_ == 1)
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
lean_dec(v_i_1525_);
lean_dec_ref(v_a_1522_);
v___x_1533_ = lean_box(0);
v___x_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
return v___x_1534_;
}
else
{
lean_object* v_one_1535_; lean_object* v_n_1536_; lean_object* v___x_1537_; 
v_one_1535_ = lean_unsigned_to_nat(1u);
v_n_1536_ = lean_nat_sub(v_i_1525_, v_one_1535_);
lean_dec(v_i_1525_);
v___x_1537_ = lean_array_fget(v_as_1524_, v_n_1536_);
if (lean_obj_tag(v___x_1537_) == 0)
{
v_i_1525_ = v_n_1536_;
goto _start;
}
else
{
lean_object* v_val_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1604_; 
v_val_1539_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1541_ = v___x_1537_;
v_isShared_1542_ = v_isSharedCheck_1604_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_val_1539_);
lean_dec(v___x_1537_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1604_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
uint8_t v___y_1544_; lean_object* v___x_1601_; uint8_t v___x_1602_; 
v___x_1601_ = l_Lean_LocalDecl_index(v_val_1539_);
v___x_1602_ = lean_nat_dec_le(v_numIndices_1523_, v___x_1601_);
lean_dec(v___x_1601_);
if (v___x_1602_ == 0)
{
uint8_t v___x_1603_; 
v___x_1603_ = l_Lean_LocalDecl_isAuxDecl(v_val_1539_);
v___y_1544_ = v___x_1603_;
goto v___jp_1543_;
}
else
{
v___y_1544_ = v___x_1602_;
goto v___jp_1543_;
}
v___jp_1543_:
{
if (v___y_1544_ == 0)
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = l_Lean_LocalDecl_type(v_val_1539_);
lean_inc_ref(v___x_1545_);
lean_inc_ref(v_a_1522_);
v___x_1546_ = l_Lean_Meta_isExprDefEq(v_a_1522_, v___x_1545_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1591_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1549_ = v___x_1546_;
v_isShared_1550_ = v_isSharedCheck_1591_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1546_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1591_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
uint8_t v___x_1551_; 
v___x_1551_ = lean_unbox(v_a_1547_);
lean_dec(v_a_1547_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; uint8_t v___x_1553_; 
lean_del_object(v___x_1549_);
v___x_1552_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__1));
v___x_1553_ = l_Lean_Expr_isAppOfArity(v_a_1522_, v___x_1552_, v_one_1535_);
if (v___x_1553_ == 0)
{
lean_dec_ref(v___x_1545_);
lean_del_object(v___x_1541_);
lean_dec(v_val_1539_);
v_i_1525_ = v_n_1536_;
goto _start;
}
else
{
lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1555_ = l_Lean_Expr_appArg_x21(v_a_1522_);
v___x_1556_ = l_Lean_Expr_isAppOfArity(v___x_1555_, v___x_1552_, v_one_1535_);
if (v___x_1556_ == 0)
{
lean_dec_ref(v___x_1555_);
lean_dec_ref(v___x_1545_);
lean_del_object(v___x_1541_);
lean_dec(v_val_1539_);
v_i_1525_ = v_n_1536_;
goto _start;
}
else
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = l_Lean_Expr_appArg_x21(v___x_1555_);
lean_dec_ref(v___x_1555_);
lean_inc_ref(v___x_1558_);
v___x_1559_ = l_Lean_Meta_isExprDefEq(v___x_1558_, v___x_1545_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1575_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1562_ = v___x_1559_;
v_isShared_1563_ = v_isSharedCheck_1575_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1559_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1575_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
uint8_t v___x_1564_; 
v___x_1564_ = lean_unbox(v_a_1560_);
lean_dec(v_a_1560_);
if (v___x_1564_ == 0)
{
lean_del_object(v___x_1562_);
lean_dec_ref(v___x_1558_);
lean_del_object(v___x_1541_);
lean_dec(v_val_1539_);
v_i_1525_ = v_n_1536_;
goto _start;
}
else
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1570_; 
lean_dec(v_n_1536_);
lean_dec_ref(v_a_1522_);
v___x_1566_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4);
v___x_1567_ = l_Lean_LocalDecl_toExpr(v_val_1539_);
v___x_1568_ = l_Lean_mkAppB(v___x_1566_, v___x_1558_, v___x_1567_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v___x_1568_);
v___x_1570_ = v___x_1541_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
lean_object* v___x_1572_; 
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1570_);
v___x_1572_ = v___x_1562_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1570_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_dec_ref(v___x_1558_);
lean_del_object(v___x_1541_);
lean_dec(v_val_1539_);
lean_dec(v_n_1536_);
lean_dec_ref(v_a_1522_);
v_a_1576_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1559_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1559_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
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
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
}
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1586_; 
lean_dec_ref(v___x_1545_);
lean_dec(v_n_1536_);
lean_dec_ref(v_a_1522_);
v___x_1584_ = l_Lean_LocalDecl_toExpr(v_val_1539_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v___x_1584_);
v___x_1586_ = v___x_1541_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1584_);
v___x_1586_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
lean_object* v___x_1588_; 
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v___x_1586_);
v___x_1588_ = v___x_1549_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
lean_dec_ref(v___x_1545_);
lean_del_object(v___x_1541_);
lean_dec(v_val_1539_);
lean_dec(v_n_1536_);
lean_dec_ref(v_a_1522_);
v_a_1592_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1546_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1546_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
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
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
else
{
lean_del_object(v___x_1541_);
lean_dec(v_val_1539_);
v_i_1525_ = v_n_1536_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_a_1605_, lean_object* v_numIndices_1606_, lean_object* v_as_1607_, lean_object* v_i_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_a_1605_, v_numIndices_1606_, v_as_1607_, v_i_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec_ref(v_as_1607_);
lean_dec(v_numIndices_1606_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(lean_object* v_a_1615_, lean_object* v_numIndices_1616_, lean_object* v_as_1617_, lean_object* v_i_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v_zero_1627_; uint8_t v_isZero_1628_; 
v_zero_1627_ = lean_unsigned_to_nat(0u);
v_isZero_1628_ = lean_nat_dec_eq(v_i_1618_, v_zero_1627_);
if (v_isZero_1628_ == 1)
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
lean_dec(v_i_1618_);
lean_dec_ref(v_a_1615_);
v___x_1629_ = lean_box(0);
v___x_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
return v___x_1630_;
}
else
{
lean_object* v_one_1631_; lean_object* v_n_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v_one_1631_ = lean_unsigned_to_nat(1u);
v_n_1632_ = lean_nat_sub(v_i_1618_, v_one_1631_);
lean_dec(v_i_1618_);
v___x_1633_ = lean_array_fget_borrowed(v_as_1617_, v_n_1632_);
lean_inc_ref(v_a_1615_);
v___x_1634_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_a_1615_, v_numIndices_1616_, v___x_1633_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_a_1635_);
if (lean_obj_tag(v_a_1635_) == 0)
{
lean_dec_ref_known(v___x_1634_, 1);
v_i_1618_ = v_n_1632_;
goto _start;
}
else
{
lean_dec_ref_known(v_a_1635_, 1);
lean_dec(v_n_1632_);
lean_dec_ref(v_a_1615_);
return v___x_1634_;
}
}
else
{
lean_dec(v_n_1632_);
lean_dec_ref(v_a_1615_);
return v___x_1634_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(lean_object* v_a_1637_, lean_object* v_numIndices_1638_, lean_object* v_x_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
if (lean_obj_tag(v_x_1639_) == 0)
{
lean_object* v_cs_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v_cs_1648_ = lean_ctor_get(v_x_1639_, 0);
v___x_1649_ = lean_array_get_size(v_cs_1648_);
v___x_1650_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_a_1637_, v_numIndices_1638_, v_cs_1648_, v___x_1649_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
return v___x_1650_;
}
else
{
lean_object* v_vs_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v_vs_1651_ = lean_ctor_get(v_x_1639_, 0);
v___x_1652_ = lean_array_get_size(v_vs_1651_);
v___x_1653_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_a_1637_, v_numIndices_1638_, v_vs_1651_, v___x_1652_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
return v___x_1653_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3___boxed(lean_object* v_a_1654_, lean_object* v_numIndices_1655_, lean_object* v_x_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_a_1654_, v_numIndices_1655_, v_x_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec_ref(v_x_1656_);
lean_dec(v_numIndices_1655_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_a_1666_, lean_object* v_numIndices_1667_, lean_object* v_as_1668_, lean_object* v_i_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_a_1666_, v_numIndices_1667_, v_as_1668_, v_i_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v_as_1668_);
lean_dec(v_numIndices_1667_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(lean_object* v_a_1679_, lean_object* v_numIndices_1680_, lean_object* v_t_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v_root_1690_; lean_object* v_tail_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v_root_1690_ = lean_ctor_get(v_t_1681_, 0);
v_tail_1691_ = lean_ctor_get(v_t_1681_, 1);
v___x_1692_ = lean_array_get_size(v_tail_1691_);
lean_inc_ref(v_a_1679_);
v___x_1693_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_a_1679_, v_numIndices_1680_, v_tail_1691_, v___x_1692_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1694_);
if (lean_obj_tag(v_a_1694_) == 0)
{
lean_object* v___x_1695_; 
lean_dec_ref_known(v___x_1693_, 1);
v___x_1695_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_a_1679_, v_numIndices_1680_, v_root_1690_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
return v___x_1695_;
}
else
{
lean_dec_ref_known(v_a_1694_, 1);
lean_dec_ref(v_a_1679_);
return v___x_1693_;
}
}
else
{
lean_dec_ref(v_a_1679_);
return v___x_1693_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1___boxed(lean_object* v_a_1696_, lean_object* v_numIndices_1697_, lean_object* v_t_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(v_a_1696_, v_numIndices_1697_, v_t_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v_t_1698_);
lean_dec(v_numIndices_1697_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(lean_object* v_a_1708_, lean_object* v_numIndices_1709_, lean_object* v_lctx_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v_decls_1719_; lean_object* v___x_1720_; 
v_decls_1719_ = lean_ctor_get(v_lctx_1710_, 1);
v___x_1720_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(v_a_1708_, v_numIndices_1709_, v_decls_1719_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1___boxed(lean_object* v_a_1721_, lean_object* v_numIndices_1722_, lean_object* v_lctx_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(v_a_1721_, v_numIndices_1722_, v_lctx_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec_ref(v_lctx_1723_);
lean_dec(v_numIndices_1722_);
return v_res_1732_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3(void){
_start:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1738_ = lean_box(0);
v___x_1739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2));
v___x_1740_ = l_Lean_mkConst(v___x_1739_, v___x_1738_);
return v___x_1740_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6(void){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1744_ = lean_box(0);
v___x_1745_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__5));
v___x_1746_ = l_Lean_mkConst(v___x_1745_, v___x_1744_);
return v___x_1746_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7(void){
_start:
{
uint8_t v___x_1747_; uint64_t v___x_1748_; 
v___x_1747_ = 1;
v___x_1748_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1747_);
return v___x_1748_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11(void){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1755_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10));
v___x_1756_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4));
v___x_1757_ = l_Lean_Name_append(v___x_1756_, v___x_1755_);
return v___x_1757_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13(void){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12));
v___x_1760_ = l_Lean_stringToMessageData(v___x_1759_);
return v___x_1760_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__15(void){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14));
v___x_1763_ = l_Lean_stringToMessageData(v___x_1762_);
return v___x_1763_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__18(void){
_start:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1767_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17));
v___x_1768_ = l_Lean_MessageData_ofFormat(v___x_1767_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(lean_object* v_numIndices_1769_, uint8_t v_useDecide_1770_, lean_object* v_prop_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_){
_start:
{
lean_object* v___x_1780_; lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1954_; 
v___x_1780_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_prop_1771_, v_a_1776_);
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1783_ = v___x_1780_;
v_isShared_1784_ = v_isSharedCheck_1954_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1780_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1954_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v_a_1805_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; uint8_t v___y_1841_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v_options_1922_; uint8_t v_hasTrace_1923_; 
v_options_1922_ = lean_ctor_get(v_a_1777_, 2);
v_hasTrace_1923_ = lean_ctor_get_uint8(v_options_1922_, sizeof(void*)*1);
if (v_hasTrace_1923_ == 0)
{
v___y_1909_ = v_a_1772_;
v___y_1910_ = v_a_1773_;
v___y_1911_ = v_a_1774_;
v___y_1912_ = v_a_1775_;
v___y_1913_ = v_a_1776_;
v___y_1914_ = v_a_1777_;
v___y_1915_ = v_a_1778_;
goto v___jp_1908_;
}
else
{
lean_object* v_inheritedTraceOptions_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; uint8_t v___x_1927_; 
v_inheritedTraceOptions_1924_ = lean_ctor_get(v_a_1777_, 13);
v___x_1925_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10));
v___x_1926_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11);
v___x_1927_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1924_, v_options_1922_, v___x_1926_);
if (v___x_1927_ == 0)
{
v___y_1909_ = v_a_1772_;
v___y_1910_ = v_a_1773_;
v___y_1911_ = v_a_1774_;
v___y_1912_ = v_a_1775_;
v___y_1913_ = v_a_1776_;
v___y_1914_ = v_a_1777_;
v___y_1915_ = v_a_1778_;
goto v___jp_1908_;
}
else
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___y_1934_; lean_object* v___x_1947_; lean_object* v___x_1948_; uint8_t v___x_1949_; 
v___x_1928_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13);
lean_inc(v_a_1781_);
v___x_1929_ = l_Lean_MessageData_ofExpr(v_a_1781_);
v___x_1930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1928_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
v___x_1931_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__15, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__15_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__15);
v___x_1932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1930_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
v___x_1947_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__1));
v___x_1948_ = lean_unsigned_to_nat(1u);
v___x_1949_ = l_Lean_Expr_isAppOfArity(v_a_1781_, v___x_1947_, v___x_1948_);
if (v___x_1949_ == 0)
{
goto v___jp_1945_;
}
else
{
lean_object* v___x_1950_; uint8_t v___x_1951_; 
v___x_1950_ = l_Lean_Expr_appArg_x21(v_a_1781_);
v___x_1951_ = l_Lean_Expr_isAppOfArity(v___x_1950_, v___x_1947_, v___x_1948_);
if (v___x_1951_ == 0)
{
lean_dec_ref(v___x_1950_);
goto v___jp_1945_;
}
else
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1952_ = l_Lean_Expr_appArg_x21(v___x_1950_);
lean_dec_ref(v___x_1950_);
v___x_1953_ = l_Lean_MessageData_ofExpr(v___x_1952_);
v___y_1934_ = v___x_1953_;
goto v___jp_1933_;
}
}
v___jp_1933_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1932_);
lean_ctor_set(v___x_1935_, 1, v___y_1934_);
v___x_1936_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v___x_1925_, v___x_1935_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_dec_ref_known(v___x_1936_, 1);
v___y_1909_ = v_a_1772_;
v___y_1910_ = v_a_1773_;
v___y_1911_ = v_a_1774_;
v___y_1912_ = v_a_1775_;
v___y_1913_ = v_a_1776_;
v___y_1914_ = v_a_1777_;
v___y_1915_ = v_a_1778_;
goto v___jp_1908_;
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
lean_del_object(v___x_1783_);
lean_dec(v_a_1781_);
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1936_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1936_);
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
v___jp_1945_:
{
lean_object* v___x_1946_; 
v___x_1946_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__18, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__18_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__18);
v___y_1934_ = v___x_1946_;
goto v___jp_1933_;
}
}
}
v___jp_1785_:
{
lean_object* v_lctx_1793_; lean_object* v___x_1794_; 
v_lctx_1793_ = lean_ctor_get(v___y_1789_, 2);
v___x_1794_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(v_a_1781_, v_numIndices_1769_, v_lctx_1793_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
return v___x_1794_;
}
v___jp_1795_:
{
lean_object* v___x_1806_; uint8_t v___x_1807_; 
v___x_1806_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2));
v___x_1807_ = l_Lean_Expr_isConstOf(v_a_1805_, v___x_1806_);
lean_dec_ref(v_a_1805_);
if (v___x_1807_ == 0)
{
lean_dec_ref(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_del_object(v___x_1783_);
v___y_1786_ = v___y_1798_;
v___y_1787_ = v___y_1797_;
v___y_1788_ = v___y_1801_;
v___y_1789_ = v___y_1799_;
v___y_1790_ = v___y_1796_;
v___y_1791_ = v___y_1800_;
v___y_1792_ = v___y_1802_;
goto v___jp_1785_;
}
else
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
lean_dec(v_a_1781_);
v___x_1808_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3);
v___x_1809_ = l_Lean_Meta_mkEqRefl(v___x_1808_, v___y_1799_, v___y_1796_, v___y_1800_, v___y_1802_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1823_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1812_ = v___x_1809_;
v_isShared_1813_ = v_isSharedCheck_1823_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1809_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1823_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1818_; 
v___x_1814_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6);
v___x_1815_ = l_Lean_Expr_appArg_x21(v___y_1804_);
lean_dec_ref(v___y_1804_);
v___x_1816_ = l_Lean_mkApp3(v___x_1814_, v___y_1803_, v___x_1815_, v_a_1810_);
if (v_isShared_1784_ == 0)
{
lean_ctor_set_tag(v___x_1783_, 1);
lean_ctor_set(v___x_1783_, 0, v___x_1816_);
v___x_1818_ = v___x_1783_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1816_);
v___x_1818_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___x_1820_; 
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v___x_1818_);
v___x_1820_ = v___x_1812_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1818_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
lean_dec_ref(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_del_object(v___x_1783_);
v_a_1824_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1809_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1809_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
}
v___jp_1832_:
{
if (v___y_1841_ == 0)
{
lean_dec_ref(v___y_1840_);
lean_del_object(v___x_1783_);
v___y_1786_ = v___y_1835_;
v___y_1787_ = v___y_1834_;
v___y_1788_ = v___y_1838_;
v___y_1789_ = v___y_1836_;
v___y_1790_ = v___y_1833_;
v___y_1791_ = v___y_1837_;
v___y_1792_ = v___y_1839_;
goto v___jp_1785_;
}
else
{
lean_object* v___x_1842_; 
lean_inc_ref(v___y_1840_);
v___x_1842_ = l_Lean_Meta_mkDecide(v___y_1840_, v___y_1836_, v___y_1833_, v___y_1837_, v___y_1839_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; lean_object* v___x_1844_; uint8_t v_foApprox_1845_; uint8_t v_ctxApprox_1846_; uint8_t v_quasiPatternApprox_1847_; uint8_t v_constApprox_1848_; uint8_t v_isDefEqStuckEx_1849_; uint8_t v_unificationHints_1850_; uint8_t v_proofIrrelevance_1851_; uint8_t v_assignSyntheticOpaque_1852_; uint8_t v_offsetCnstrs_1853_; uint8_t v_etaStruct_1854_; uint8_t v_univApprox_1855_; uint8_t v_iota_1856_; uint8_t v_beta_1857_; uint8_t v_proj_1858_; uint8_t v_zeta_1859_; uint8_t v_zetaDelta_1860_; uint8_t v_zetaUnused_1861_; uint8_t v_zetaHave_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1899_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
lean_inc(v_a_1843_);
lean_dec_ref_known(v___x_1842_, 1);
v___x_1844_ = l_Lean_Meta_Context_config(v___y_1836_);
v_foApprox_1845_ = lean_ctor_get_uint8(v___x_1844_, 0);
v_ctxApprox_1846_ = lean_ctor_get_uint8(v___x_1844_, 1);
v_quasiPatternApprox_1847_ = lean_ctor_get_uint8(v___x_1844_, 2);
v_constApprox_1848_ = lean_ctor_get_uint8(v___x_1844_, 3);
v_isDefEqStuckEx_1849_ = lean_ctor_get_uint8(v___x_1844_, 4);
v_unificationHints_1850_ = lean_ctor_get_uint8(v___x_1844_, 5);
v_proofIrrelevance_1851_ = lean_ctor_get_uint8(v___x_1844_, 6);
v_assignSyntheticOpaque_1852_ = lean_ctor_get_uint8(v___x_1844_, 7);
v_offsetCnstrs_1853_ = lean_ctor_get_uint8(v___x_1844_, 8);
v_etaStruct_1854_ = lean_ctor_get_uint8(v___x_1844_, 10);
v_univApprox_1855_ = lean_ctor_get_uint8(v___x_1844_, 11);
v_iota_1856_ = lean_ctor_get_uint8(v___x_1844_, 12);
v_beta_1857_ = lean_ctor_get_uint8(v___x_1844_, 13);
v_proj_1858_ = lean_ctor_get_uint8(v___x_1844_, 14);
v_zeta_1859_ = lean_ctor_get_uint8(v___x_1844_, 15);
v_zetaDelta_1860_ = lean_ctor_get_uint8(v___x_1844_, 16);
v_zetaUnused_1861_ = lean_ctor_get_uint8(v___x_1844_, 17);
v_zetaHave_1862_ = lean_ctor_get_uint8(v___x_1844_, 18);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1864_ = v___x_1844_;
v_isShared_1865_ = v_isSharedCheck_1899_;
goto v_resetjp_1863_;
}
else
{
lean_dec(v___x_1844_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1899_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
uint8_t v_trackZetaDelta_1866_; lean_object* v_zetaDeltaSet_1867_; lean_object* v_lctx_1868_; lean_object* v_localInstances_1869_; lean_object* v_defEqCtx_x3f_1870_; lean_object* v_synthPendingDepth_1871_; lean_object* v_canUnfold_x3f_1872_; uint8_t v_univApprox_1873_; uint8_t v_inTypeClassResolution_1874_; uint8_t v_cacheInferType_1875_; uint8_t v___x_1876_; lean_object* v_config_1878_; 
v_trackZetaDelta_1866_ = lean_ctor_get_uint8(v___y_1836_, sizeof(void*)*7);
v_zetaDeltaSet_1867_ = lean_ctor_get(v___y_1836_, 1);
v_lctx_1868_ = lean_ctor_get(v___y_1836_, 2);
v_localInstances_1869_ = lean_ctor_get(v___y_1836_, 3);
v_defEqCtx_x3f_1870_ = lean_ctor_get(v___y_1836_, 4);
v_synthPendingDepth_1871_ = lean_ctor_get(v___y_1836_, 5);
v_canUnfold_x3f_1872_ = lean_ctor_get(v___y_1836_, 6);
v_univApprox_1873_ = lean_ctor_get_uint8(v___y_1836_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1874_ = lean_ctor_get_uint8(v___y_1836_, sizeof(void*)*7 + 2);
v_cacheInferType_1875_ = lean_ctor_get_uint8(v___y_1836_, sizeof(void*)*7 + 3);
v___x_1876_ = 1;
if (v_isShared_1865_ == 0)
{
v_config_1878_ = v___x_1864_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, 0, v_foApprox_1845_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, 1, v_ctxApprox_1846_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, 2, v_quasiPatternApprox_1847_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, 3, v_constApprox_1848_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, 4, v_isDefEqStuckEx_1849_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, 5, v_unificationHints_1850_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, 6, v_proofIrrelevance_1851_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, 7, v_assignSyntheticOpaque_1852_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, 8, v_offsetCnstrs_1853_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, 10, v_etaStruct_1854_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, 11, v_univApprox_1855_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, 12, v_iota_1856_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, 13, v_beta_1857_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, 14, v_proj_1858_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, 15, v_zeta_1859_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, 16, v_zetaDelta_1860_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, 17, v_zetaUnused_1861_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, 18, v_zetaHave_1862_);
v_config_1878_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
uint64_t v___x_1879_; uint64_t v___x_1880_; uint64_t v___x_1881_; uint64_t v___x_1882_; uint64_t v___x_1883_; uint64_t v_key_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
lean_ctor_set_uint8(v_config_1878_, 9, v___x_1876_);
v___x_1879_ = l_Lean_Meta_Context_configKey(v___y_1836_);
v___x_1880_ = 3ULL;
v___x_1881_ = lean_uint64_shift_right(v___x_1879_, v___x_1880_);
v___x_1882_ = lean_uint64_shift_left(v___x_1881_, v___x_1880_);
v___x_1883_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7);
v_key_1884_ = lean_uint64_lor(v___x_1882_, v___x_1883_);
v___x_1885_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1885_, 0, v_config_1878_);
lean_ctor_set_uint64(v___x_1885_, sizeof(void*)*1, v_key_1884_);
lean_inc(v_canUnfold_x3f_1872_);
lean_inc(v_synthPendingDepth_1871_);
lean_inc(v_defEqCtx_x3f_1870_);
lean_inc_ref(v_localInstances_1869_);
lean_inc_ref(v_lctx_1868_);
lean_inc(v_zetaDeltaSet_1867_);
v___x_1886_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1886_, 0, v___x_1885_);
lean_ctor_set(v___x_1886_, 1, v_zetaDeltaSet_1867_);
lean_ctor_set(v___x_1886_, 2, v_lctx_1868_);
lean_ctor_set(v___x_1886_, 3, v_localInstances_1869_);
lean_ctor_set(v___x_1886_, 4, v_defEqCtx_x3f_1870_);
lean_ctor_set(v___x_1886_, 5, v_synthPendingDepth_1871_);
lean_ctor_set(v___x_1886_, 6, v_canUnfold_x3f_1872_);
lean_ctor_set_uint8(v___x_1886_, sizeof(void*)*7, v_trackZetaDelta_1866_);
lean_ctor_set_uint8(v___x_1886_, sizeof(void*)*7 + 1, v_univApprox_1873_);
lean_ctor_set_uint8(v___x_1886_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1874_);
lean_ctor_set_uint8(v___x_1886_, sizeof(void*)*7 + 3, v_cacheInferType_1875_);
lean_inc(v___y_1839_);
lean_inc_ref(v___y_1837_);
lean_inc(v___y_1833_);
lean_inc(v_a_1843_);
v___x_1887_ = lean_whnf(v_a_1843_, v___x_1886_, v___y_1833_, v___y_1837_, v___y_1839_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1888_);
lean_dec_ref_known(v___x_1887_, 1);
v___y_1796_ = v___y_1833_;
v___y_1797_ = v___y_1834_;
v___y_1798_ = v___y_1835_;
v___y_1799_ = v___y_1836_;
v___y_1800_ = v___y_1837_;
v___y_1801_ = v___y_1838_;
v___y_1802_ = v___y_1839_;
v___y_1803_ = v___y_1840_;
v___y_1804_ = v_a_1843_;
v_a_1805_ = v_a_1888_;
goto v___jp_1795_;
}
else
{
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1889_; 
v_a_1889_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1889_);
lean_dec_ref_known(v___x_1887_, 1);
v___y_1796_ = v___y_1833_;
v___y_1797_ = v___y_1834_;
v___y_1798_ = v___y_1835_;
v___y_1799_ = v___y_1836_;
v___y_1800_ = v___y_1837_;
v___y_1801_ = v___y_1838_;
v___y_1802_ = v___y_1839_;
v___y_1803_ = v___y_1840_;
v___y_1804_ = v_a_1843_;
v_a_1805_ = v_a_1889_;
goto v___jp_1795_;
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_dec(v_a_1843_);
lean_dec_ref(v___y_1840_);
lean_del_object(v___x_1783_);
lean_dec(v_a_1781_);
v_a_1890_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1887_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1887_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
lean_dec_ref(v___y_1840_);
lean_del_object(v___x_1783_);
lean_dec(v_a_1781_);
v_a_1900_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1902_ = v___x_1842_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1842_);
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
v___jp_1908_:
{
if (v_useDecide_1770_ == 0)
{
lean_del_object(v___x_1783_);
v___y_1786_ = v___y_1909_;
v___y_1787_ = v___y_1910_;
v___y_1788_ = v___y_1911_;
v___y_1789_ = v___y_1912_;
v___y_1790_ = v___y_1913_;
v___y_1791_ = v___y_1914_;
v___y_1792_ = v___y_1915_;
goto v___jp_1785_;
}
else
{
lean_object* v___x_1916_; lean_object* v_a_1917_; uint8_t v___x_1918_; uint8_t v___x_1919_; 
lean_inc(v_a_1781_);
v___x_1916_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_a_1781_, v___y_1913_);
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref(v___x_1916_);
v___x_1918_ = l_Lean_Expr_hasFVar(v_a_1917_);
v___x_1919_ = lean_bool_not(v___x_1918_);
if (v___x_1919_ == 0)
{
v___y_1833_ = v___y_1913_;
v___y_1834_ = v___y_1910_;
v___y_1835_ = v___y_1909_;
v___y_1836_ = v___y_1912_;
v___y_1837_ = v___y_1914_;
v___y_1838_ = v___y_1911_;
v___y_1839_ = v___y_1915_;
v___y_1840_ = v_a_1917_;
v___y_1841_ = v___x_1919_;
goto v___jp_1832_;
}
else
{
uint8_t v___x_1920_; uint8_t v___x_1921_; 
v___x_1920_ = l_Lean_Expr_hasMVar(v_a_1917_);
v___x_1921_ = lean_bool_not(v___x_1920_);
v___y_1833_ = v___y_1913_;
v___y_1834_ = v___y_1910_;
v___y_1835_ = v___y_1909_;
v___y_1836_ = v___y_1912_;
v___y_1837_ = v___y_1914_;
v___y_1838_ = v___y_1911_;
v___y_1839_ = v___y_1915_;
v___y_1840_ = v_a_1917_;
v___y_1841_ = v___x_1921_;
goto v___jp_1832_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___boxed(lean_object* v_numIndices_1955_, lean_object* v_useDecide_1956_, lean_object* v_prop_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_){
_start:
{
uint8_t v_useDecide_boxed_1966_; lean_object* v_res_1967_; 
v_useDecide_boxed_1966_ = lean_unbox(v_useDecide_1956_);
v_res_1967_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_1955_, v_useDecide_boxed_1966_, v_prop_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_);
lean_dec(v_a_1964_);
lean_dec_ref(v_a_1963_);
lean_dec(v_a_1962_);
lean_dec_ref(v_a_1961_);
lean_dec(v_a_1960_);
lean_dec_ref(v_a_1959_);
lean_dec(v_a_1958_);
lean_dec(v_numIndices_1955_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2(lean_object* v_cls_1968_, lean_object* v_msg_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v_cls_1968_, v_msg_1969_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___boxed(lean_object* v_cls_1979_, lean_object* v_msg_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2(v_cls_1979_, v_msg_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2(lean_object* v_a_1990_, lean_object* v_numIndices_1991_, lean_object* v_as_1992_, lean_object* v_i_1993_, lean_object* v_a_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v___x_2003_; 
v___x_2003_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_a_1990_, v_numIndices_1991_, v_as_1992_, v_i_1993_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_a_2004_, lean_object* v_numIndices_2005_, lean_object* v_as_2006_, lean_object* v_i_2007_, lean_object* v_a_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2(v_a_2004_, v_numIndices_2005_, v_as_2006_, v_i_2007_, v_a_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v_as_2006_);
lean_dec(v_numIndices_2005_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5(lean_object* v_a_2018_, lean_object* v_numIndices_2019_, lean_object* v_as_2020_, lean_object* v_i_2021_, lean_object* v_a_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v___x_2031_; 
v___x_2031_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_a_2018_, v_numIndices_2019_, v_as_2020_, v_i_2021_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_a_2032_, lean_object* v_numIndices_2033_, lean_object* v_as_2034_, lean_object* v_i_2035_, lean_object* v_a_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5(v_a_2032_, v_numIndices_2033_, v_as_2034_, v_i_2035_, v_a_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v_as_2034_);
lean_dec(v_numIndices_2033_);
return v_res_2045_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3(void){
_start:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2051_ = lean_box(0);
v___x_2052_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__2));
v___x_2053_ = l_Lean_mkConst(v___x_2052_, v___x_2051_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27(lean_object* v_numIndices_2057_, uint8_t v_useDecideBool_2058_, lean_object* v_e_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_){
_start:
{
lean_object* v___x_2068_; 
lean_inc_ref(v_e_2059_);
v___x_2068_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2059_, v_a_2064_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2249_; 
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2071_ = v___x_2068_;
v_isShared_2072_ = v_isSharedCheck_2249_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2068_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2249_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2078_; uint8_t v___x_2079_; 
v___x_2078_ = l_Lean_Expr_cleanupAnnotations(v_a_2069_);
v___x_2079_ = l_Lean_Expr_isApp(v___x_2078_);
if (v___x_2079_ == 0)
{
lean_dec_ref(v___x_2078_);
lean_dec_ref(v_e_2059_);
goto v___jp_2073_;
}
else
{
lean_object* v_arg_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; 
v_arg_2080_ = lean_ctor_get(v___x_2078_, 1);
lean_inc_ref(v_arg_2080_);
v___x_2081_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2078_);
v___x_2082_ = l_Lean_Expr_isApp(v___x_2081_);
if (v___x_2082_ == 0)
{
lean_dec_ref(v___x_2081_);
lean_dec_ref(v_arg_2080_);
lean_dec_ref(v_e_2059_);
goto v___jp_2073_;
}
else
{
lean_object* v_arg_2083_; lean_object* v___x_2084_; uint8_t v___x_2085_; 
v_arg_2083_ = lean_ctor_get(v___x_2081_, 1);
lean_inc_ref(v_arg_2083_);
v___x_2084_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2081_);
v___x_2085_ = l_Lean_Expr_isApp(v___x_2084_);
if (v___x_2085_ == 0)
{
lean_dec_ref(v___x_2084_);
lean_dec_ref(v_arg_2083_);
lean_dec_ref(v_arg_2080_);
lean_dec_ref(v_e_2059_);
goto v___jp_2073_;
}
else
{
lean_object* v_arg_2086_; lean_object* v___x_2087_; uint8_t v___x_2088_; 
v_arg_2086_ = lean_ctor_get(v___x_2084_, 1);
lean_inc_ref(v_arg_2086_);
v___x_2087_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2084_);
v___x_2088_ = l_Lean_Expr_isApp(v___x_2087_);
if (v___x_2088_ == 0)
{
lean_dec_ref(v___x_2087_);
lean_dec_ref(v_arg_2086_);
lean_dec_ref(v_arg_2083_);
lean_dec_ref(v_arg_2080_);
lean_dec_ref(v_e_2059_);
goto v___jp_2073_;
}
else
{
lean_object* v_arg_2089_; lean_object* v___x_2090_; uint8_t v___x_2091_; 
v_arg_2089_ = lean_ctor_get(v___x_2087_, 1);
lean_inc_ref(v_arg_2089_);
v___x_2090_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2087_);
v___x_2091_ = l_Lean_Expr_isApp(v___x_2090_);
if (v___x_2091_ == 0)
{
lean_dec_ref(v___x_2090_);
lean_dec_ref(v_arg_2089_);
lean_dec_ref(v_arg_2086_);
lean_dec_ref(v_arg_2083_);
lean_dec_ref(v_arg_2080_);
lean_dec_ref(v_e_2059_);
goto v___jp_2073_;
}
else
{
lean_object* v_arg_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; uint8_t v___x_2095_; 
v_arg_2092_ = lean_ctor_get(v___x_2090_, 1);
lean_inc_ref(v_arg_2092_);
v___x_2093_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2090_);
v___x_2094_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__2));
v___x_2095_ = l_Lean_Expr_isConstOf(v___x_2093_, v___x_2094_);
if (v___x_2095_ == 0)
{
lean_dec_ref(v___x_2093_);
lean_dec_ref(v_arg_2092_);
lean_dec_ref(v_arg_2089_);
lean_dec_ref(v_arg_2086_);
lean_dec_ref(v_arg_2083_);
lean_dec_ref(v_arg_2080_);
lean_dec_ref(v_e_2059_);
goto v___jp_2073_;
}
else
{
lean_object* v___x_2096_; 
lean_del_object(v___x_2071_);
lean_inc_ref(v_arg_2089_);
v___x_2096_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2057_, v_useDecideBool_2058_, v_arg_2089_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2240_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2099_ = v___x_2096_;
v_isShared_2100_ = v_isSharedCheck_2240_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2096_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2240_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2101_; 
v___x_2101_ = l_Lean_Expr_constLevels_x21(v___x_2093_);
if (lean_obj_tag(v_a_2097_) == 1)
{
lean_object* v_val_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2117_; 
lean_dec_ref(v___x_2093_);
lean_dec_ref(v_e_2059_);
v_val_2102_ = lean_ctor_get(v_a_2097_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v_a_2097_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2104_ = v_a_2097_;
v_isShared_2105_ = v_isSharedCheck_2117_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_val_2102_);
lean_dec(v_a_2097_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2117_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2110_; 
v___x_2106_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__7));
v___x_2107_ = l_Lean_mkConst(v___x_2106_, v___x_2101_);
lean_inc_ref(v_arg_2083_);
v___x_2108_ = l_Lean_mkApp6(v___x_2107_, v_arg_2089_, v_arg_2086_, v_val_2102_, v_arg_2092_, v_arg_2083_, v_arg_2080_);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 0, v___x_2108_);
v___x_2110_ = v___x_2104_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2108_);
v___x_2110_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2114_; 
v___x_2111_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2111_, 0, v_arg_2083_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
lean_ctor_set_uint8(v___x_2111_, sizeof(void*)*2, v___x_2095_);
v___x_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 0, v___x_2112_);
v___x_2114_ = v___x_2099_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v___x_2112_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
else
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
lean_del_object(v___x_2099_);
lean_dec(v_a_2097_);
lean_inc_ref(v_arg_2089_);
v___x_2118_ = l_Lean_mkNot(v_arg_2089_);
v___x_2119_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2057_, v_useDecideBool_2058_, v___x_2118_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2231_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2122_ = v___x_2119_;
v_isShared_2123_ = v_isSharedCheck_2231_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2119_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2231_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
if (lean_obj_tag(v_a_2120_) == 1)
{
lean_object* v_val_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2139_; 
lean_dec_ref(v___x_2093_);
lean_dec_ref(v_e_2059_);
v_val_2124_ = lean_ctor_get(v_a_2120_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v_a_2120_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2126_ = v_a_2120_;
v_isShared_2127_ = v_isSharedCheck_2139_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_val_2124_);
lean_dec(v_a_2120_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2139_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2132_; 
v___x_2128_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__9));
v___x_2129_ = l_Lean_mkConst(v___x_2128_, v___x_2101_);
lean_inc_ref(v_arg_2080_);
v___x_2130_ = l_Lean_mkApp6(v___x_2129_, v_arg_2089_, v_arg_2086_, v_val_2124_, v_arg_2092_, v_arg_2083_, v_arg_2080_);
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 0, v___x_2130_);
v___x_2132_ = v___x_2126_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2130_);
v___x_2132_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2136_; 
v___x_2133_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2133_, 0, v_arg_2080_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
lean_ctor_set_uint8(v___x_2133_, sizeof(void*)*2, v___x_2095_);
v___x_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 0, v___x_2134_);
v___x_2136_ = v___x_2122_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2134_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
else
{
lean_object* v___x_2140_; 
lean_del_object(v___x_2122_);
lean_dec(v_a_2120_);
lean_inc(v_a_2066_);
lean_inc_ref(v_a_2065_);
lean_inc(v_a_2064_);
lean_inc_ref(v_a_2063_);
lean_inc(v_a_2062_);
lean_inc_ref(v_a_2061_);
lean_inc(v_a_2060_);
lean_inc_ref(v_arg_2089_);
v___x_2140_ = lean_simp(v_arg_2089_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2222_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2143_ = v___x_2140_;
v_isShared_2144_ = v_isSharedCheck_2222_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2140_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2222_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v_expr_2145_; uint8_t v___x_2146_; 
v_expr_2145_ = lean_ctor_get(v_a_2141_, 0);
v___x_2146_ = lean_expr_eqv(v_expr_2145_, v_arg_2089_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
lean_del_object(v___x_2143_);
v___x_2147_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3);
lean_inc_ref(v_expr_2145_);
v___x_2148_ = l_Lean_Expr_app___override(v___x_2147_, v_expr_2145_);
v___x_2149_ = lean_box(0);
v___x_2150_ = l_Lean_Meta_trySynthInstance(v___x_2148_, v___x_2149_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2199_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2153_ = v___x_2150_;
v_isShared_2154_ = v_isSharedCheck_2199_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2150_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2199_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
if (lean_obj_tag(v_a_2151_) == 1)
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2185_; 
lean_inc_ref(v_expr_2145_);
lean_del_object(v___x_2153_);
lean_dec_ref(v_e_2059_);
v_a_2155_ = lean_ctor_get(v_a_2151_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v_a_2151_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2157_ = v_a_2151_;
v_isShared_2158_ = v_isSharedCheck_2185_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v_a_2151_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2185_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2159_; 
v___x_2159_ = l_Lean_Meta_Simp_Result_getProof(v_a_2141_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2176_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2162_ = v___x_2159_;
v_isShared_2163_ = v_isSharedCheck_2176_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2159_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2176_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2169_; 
v___x_2164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__5));
v___x_2165_ = l_Lean_mkConst(v___x_2164_, v___x_2101_);
lean_inc_ref(v_arg_2080_);
lean_inc_ref(v_arg_2083_);
lean_inc(v_a_2155_);
lean_inc_ref(v_expr_2145_);
lean_inc_ref(v_arg_2092_);
v___x_2166_ = l_Lean_mkApp8(v___x_2165_, v_arg_2092_, v_arg_2089_, v_expr_2145_, v_arg_2086_, v_a_2155_, v_arg_2083_, v_arg_2080_, v_a_2160_);
v___x_2167_ = l_Lean_mkApp5(v___x_2093_, v_arg_2092_, v_expr_2145_, v_a_2155_, v_arg_2083_, v_arg_2080_);
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 0, v___x_2166_);
v___x_2169_ = v___x_2157_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2166_);
v___x_2169_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2173_; 
v___x_2170_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2170_, 0, v___x_2167_);
lean_ctor_set(v___x_2170_, 1, v___x_2169_);
lean_ctor_set_uint8(v___x_2170_, sizeof(void*)*2, v___x_2095_);
v___x_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2170_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 0, v___x_2171_);
v___x_2173_ = v___x_2162_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2171_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
lean_del_object(v___x_2157_);
lean_dec(v_a_2155_);
lean_dec_ref(v_expr_2145_);
lean_dec(v___x_2101_);
lean_dec_ref(v___x_2093_);
lean_dec_ref(v_arg_2092_);
lean_dec_ref(v_arg_2089_);
lean_dec_ref(v_arg_2086_);
lean_dec_ref(v_arg_2083_);
lean_dec_ref(v_arg_2080_);
v_a_2177_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2159_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2159_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
}
else
{
lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2196_; 
lean_dec(v_a_2151_);
lean_dec(v___x_2101_);
lean_dec_ref(v___x_2093_);
lean_dec_ref(v_arg_2092_);
lean_dec_ref(v_arg_2089_);
lean_dec_ref(v_arg_2086_);
lean_dec_ref(v_arg_2083_);
lean_dec_ref(v_arg_2080_);
v_isSharedCheck_2196_ = !lean_is_exclusive(v_a_2141_);
if (v_isSharedCheck_2196_ == 0)
{
lean_object* v_unused_2197_; lean_object* v_unused_2198_; 
v_unused_2197_ = lean_ctor_get(v_a_2141_, 1);
lean_dec(v_unused_2197_);
v_unused_2198_ = lean_ctor_get(v_a_2141_, 0);
lean_dec(v_unused_2198_);
v___x_2187_ = v_a_2141_;
v_isShared_2188_ = v_isSharedCheck_2196_;
goto v_resetjp_2186_;
}
else
{
lean_dec(v_a_2141_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2196_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 1, v___x_2149_);
lean_ctor_set(v___x_2187_, 0, v_e_2059_);
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_e_2059_);
lean_ctor_set(v_reuseFailAlloc_2195_, 1, v___x_2149_);
v___x_2190_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
lean_object* v___x_2191_; lean_object* v___x_2193_; 
lean_ctor_set_uint8(v___x_2190_, sizeof(void*)*2, v___x_2095_);
v___x_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 0, v___x_2191_);
v___x_2193_ = v___x_2153_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2191_);
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
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_dec(v_a_2141_);
lean_dec(v___x_2101_);
lean_dec_ref(v___x_2093_);
lean_dec_ref(v_arg_2092_);
lean_dec_ref(v_arg_2089_);
lean_dec_ref(v_arg_2086_);
lean_dec_ref(v_arg_2083_);
lean_dec_ref(v_arg_2080_);
lean_dec_ref(v_e_2059_);
v_a_2200_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2150_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2150_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
else
{
lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2219_; 
lean_dec(v___x_2101_);
lean_dec_ref(v___x_2093_);
lean_dec_ref(v_arg_2092_);
lean_dec_ref(v_arg_2089_);
lean_dec_ref(v_arg_2086_);
lean_dec_ref(v_arg_2083_);
lean_dec_ref(v_arg_2080_);
v_isSharedCheck_2219_ = !lean_is_exclusive(v_a_2141_);
if (v_isSharedCheck_2219_ == 0)
{
lean_object* v_unused_2220_; lean_object* v_unused_2221_; 
v_unused_2220_ = lean_ctor_get(v_a_2141_, 1);
lean_dec(v_unused_2220_);
v_unused_2221_ = lean_ctor_get(v_a_2141_, 0);
lean_dec(v_unused_2221_);
v___x_2209_ = v_a_2141_;
v_isShared_2210_ = v_isSharedCheck_2219_;
goto v_resetjp_2208_;
}
else
{
lean_dec(v_a_2141_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2219_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2211_ = lean_box(0);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 1, v___x_2211_);
lean_ctor_set(v___x_2209_, 0, v_e_2059_);
v___x_2213_ = v___x_2209_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_e_2059_);
lean_ctor_set(v_reuseFailAlloc_2218_, 1, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
lean_object* v___x_2214_; lean_object* v___x_2216_; 
lean_ctor_set_uint8(v___x_2213_, sizeof(void*)*2, v___x_2095_);
v___x_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 0, v___x_2214_);
v___x_2216_ = v___x_2143_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2214_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec(v___x_2101_);
lean_dec_ref(v___x_2093_);
lean_dec_ref(v_arg_2092_);
lean_dec_ref(v_arg_2089_);
lean_dec_ref(v_arg_2086_);
lean_dec_ref(v_arg_2083_);
lean_dec_ref(v_arg_2080_);
lean_dec_ref(v_e_2059_);
v_a_2223_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2140_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2140_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
}
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec(v___x_2101_);
lean_dec_ref(v___x_2093_);
lean_dec_ref(v_arg_2092_);
lean_dec_ref(v_arg_2089_);
lean_dec_ref(v_arg_2086_);
lean_dec_ref(v_arg_2083_);
lean_dec_ref(v_arg_2080_);
lean_dec_ref(v_e_2059_);
v_a_2232_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2119_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2119_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
}
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
lean_dec_ref(v___x_2093_);
lean_dec_ref(v_arg_2092_);
lean_dec_ref(v_arg_2089_);
lean_dec_ref(v_arg_2086_);
lean_dec_ref(v_arg_2083_);
lean_dec_ref(v_arg_2080_);
lean_dec_ref(v_e_2059_);
v_a_2241_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2096_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2096_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
}
}
}
}
}
v___jp_2073_:
{
lean_object* v___x_2074_; lean_object* v___x_2076_; 
v___x_2074_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__0));
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 0, v___x_2074_);
v___x_2076_ = v___x_2071_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2074_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
lean_dec_ref(v_e_2059_);
v_a_2250_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2068_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2068_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___boxed(lean_object* v_numIndices_2258_, lean_object* v_useDecideBool_2259_, lean_object* v_e_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_){
_start:
{
uint8_t v_useDecideBool_boxed_2269_; lean_object* v_res_2270_; 
v_useDecideBool_boxed_2269_ = lean_unbox(v_useDecideBool_2259_);
v_res_2270_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27(v_numIndices_2258_, v_useDecideBool_boxed_2269_, v_e_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_);
lean_dec(v_a_2267_);
lean_dec_ref(v_a_2266_);
lean_dec(v_a_2265_);
lean_dec_ref(v_a_2264_);
lean_dec(v_a_2263_);
lean_dec_ref(v_a_2262_);
lean_dec(v_a_2261_);
lean_dec(v_numIndices_2258_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(lean_object* v_e_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_){
_start:
{
if (lean_obj_tag(v_e_2274_) == 6)
{
lean_object* v_binderName_2278_; lean_object* v___x_2279_; 
v_binderName_2278_ = lean_ctor_get(v_e_2274_, 0);
lean_inc(v_binderName_2278_);
v___x_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2279_, 0, v_binderName_2278_);
return v___x_2279_;
}
else
{
lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2280_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__1));
v___x_2281_ = l_Lean_Core_mkFreshUserName(v___x_2280_, v_a_2275_, v_a_2276_);
return v___x_2281_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___boxed(lean_object* v_e_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_e_2282_, v_a_2283_, v_a_2284_);
lean_dec(v_a_2284_);
lean_dec_ref(v_a_2283_);
lean_dec_ref(v_e_2282_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName(lean_object* v_e_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_e_2287_, v_a_2290_, v_a_2291_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___boxed(lean_object* v_e_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName(v_e_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
lean_dec(v_a_2298_);
lean_dec_ref(v_a_2297_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
lean_dec_ref(v_e_2294_);
return v_res_2300_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3(void){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2306_ = lean_box(0);
v___x_2307_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__2));
v___x_2308_ = l_Lean_mkConst(v___x_2307_, v___x_2306_);
return v___x_2308_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4(void){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2309_ = lean_unsigned_to_nat(0u);
v___x_2310_ = l_Lean_mkBVar(v___x_2309_);
return v___x_2310_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7(void){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2315_ = lean_box(0);
v___x_2316_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__6));
v___x_2317_ = l_Lean_mkConst(v___x_2316_, v___x_2315_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27(lean_object* v_numIndices_2321_, uint8_t v_useDecideBool_2322_, lean_object* v_e_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_){
_start:
{
lean_object* v___x_2332_; 
lean_inc_ref(v_e_2323_);
v___x_2332_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2323_, v_a_2328_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2542_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2335_ = v___x_2332_;
v_isShared_2336_ = v_isSharedCheck_2542_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2332_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2542_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2342_; uint8_t v___x_2343_; 
v___x_2342_ = l_Lean_Expr_cleanupAnnotations(v_a_2333_);
v___x_2343_ = l_Lean_Expr_isApp(v___x_2342_);
if (v___x_2343_ == 0)
{
lean_dec_ref(v___x_2342_);
lean_dec_ref(v_e_2323_);
goto v___jp_2337_;
}
else
{
lean_object* v_arg_2344_; lean_object* v___x_2345_; uint8_t v___x_2346_; 
v_arg_2344_ = lean_ctor_get(v___x_2342_, 1);
lean_inc_ref(v_arg_2344_);
v___x_2345_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2342_);
v___x_2346_ = l_Lean_Expr_isApp(v___x_2345_);
if (v___x_2346_ == 0)
{
lean_dec_ref(v___x_2345_);
lean_dec_ref(v_arg_2344_);
lean_dec_ref(v_e_2323_);
goto v___jp_2337_;
}
else
{
lean_object* v_arg_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; 
v_arg_2347_ = lean_ctor_get(v___x_2345_, 1);
lean_inc_ref(v_arg_2347_);
v___x_2348_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2345_);
v___x_2349_ = l_Lean_Expr_isApp(v___x_2348_);
if (v___x_2349_ == 0)
{
lean_dec_ref(v___x_2348_);
lean_dec_ref(v_arg_2347_);
lean_dec_ref(v_arg_2344_);
lean_dec_ref(v_e_2323_);
goto v___jp_2337_;
}
else
{
lean_object* v_arg_2350_; lean_object* v___x_2351_; uint8_t v___x_2352_; 
v_arg_2350_ = lean_ctor_get(v___x_2348_, 1);
lean_inc_ref(v_arg_2350_);
v___x_2351_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2348_);
v___x_2352_ = l_Lean_Expr_isApp(v___x_2351_);
if (v___x_2352_ == 0)
{
lean_dec_ref(v___x_2351_);
lean_dec_ref(v_arg_2350_);
lean_dec_ref(v_arg_2347_);
lean_dec_ref(v_arg_2344_);
lean_dec_ref(v_e_2323_);
goto v___jp_2337_;
}
else
{
lean_object* v_arg_2353_; lean_object* v___x_2354_; uint8_t v___x_2355_; 
v_arg_2353_ = lean_ctor_get(v___x_2351_, 1);
lean_inc_ref(v_arg_2353_);
v___x_2354_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2351_);
v___x_2355_ = l_Lean_Expr_isApp(v___x_2354_);
if (v___x_2355_ == 0)
{
lean_dec_ref(v___x_2354_);
lean_dec_ref(v_arg_2353_);
lean_dec_ref(v_arg_2350_);
lean_dec_ref(v_arg_2347_);
lean_dec_ref(v_arg_2344_);
lean_dec_ref(v_e_2323_);
goto v___jp_2337_;
}
else
{
lean_object* v_arg_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; uint8_t v___x_2359_; 
v_arg_2356_ = lean_ctor_get(v___x_2354_, 1);
lean_inc_ref(v_arg_2356_);
v___x_2357_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2354_);
v___x_2358_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__4));
v___x_2359_ = l_Lean_Expr_isConstOf(v___x_2357_, v___x_2358_);
if (v___x_2359_ == 0)
{
lean_dec_ref(v___x_2357_);
lean_dec_ref(v_arg_2356_);
lean_dec_ref(v_arg_2353_);
lean_dec_ref(v_arg_2350_);
lean_dec_ref(v_arg_2347_);
lean_dec_ref(v_arg_2344_);
lean_dec_ref(v_e_2323_);
goto v___jp_2337_;
}
else
{
lean_object* v___x_2360_; 
lean_del_object(v___x_2335_);
lean_inc_ref(v_arg_2353_);
v___x_2360_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2321_, v_useDecideBool_2322_, v_arg_2353_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2533_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2363_ = v___x_2360_;
v_isShared_2364_ = v_isSharedCheck_2533_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2360_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2533_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2365_; 
v___x_2365_ = l_Lean_Expr_constLevels_x21(v___x_2357_);
if (lean_obj_tag(v_a_2361_) == 1)
{
lean_object* v_val_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2383_; 
lean_dec_ref(v___x_2357_);
lean_dec_ref(v_e_2323_);
v_val_2366_ = lean_ctor_get(v_a_2361_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v_a_2361_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2368_ = v_a_2361_;
v_isShared_2369_ = v_isSharedCheck_2383_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_val_2366_);
lean_dec(v_a_2361_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2383_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2376_; 
lean_inc(v_val_2366_);
lean_inc_ref(v_arg_2347_);
v___x_2370_ = l_Lean_Expr_app___override(v_arg_2347_, v_val_2366_);
v___x_2371_ = l_Lean_Expr_headBeta(v___x_2370_);
v___x_2372_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__11));
v___x_2373_ = l_Lean_mkConst(v___x_2372_, v___x_2365_);
v___x_2374_ = l_Lean_mkApp6(v___x_2373_, v_arg_2353_, v_arg_2350_, v_val_2366_, v_arg_2356_, v_arg_2347_, v_arg_2344_);
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 0, v___x_2374_);
v___x_2376_ = v___x_2368_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v___x_2374_);
v___x_2376_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2380_; 
v___x_2377_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2377_, 0, v___x_2371_);
lean_ctor_set(v___x_2377_, 1, v___x_2376_);
lean_ctor_set_uint8(v___x_2377_, sizeof(void*)*2, v___x_2359_);
v___x_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 0, v___x_2378_);
v___x_2380_ = v___x_2363_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v___x_2378_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
else
{
lean_object* v___x_2384_; lean_object* v___x_2385_; 
lean_del_object(v___x_2363_);
lean_dec(v_a_2361_);
lean_inc_ref(v_arg_2353_);
v___x_2384_ = l_Lean_mkNot(v_arg_2353_);
v___x_2385_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2321_, v_useDecideBool_2322_, v___x_2384_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2524_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2388_ = v___x_2385_;
v_isShared_2389_ = v_isSharedCheck_2524_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2385_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2524_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
if (lean_obj_tag(v_a_2386_) == 1)
{
lean_object* v_val_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2407_; 
lean_dec_ref(v___x_2357_);
lean_dec_ref(v_e_2323_);
v_val_2390_ = lean_ctor_get(v_a_2386_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v_a_2386_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2392_ = v_a_2386_;
v_isShared_2393_ = v_isSharedCheck_2407_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_val_2390_);
lean_dec(v_a_2386_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2407_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2400_; 
lean_inc(v_val_2390_);
lean_inc_ref(v_arg_2344_);
v___x_2394_ = l_Lean_Expr_app___override(v_arg_2344_, v_val_2390_);
v___x_2395_ = l_Lean_Expr_headBeta(v___x_2394_);
v___x_2396_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__13));
v___x_2397_ = l_Lean_mkConst(v___x_2396_, v___x_2365_);
v___x_2398_ = l_Lean_mkApp6(v___x_2397_, v_arg_2353_, v_arg_2350_, v_val_2390_, v_arg_2356_, v_arg_2347_, v_arg_2344_);
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 0, v___x_2398_);
v___x_2400_ = v___x_2392_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v___x_2398_);
v___x_2400_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2404_; 
v___x_2401_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2401_, 0, v___x_2395_);
lean_ctor_set(v___x_2401_, 1, v___x_2400_);
lean_ctor_set_uint8(v___x_2401_, sizeof(void*)*2, v___x_2359_);
v___x_2402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2401_);
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 0, v___x_2402_);
v___x_2404_ = v___x_2388_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2402_);
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
else
{
lean_object* v___x_2408_; 
lean_del_object(v___x_2388_);
lean_dec(v_a_2386_);
lean_inc(v_a_2330_);
lean_inc_ref(v_a_2329_);
lean_inc(v_a_2328_);
lean_inc_ref(v_a_2327_);
lean_inc(v_a_2326_);
lean_inc_ref(v_a_2325_);
lean_inc(v_a_2324_);
lean_inc_ref(v_arg_2353_);
v___x_2408_ = lean_simp(v_arg_2353_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2515_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2411_ = v___x_2408_;
v_isShared_2412_ = v_isSharedCheck_2515_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2408_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2515_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v_expr_2413_; uint8_t v___x_2414_; 
v_expr_2413_ = lean_ctor_get(v_a_2409_, 0);
v___x_2414_ = lean_expr_eqv(v_expr_2413_, v_arg_2353_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; 
lean_inc_ref(v_expr_2413_);
lean_del_object(v___x_2411_);
v___x_2415_ = l_Lean_Meta_Simp_Result_getProof(v_a_2409_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_a_2416_);
lean_dec_ref_known(v___x_2415_, 1);
v___x_2417_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3);
lean_inc_ref(v_expr_2413_);
v___x_2418_ = l_Lean_Expr_app___override(v___x_2417_, v_expr_2413_);
v___x_2419_ = lean_box(0);
v___x_2420_ = l_Lean_Meta_trySynthInstance(v___x_2418_, v___x_2419_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2484_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2423_ = v___x_2420_;
v_isShared_2424_ = v_isSharedCheck_2484_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2420_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2484_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
if (lean_obj_tag(v_a_2421_) == 1)
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2478_; 
lean_del_object(v___x_2423_);
lean_dec_ref(v_e_2323_);
v_a_2425_ = lean_ctor_get(v_a_2421_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v_a_2421_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2427_ = v_a_2421_;
v_isShared_2428_ = v_isSharedCheck_2478_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v_a_2421_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2478_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2429_; 
v___x_2429_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_arg_2347_, v_a_2329_, v_a_2330_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; lean_object* v___x_2431_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc(v_a_2430_);
lean_dec_ref_known(v___x_2429_, 1);
v___x_2431_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_arg_2344_, v_a_2329_, v_a_2330_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2461_; 
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2434_ = v___x_2431_;
v_isShared_2435_ = v_isSharedCheck_2461_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2431_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2461_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; uint8_t v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2454_; 
v___x_2436_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3);
v___x_2437_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4);
lean_inc_n(v_a_2416_, 2);
lean_inc_ref_n(v_expr_2413_, 5);
lean_inc_ref_n(v_arg_2353_, 2);
v___x_2438_ = l_Lean_mkApp4(v___x_2436_, v_arg_2353_, v_expr_2413_, v_a_2416_, v___x_2437_);
lean_inc_ref(v_arg_2347_);
v___x_2439_ = l_Lean_Expr_app___override(v_arg_2347_, v___x_2438_);
v___x_2440_ = l_Lean_Expr_headBeta(v___x_2439_);
v___x_2441_ = 0;
v___x_2442_ = l_Lean_mkLambda(v_a_2430_, v___x_2441_, v_expr_2413_, v___x_2440_);
v___x_2443_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7);
v___x_2444_ = l_Lean_mkApp4(v___x_2443_, v_arg_2353_, v_expr_2413_, v_a_2416_, v___x_2437_);
lean_inc_ref(v_arg_2344_);
v___x_2445_ = l_Lean_Expr_app___override(v_arg_2344_, v___x_2444_);
v___x_2446_ = l_Lean_Expr_headBeta(v___x_2445_);
v___x_2447_ = l_Lean_mkNot(v_expr_2413_);
v___x_2448_ = l_Lean_mkLambda(v_a_2432_, v___x_2441_, v___x_2447_, v___x_2446_);
lean_inc(v_a_2425_);
lean_inc_ref(v_arg_2356_);
v___x_2449_ = l_Lean_mkApp5(v___x_2357_, v_arg_2356_, v_expr_2413_, v_a_2425_, v___x_2442_, v___x_2448_);
v___x_2450_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__9));
v___x_2451_ = l_Lean_mkConst(v___x_2450_, v___x_2365_);
v___x_2452_ = l_Lean_mkApp8(v___x_2451_, v_arg_2356_, v_arg_2353_, v_expr_2413_, v_arg_2350_, v_a_2425_, v_arg_2347_, v_arg_2344_, v_a_2416_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v___x_2452_);
v___x_2454_ = v___x_2427_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2452_);
v___x_2454_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2458_; 
v___x_2455_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2455_, 0, v___x_2449_);
lean_ctor_set(v___x_2455_, 1, v___x_2454_);
lean_ctor_set_uint8(v___x_2455_, sizeof(void*)*2, v___x_2359_);
v___x_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2455_);
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 0, v___x_2456_);
v___x_2458_ = v___x_2434_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v___x_2456_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_dec(v_a_2430_);
lean_del_object(v___x_2427_);
lean_dec(v_a_2425_);
lean_dec(v_a_2416_);
lean_dec_ref(v_expr_2413_);
lean_dec(v___x_2365_);
lean_dec_ref(v___x_2357_);
lean_dec_ref(v_arg_2356_);
lean_dec_ref(v_arg_2353_);
lean_dec_ref(v_arg_2350_);
lean_dec_ref(v_arg_2347_);
lean_dec_ref(v_arg_2344_);
v_a_2462_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2431_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2431_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
lean_del_object(v___x_2427_);
lean_dec(v_a_2425_);
lean_dec(v_a_2416_);
lean_dec_ref(v_expr_2413_);
lean_dec(v___x_2365_);
lean_dec_ref(v___x_2357_);
lean_dec_ref(v_arg_2356_);
lean_dec_ref(v_arg_2353_);
lean_dec_ref(v_arg_2350_);
lean_dec_ref(v_arg_2347_);
lean_dec_ref(v_arg_2344_);
v_a_2470_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2429_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2429_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
}
else
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2482_; 
lean_dec(v_a_2421_);
lean_dec(v_a_2416_);
lean_dec_ref(v_expr_2413_);
lean_dec(v___x_2365_);
lean_dec_ref(v___x_2357_);
lean_dec_ref(v_arg_2356_);
lean_dec_ref(v_arg_2353_);
lean_dec_ref(v_arg_2350_);
lean_dec_ref(v_arg_2347_);
lean_dec_ref(v_arg_2344_);
v___x_2479_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2479_, 0, v_e_2323_);
lean_ctor_set(v___x_2479_, 1, v___x_2419_);
lean_ctor_set_uint8(v___x_2479_, sizeof(void*)*2, v___x_2359_);
v___x_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 0, v___x_2480_);
v___x_2482_ = v___x_2423_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2480_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
else
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
lean_dec(v_a_2416_);
lean_dec_ref(v_expr_2413_);
lean_dec(v___x_2365_);
lean_dec_ref(v___x_2357_);
lean_dec_ref(v_arg_2356_);
lean_dec_ref(v_arg_2353_);
lean_dec_ref(v_arg_2350_);
lean_dec_ref(v_arg_2347_);
lean_dec_ref(v_arg_2344_);
lean_dec_ref(v_e_2323_);
v_a_2485_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2420_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2420_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
else
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
lean_dec_ref(v_expr_2413_);
lean_dec(v___x_2365_);
lean_dec_ref(v___x_2357_);
lean_dec_ref(v_arg_2356_);
lean_dec_ref(v_arg_2353_);
lean_dec_ref(v_arg_2350_);
lean_dec_ref(v_arg_2347_);
lean_dec_ref(v_arg_2344_);
lean_dec_ref(v_e_2323_);
v_a_2493_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2495_ = v___x_2415_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2415_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2493_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
else
{
lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2512_; 
lean_dec(v___x_2365_);
lean_dec_ref(v___x_2357_);
lean_dec_ref(v_arg_2356_);
lean_dec_ref(v_arg_2353_);
lean_dec_ref(v_arg_2350_);
lean_dec_ref(v_arg_2347_);
lean_dec_ref(v_arg_2344_);
v_isSharedCheck_2512_ = !lean_is_exclusive(v_a_2409_);
if (v_isSharedCheck_2512_ == 0)
{
lean_object* v_unused_2513_; lean_object* v_unused_2514_; 
v_unused_2513_ = lean_ctor_get(v_a_2409_, 1);
lean_dec(v_unused_2513_);
v_unused_2514_ = lean_ctor_get(v_a_2409_, 0);
lean_dec(v_unused_2514_);
v___x_2502_ = v_a_2409_;
v_isShared_2503_ = v_isSharedCheck_2512_;
goto v_resetjp_2501_;
}
else
{
lean_dec(v_a_2409_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2512_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2504_; lean_object* v___x_2506_; 
v___x_2504_ = lean_box(0);
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 1, v___x_2504_);
lean_ctor_set(v___x_2502_, 0, v_e_2323_);
v___x_2506_ = v___x_2502_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_e_2323_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v___x_2504_);
v___x_2506_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
lean_object* v___x_2507_; lean_object* v___x_2509_; 
lean_ctor_set_uint8(v___x_2506_, sizeof(void*)*2, v___x_2359_);
v___x_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2506_);
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 0, v___x_2507_);
v___x_2509_ = v___x_2411_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2507_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
}
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
lean_dec(v___x_2365_);
lean_dec_ref(v___x_2357_);
lean_dec_ref(v_arg_2356_);
lean_dec_ref(v_arg_2353_);
lean_dec_ref(v_arg_2350_);
lean_dec_ref(v_arg_2347_);
lean_dec_ref(v_arg_2344_);
lean_dec_ref(v_e_2323_);
v_a_2516_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2408_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2408_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
}
}
else
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2532_; 
lean_dec(v___x_2365_);
lean_dec_ref(v___x_2357_);
lean_dec_ref(v_arg_2356_);
lean_dec_ref(v_arg_2353_);
lean_dec_ref(v_arg_2350_);
lean_dec_ref(v_arg_2347_);
lean_dec_ref(v_arg_2344_);
lean_dec_ref(v_e_2323_);
v_a_2525_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2527_ = v___x_2385_;
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2385_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2525_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
}
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
lean_dec_ref(v___x_2357_);
lean_dec_ref(v_arg_2356_);
lean_dec_ref(v_arg_2353_);
lean_dec_ref(v_arg_2350_);
lean_dec_ref(v_arg_2347_);
lean_dec_ref(v_arg_2344_);
lean_dec_ref(v_e_2323_);
v_a_2534_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2536_ = v___x_2360_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2360_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
}
}
}
}
}
v___jp_2337_:
{
lean_object* v___x_2338_; lean_object* v___x_2340_; 
v___x_2338_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__0));
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 0, v___x_2338_);
v___x_2340_ = v___x_2335_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2338_);
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
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
lean_dec_ref(v_e_2323_);
v_a_2543_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2332_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2332_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___boxed(lean_object* v_numIndices_2551_, lean_object* v_useDecideBool_2552_, lean_object* v_e_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_){
_start:
{
uint8_t v_useDecideBool_boxed_2562_; lean_object* v_res_2563_; 
v_useDecideBool_boxed_2562_ = lean_unbox(v_useDecideBool_2552_);
v_res_2563_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27(v_numIndices_2551_, v_useDecideBool_boxed_2562_, v_e_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_);
lean_dec(v_a_2560_);
lean_dec_ref(v_a_2559_);
lean_dec(v_a_2558_);
lean_dec_ref(v_a_2557_);
lean_dec(v_a_2556_);
lean_dec_ref(v_a_2555_);
lean_dec(v_a_2554_);
lean_dec(v_numIndices_2551_);
return v_res_2563_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0(void){
_start:
{
lean_object* v___x_2564_; 
v___x_2564_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_2564_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1(void){
_start:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v_s_2567_; 
v___x_2565_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__2, &l_Lean_Meta_SplitIf_getSimpContext___closed__2_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__2);
v___x_2566_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0);
v_s_2567_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_s_2567_, 0, v___x_2566_);
lean_ctor_set(v_s_2567_, 1, v___x_2566_);
lean_ctor_set(v_s_2567_, 2, v___x_2565_);
lean_ctor_set(v_s_2567_, 3, v___x_2565_);
return v_s_2567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(lean_object* v_numIndices_2631_, uint8_t v_useDecide_2632_){
_start:
{
lean_object* v_s_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; uint8_t v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v_s_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v_s_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v_s_2634_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1);
v___x_2635_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__3));
v___x_2636_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__16));
v___x_2637_ = 0;
v___x_2638_ = lean_box(v_useDecide_2632_);
lean_inc(v_numIndices_2631_);
v___x_2639_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___boxed), 11, 2);
lean_closure_set(v___x_2639_, 0, v_numIndices_2631_);
lean_closure_set(v___x_2639_, 1, v___x_2638_);
v___x_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2639_);
v_s_2641_ = l_Lean_Meta_Simp_Simprocs_addCore(v_s_2634_, v___x_2635_, v___x_2636_, v___x_2637_, v___x_2640_);
v___x_2642_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__18));
v___x_2643_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__20));
v___x_2644_ = lean_box(v_useDecide_2632_);
v___x_2645_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___boxed), 11, 2);
lean_closure_set(v___x_2645_, 0, v_numIndices_2631_);
lean_closure_set(v___x_2645_, 1, v___x_2644_);
v___x_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2645_);
v_s_2647_ = l_Lean_Meta_Simp_Simprocs_addCore(v_s_2641_, v___x_2642_, v___x_2643_, v___x_2637_, v___x_2646_);
v___x_2648_ = lean_unsigned_to_nat(1u);
v___x_2649_ = lean_mk_empty_array_with_capacity(v___x_2648_);
v___x_2650_ = lean_array_push(v___x_2649_, v_s_2647_);
v___x_2651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2650_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___boxed(lean_object* v_numIndices_2652_, lean_object* v_useDecide_2653_, lean_object* v_a_2654_){
_start:
{
uint8_t v_useDecide_boxed_2655_; lean_object* v_res_2656_; 
v_useDecide_boxed_2655_ = lean_unbox(v_useDecide_2653_);
v_res_2656_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_numIndices_2652_, v_useDecide_boxed_2655_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs(lean_object* v_numIndices_2657_, uint8_t v_useDecide_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_){
_start:
{
lean_object* v___x_2664_; 
v___x_2664_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_numIndices_2657_, v_useDecide_2658_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___boxed(lean_object* v_numIndices_2665_, lean_object* v_useDecide_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_){
_start:
{
uint8_t v_useDecide_boxed_2672_; lean_object* v_res_2673_; 
v_useDecide_boxed_2672_ = lean_unbox(v_useDecide_2666_);
v_res_2673_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs(v_numIndices_2665_, v_useDecide_boxed_2672_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_);
lean_dec(v_a_2670_);
lean_dec_ref(v_a_2669_);
lean_dec(v_a_2668_);
lean_dec_ref(v_a_2667_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(uint8_t v_useDecide_2674_, lean_object* v_a_2675_){
_start:
{
lean_object* v_lctx_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v_lctx_2677_ = lean_ctor_get(v_a_2675_, 2);
lean_inc_ref(v_lctx_2677_);
v___x_2678_ = lean_local_ctx_num_indices(v_lctx_2677_);
v___x_2679_ = lean_box(v_useDecide_2674_);
v___x_2680_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___boxed), 11, 2);
lean_closure_set(v___x_2680_, 0, v___x_2678_);
lean_closure_set(v___x_2680_, 1, v___x_2679_);
v___x_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2680_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg___boxed(lean_object* v_useDecide_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_){
_start:
{
uint8_t v_useDecide_boxed_2685_; lean_object* v_res_2686_; 
v_useDecide_boxed_2685_ = lean_unbox(v_useDecide_2682_);
v_res_2686_ = l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(v_useDecide_boxed_2685_, v_a_2683_);
lean_dec_ref(v_a_2683_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f(uint8_t v_useDecide_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_){
_start:
{
lean_object* v___x_2693_; 
v___x_2693_ = l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(v_useDecide_2687_, v_a_2688_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed(lean_object* v_useDecide_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_){
_start:
{
uint8_t v_useDecide_boxed_2700_; lean_object* v_res_2701_; 
v_useDecide_boxed_2700_ = lean_unbox(v_useDecide_2694_);
v_res_2701_ = l_Lean_Meta_SplitIf_mkDischarge_x3f(v_useDecide_boxed_2700_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_);
lean_dec(v_a_2698_);
lean_dec_ref(v_a_2697_);
lean_dec(v_a_2696_);
lean_dec_ref(v_a_2695_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(lean_object* v_mvarId_2702_, lean_object* v_x_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2702_, v_x_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2717_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2712_ = v___x_2709_;
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2709_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2715_; 
if (v_isShared_2713_ == 0)
{
v___x_2715_ = v___x_2712_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_a_2710_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
else
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
v_a_2718_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2720_ = v___x_2709_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2709_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_2726_, lean_object* v_x_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2726_, v_x_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0(lean_object* v_00_u03b1_2734_, lean_object* v_mvarId_2735_, lean_object* v_x_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v___x_2742_; 
v___x_2742_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2735_, v_x_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___boxed(lean_object* v_00_u03b1_2743_, lean_object* v_mvarId_2744_, lean_object* v_x_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0(v_00_u03b1_2743_, v_mvarId_2744_, v_x_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
return v_res_2751_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2753_ = ((lean_object*)(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__0));
v___x_2754_ = l_Lean_stringToMessageData(v___x_2753_);
return v___x_2754_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2756_ = ((lean_object*)(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__2));
v___x_2757_ = l_Lean_stringToMessageData(v___x_2756_);
return v___x_2757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0(lean_object* v_e_2758_, lean_object* v_mvarId_2759_, lean_object* v_hName_x3f_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v___x_2769_; lean_object* v_a_2770_; lean_object* v___x_2771_; 
v___x_2769_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_2758_, v___y_2762_);
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
lean_inc_n(v_a_2770_, 2);
lean_dec_ref(v___x_2769_);
v___x_2771_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(v_a_2770_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2772_);
lean_dec_ref_known(v___x_2771_, 1);
if (lean_obj_tag(v_a_2772_) == 1)
{
lean_object* v_val_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2847_; 
lean_dec(v_a_2770_);
v_val_2773_ = lean_ctor_get(v_a_2772_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v_a_2772_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2775_ = v_a_2772_;
v_isShared_2776_ = v_isSharedCheck_2847_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_val_2773_);
lean_dec(v_a_2772_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2847_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v_fst_2777_; lean_object* v_snd_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2846_; 
v_fst_2777_ = lean_ctor_get(v_val_2773_, 0);
v_snd_2778_ = lean_ctor_get(v_val_2773_, 1);
v_isSharedCheck_2846_ = !lean_is_exclusive(v_val_2773_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2780_ = v_val_2773_;
v_isShared_2781_ = v_isSharedCheck_2846_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_snd_2778_);
lean_inc(v_fst_2777_);
lean_dec(v_val_2773_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2846_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v_hName_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; 
if (lean_obj_tag(v_hName_x3f_2760_) == 0)
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__1));
v___x_2835_ = l_Lean_Core_mkFreshUserName(v___x_2834_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v_a_2836_; 
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_a_2836_);
lean_dec_ref_known(v___x_2835_, 1);
v_hName_2809_ = v_a_2836_;
v___y_2810_ = v___y_2761_;
v___y_2811_ = v___y_2762_;
v___y_2812_ = v___y_2763_;
v___y_2813_ = v___y_2764_;
goto v___jp_2808_;
}
else
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
lean_del_object(v___x_2780_);
lean_dec(v_snd_2778_);
lean_dec(v_fst_2777_);
lean_del_object(v___x_2775_);
lean_dec(v_mvarId_2759_);
v_a_2837_ = lean_ctor_get(v___x_2835_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v___x_2835_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2835_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2842_; 
if (v_isShared_2840_ == 0)
{
v___x_2842_ = v___x_2839_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_a_2837_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
}
else
{
lean_object* v_val_2845_; 
v_val_2845_ = lean_ctor_get(v_hName_x3f_2760_, 0);
lean_inc(v_val_2845_);
lean_dec_ref_known(v_hName_x3f_2760_, 1);
v_hName_2809_ = v_val_2845_;
v___y_2810_ = v___y_2761_;
v___y_2811_ = v___y_2762_;
v___y_2812_ = v___y_2763_;
v___y_2813_ = v___y_2764_;
goto v___jp_2808_;
}
v___jp_2782_:
{
lean_object* v___x_2788_; 
v___x_2788_ = l_Lean_MVarId_byCasesDec(v_mvarId_2759_, v_fst_2777_, v_snd_2778_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2799_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2791_ = v___x_2788_;
v_isShared_2792_ = v_isSharedCheck_2799_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2788_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2799_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 0, v_a_2789_);
v___x_2794_ = v___x_2775_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2789_);
v___x_2794_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
lean_object* v___x_2796_; 
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 0, v___x_2794_);
v___x_2796_ = v___x_2791_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2794_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
lean_del_object(v___x_2775_);
v_a_2800_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2788_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2788_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
v___jp_2808_:
{
lean_object* v_options_2814_; uint8_t v_hasTrace_2815_; 
v_options_2814_ = lean_ctor_get(v___y_2812_, 2);
v_hasTrace_2815_ = lean_ctor_get_uint8(v_options_2814_, sizeof(void*)*1);
if (v_hasTrace_2815_ == 0)
{
lean_del_object(v___x_2780_);
v___y_2783_ = v_hName_2809_;
v___y_2784_ = v___y_2810_;
v___y_2785_ = v___y_2811_;
v___y_2786_ = v___y_2812_;
v___y_2787_ = v___y_2813_;
goto v___jp_2782_;
}
else
{
lean_object* v_inheritedTraceOptions_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; uint8_t v___x_2819_; 
v_inheritedTraceOptions_2816_ = lean_ctor_get(v___y_2812_, 13);
v___x_2817_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10));
v___x_2818_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11);
v___x_2819_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2816_, v_options_2814_, v___x_2818_);
if (v___x_2819_ == 0)
{
lean_del_object(v___x_2780_);
v___y_2783_ = v_hName_2809_;
v___y_2784_ = v___y_2810_;
v___y_2785_ = v___y_2811_;
v___y_2786_ = v___y_2812_;
v___y_2787_ = v___y_2813_;
goto v___jp_2782_;
}
else
{
lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2823_; 
v___x_2820_ = lean_obj_once(&l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1, &l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1_once, _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1);
lean_inc(v_snd_2778_);
v___x_2821_ = l_Lean_MessageData_ofExpr(v_snd_2778_);
if (v_isShared_2781_ == 0)
{
lean_ctor_set_tag(v___x_2780_, 7);
lean_ctor_set(v___x_2780_, 1, v___x_2821_);
lean_ctor_set(v___x_2780_, 0, v___x_2820_);
v___x_2823_ = v___x_2780_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2820_);
lean_ctor_set(v_reuseFailAlloc_2833_, 1, v___x_2821_);
v___x_2823_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
lean_object* v___x_2824_; 
v___x_2824_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_2817_, v___x_2823_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_dec_ref_known(v___x_2824_, 1);
v___y_2783_ = v_hName_2809_;
v___y_2784_ = v___y_2810_;
v___y_2785_ = v___y_2811_;
v___y_2786_ = v___y_2812_;
v___y_2787_ = v___y_2813_;
goto v___jp_2782_;
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
lean_dec(v_hName_2809_);
lean_dec(v_snd_2778_);
lean_dec(v_fst_2777_);
lean_del_object(v___x_2775_);
lean_dec(v_mvarId_2759_);
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2824_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2824_);
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
}
}
}
}
}
}
else
{
lean_object* v_options_2848_; uint8_t v_hasTrace_2849_; 
lean_dec(v_a_2772_);
lean_dec(v_hName_x3f_2760_);
lean_dec(v_mvarId_2759_);
v_options_2848_ = lean_ctor_get(v___y_2763_, 2);
v_hasTrace_2849_ = lean_ctor_get_uint8(v_options_2848_, sizeof(void*)*1);
if (v_hasTrace_2849_ == 0)
{
lean_dec(v_a_2770_);
goto v___jp_2766_;
}
else
{
lean_object* v_inheritedTraceOptions_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; uint8_t v___x_2853_; 
v_inheritedTraceOptions_2850_ = lean_ctor_get(v___y_2763_, 13);
v___x_2851_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10));
v___x_2852_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11);
v___x_2853_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2850_, v_options_2848_, v___x_2852_);
if (v___x_2853_ == 0)
{
lean_dec(v_a_2770_);
goto v___jp_2766_;
}
else
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2854_ = lean_obj_once(&l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3, &l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3_once, _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3);
v___x_2855_ = l_Lean_indentExpr(v_a_2770_);
v___x_2856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2854_);
lean_ctor_set(v___x_2856_, 1, v___x_2855_);
v___x_2857_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_2851_, v___x_2856_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_dec_ref_known(v___x_2857_, 1);
goto v___jp_2766_;
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2857_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2857_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
lean_dec(v_a_2770_);
lean_dec(v_hName_x3f_2760_);
lean_dec(v_mvarId_2759_);
v_a_2866_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2771_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2771_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
v___jp_2766_:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = lean_box(0);
v___x_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2767_);
return v___x_2768_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___boxed(lean_object* v_e_2874_, lean_object* v_mvarId_2875_, lean_object* v_hName_x3f_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0(v_e_2874_, v_mvarId_2875_, v_hName_x3f_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f(lean_object* v_mvarId_2883_, lean_object* v_e_2884_, lean_object* v_hName_x3f_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_){
_start:
{
lean_object* v___f_2891_; lean_object* v___x_2892_; 
lean_inc(v_mvarId_2883_);
v___f_2891_ = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2891_, 0, v_e_2884_);
lean_closure_set(v___f_2891_, 1, v_mvarId_2883_);
lean_closure_set(v___f_2891_, 2, v_hName_x3f_2885_);
v___x_2892_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2883_, v___f_2891_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___boxed(lean_object* v_mvarId_2893_, lean_object* v_e_2894_, lean_object* v_hName_x3f_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(v_mvarId_2893_, v_e_2894_, v_hName_x3f_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_);
lean_dec(v_a_2899_);
lean_dec_ref(v_a_2898_);
lean_dec(v_a_2897_);
lean_dec_ref(v_a_2896_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0(lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_){
_start:
{
lean_object* v_lctx_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v_lctx_2907_ = lean_ctor_get(v___y_2902_, 2);
lean_inc_ref(v_lctx_2907_);
lean_dec_ref(v___y_2902_);
v___x_2908_ = lean_local_ctx_num_indices(v_lctx_2907_);
v___x_2909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2908_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0___boxed(lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0(v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(lean_object* v_mvarId_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_){
_start:
{
lean_object* v___f_2923_; lean_object* v___x_2924_; 
v___f_2923_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___closed__0));
v___x_2924_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2917_, v___f_2923_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___boxed(lean_object* v_mvarId_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(v_mvarId_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_);
lean_dec(v_a_2929_);
lean_dec_ref(v_a_2928_);
lean_dec(v_a_2927_);
lean_dec_ref(v_a_2926_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_simpIfTarget_spec__0(lean_object* v_msg_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v___f_2939_; lean_object* v___x_1888__overap_2940_; lean_object* v___x_2941_; 
v___f_2939_ = ((lean_object*)(l_panic___at___00Lean_Meta_simpIfTarget_spec__0___closed__0));
v___x_1888__overap_2940_ = lean_panic_fn_borrowed(v___f_2939_, v_msg_2933_);
lean_inc(v___y_2937_);
lean_inc_ref(v___y_2936_);
lean_inc(v___y_2935_);
lean_inc_ref(v___y_2934_);
v___x_2941_ = lean_apply_5(v___x_1888__overap_2940_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, lean_box(0));
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_simpIfTarget_spec__0___boxed(lean_object* v_msg_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_){
_start:
{
lean_object* v_res_2948_; 
v_res_2948_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v_msg_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
lean_dec(v___y_2946_);
lean_dec_ref(v___y_2945_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
return v_res_2948_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(lean_object* v_opts_2949_, lean_object* v_opt_2950_){
_start:
{
lean_object* v_name_2951_; lean_object* v_defValue_2952_; lean_object* v_map_2953_; lean_object* v___x_2954_; 
v_name_2951_ = lean_ctor_get(v_opt_2950_, 0);
v_defValue_2952_ = lean_ctor_get(v_opt_2950_, 1);
v_map_2953_ = lean_ctor_get(v_opts_2949_, 0);
v___x_2954_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2953_, v_name_2951_);
if (lean_obj_tag(v___x_2954_) == 0)
{
uint8_t v___x_2955_; 
v___x_2955_ = lean_unbox(v_defValue_2952_);
return v___x_2955_;
}
else
{
lean_object* v_val_2956_; 
v_val_2956_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_val_2956_);
lean_dec_ref_known(v___x_2954_, 1);
if (lean_obj_tag(v_val_2956_) == 1)
{
uint8_t v_v_2957_; 
v_v_2957_ = lean_ctor_get_uint8(v_val_2956_, 0);
lean_dec_ref_known(v_val_2956_, 0);
return v_v_2957_;
}
else
{
uint8_t v___x_2958_; 
lean_dec(v_val_2956_);
v___x_2958_ = lean_unbox(v_defValue_2952_);
return v___x_2958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1___boxed(lean_object* v_opts_2959_, lean_object* v_opt_2960_){
_start:
{
uint8_t v_res_2961_; lean_object* v_r_2962_; 
v_res_2961_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v_opts_2959_, v_opt_2960_);
lean_dec_ref(v_opt_2960_);
lean_dec_ref(v_opts_2959_);
v_r_2962_ = lean_box(v_res_2961_);
return v_r_2962_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__0(void){
_start:
{
lean_object* v___x_2963_; 
v___x_2963_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2963_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__1(void){
_start:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2964_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__0, &l_Lean_Meta_simpIfTarget___closed__0_once, _init_l_Lean_Meta_simpIfTarget___closed__0);
v___x_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
return v___x_2965_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__2(void){
_start:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2966_ = lean_unsigned_to_nat(0u);
v___x_2967_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__1, &l_Lean_Meta_simpIfTarget___closed__1_once, _init_l_Lean_Meta_simpIfTarget___closed__1);
v___x_2968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2967_);
lean_ctor_set(v___x_2968_, 1, v___x_2966_);
return v___x_2968_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__3(void){
_start:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2969_ = lean_unsigned_to_nat(32u);
v___x_2970_ = lean_mk_empty_array_with_capacity(v___x_2969_);
v___x_2971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2970_);
return v___x_2971_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__4(void){
_start:
{
size_t v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2972_ = ((size_t)5ULL);
v___x_2973_ = lean_unsigned_to_nat(0u);
v___x_2974_ = lean_unsigned_to_nat(32u);
v___x_2975_ = lean_mk_empty_array_with_capacity(v___x_2974_);
v___x_2976_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__3, &l_Lean_Meta_simpIfTarget___closed__3_once, _init_l_Lean_Meta_simpIfTarget___closed__3);
v___x_2977_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2977_, 0, v___x_2976_);
lean_ctor_set(v___x_2977_, 1, v___x_2975_);
lean_ctor_set(v___x_2977_, 2, v___x_2973_);
lean_ctor_set(v___x_2977_, 3, v___x_2973_);
lean_ctor_set_usize(v___x_2977_, 4, v___x_2972_);
return v___x_2977_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__5(void){
_start:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2978_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__4, &l_Lean_Meta_simpIfTarget___closed__4_once, _init_l_Lean_Meta_simpIfTarget___closed__4);
v___x_2979_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__1, &l_Lean_Meta_simpIfTarget___closed__1_once, _init_l_Lean_Meta_simpIfTarget___closed__1);
v___x_2980_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2979_);
lean_ctor_set(v___x_2980_, 1, v___x_2979_);
lean_ctor_set(v___x_2980_, 2, v___x_2979_);
lean_ctor_set(v___x_2980_, 3, v___x_2978_);
return v___x_2980_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__6(void){
_start:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2981_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__5, &l_Lean_Meta_simpIfTarget___closed__5_once, _init_l_Lean_Meta_simpIfTarget___closed__5);
v___x_2982_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__2, &l_Lean_Meta_simpIfTarget___closed__2_once, _init_l_Lean_Meta_simpIfTarget___closed__2);
v___x_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2982_);
lean_ctor_set(v___x_2983_, 1, v___x_2981_);
return v___x_2983_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__10(void){
_start:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2987_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__9));
v___x_2988_ = lean_unsigned_to_nat(78u);
v___x_2989_ = lean_unsigned_to_nat(289u);
v___x_2990_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__8));
v___x_2991_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_2992_ = l_mkPanicMessageWithDecl(v___x_2991_, v___x_2990_, v___x_2989_, v___x_2988_, v___x_2987_);
return v___x_2992_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__12(void){
_start:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2995_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__9));
v___x_2996_ = lean_unsigned_to_nat(128u);
v___x_2997_ = lean_unsigned_to_nat(293u);
v___x_2998_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__8));
v___x_2999_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_3000_ = l_mkPanicMessageWithDecl(v___x_2999_, v___x_2998_, v___x_2997_, v___x_2996_, v___x_2995_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfTarget(lean_object* v_mvarId_3001_, uint8_t v_useDecide_3002_, uint8_t v_useNewSemantics_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_){
_start:
{
if (v_useNewSemantics_3003_ == 0)
{
lean_object* v_options_3056_; lean_object* v___x_3057_; uint8_t v___x_3058_; uint8_t v___x_3059_; 
v_options_3056_ = lean_ctor_get(v_a_3006_, 2);
v___x_3057_ = l_Lean_Meta_backward_split;
v___x_3058_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v_options_3056_, v___x_3057_);
v___x_3059_ = lean_bool_not(v___x_3058_);
if (v___x_3059_ == 0)
{
lean_object* v___x_3060_; 
v___x_3060_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v_a_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
lean_inc(v_a_3061_);
lean_dec_ref_known(v___x_3060_, 1);
v___x_3062_ = lean_box(v_useDecide_3002_);
v___x_3063_ = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed), 6, 1);
lean_closure_set(v___x_3063_, 0, v___x_3062_);
lean_inc(v_mvarId_3001_);
v___x_3064_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_3001_, v___x_3063_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_object* v_a_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v_a_3065_ = lean_ctor_get(v___x_3064_, 0);
lean_inc(v_a_3065_);
lean_dec_ref_known(v___x_3064_, 1);
v___x_3066_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__11));
v___x_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3067_, 0, v_a_3065_);
v___x_3068_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__6, &l_Lean_Meta_simpIfTarget___closed__6_once, _init_l_Lean_Meta_simpIfTarget___closed__6);
v___x_3069_ = l_Lean_Meta_simpTarget(v_mvarId_3001_, v_a_3061_, v___x_3066_, v___x_3067_, v___x_3059_, v___x_3068_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3081_; 
v_a_3070_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3072_ = v___x_3069_;
v_isShared_3073_ = v_isSharedCheck_3081_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_3069_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3081_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v_fst_3074_; 
v_fst_3074_ = lean_ctor_get(v_a_3070_, 0);
lean_inc(v_fst_3074_);
lean_dec(v_a_3070_);
if (lean_obj_tag(v_fst_3074_) == 1)
{
lean_object* v_val_3075_; lean_object* v___x_3077_; 
v_val_3075_ = lean_ctor_get(v_fst_3074_, 0);
lean_inc(v_val_3075_);
lean_dec_ref_known(v_fst_3074_, 1);
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 0, v_val_3075_);
v___x_3077_ = v___x_3072_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_val_3075_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
else
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
lean_dec(v_fst_3074_);
lean_del_object(v___x_3072_);
v___x_3079_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__12, &l_Lean_Meta_simpIfTarget___closed__12_once, _init_l_Lean_Meta_simpIfTarget___closed__12);
v___x_3080_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3079_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_);
return v___x_3080_;
}
}
}
else
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3089_; 
v_a_3082_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3084_ = v___x_3069_;
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_3069_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3087_; 
if (v_isShared_3085_ == 0)
{
v___x_3087_ = v___x_3084_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_a_3082_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
}
else
{
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3097_; 
lean_dec(v_a_3061_);
lean_dec(v_mvarId_3001_);
v_a_3090_ = lean_ctor_get(v___x_3064_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3092_ = v___x_3064_;
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3064_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3095_; 
if (v_isShared_3093_ == 0)
{
v___x_3095_ = v___x_3092_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_a_3090_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
}
}
else
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
lean_dec(v_mvarId_3001_);
v_a_3098_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_3060_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3060_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3098_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
}
else
{
goto v___jp_3009_;
}
}
else
{
goto v___jp_3009_;
}
v___jp_3009_:
{
lean_object* v___x_3010_; 
v___x_3010_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_3004_, v_a_3006_, v_a_3007_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; lean_object* v___x_3012_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref_known(v___x_3010_, 1);
lean_inc(v_mvarId_3001_);
v___x_3012_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(v_mvarId_3001_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v___x_3014_; lean_object* v_a_3015_; lean_object* v___x_3016_; uint8_t v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_a_3013_);
lean_dec_ref_known(v___x_3012_, 1);
v___x_3014_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_a_3013_, v_useDecide_3002_);
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_a_3015_);
lean_dec_ref(v___x_3014_);
v___x_3016_ = lean_box(0);
v___x_3017_ = 0;
v___x_3018_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__6, &l_Lean_Meta_simpIfTarget___closed__6_once, _init_l_Lean_Meta_simpIfTarget___closed__6);
v___x_3019_ = l_Lean_Meta_simpTarget(v_mvarId_3001_, v_a_3011_, v_a_3015_, v___x_3016_, v___x_3017_, v___x_3018_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3031_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3022_ = v___x_3019_;
v_isShared_3023_ = v_isSharedCheck_3031_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_a_3020_);
lean_dec(v___x_3019_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3031_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v_fst_3024_; 
v_fst_3024_ = lean_ctor_get(v_a_3020_, 0);
lean_inc(v_fst_3024_);
lean_dec(v_a_3020_);
if (lean_obj_tag(v_fst_3024_) == 1)
{
lean_object* v_val_3025_; lean_object* v___x_3027_; 
v_val_3025_ = lean_ctor_get(v_fst_3024_, 0);
lean_inc(v_val_3025_);
lean_dec_ref_known(v_fst_3024_, 1);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 0, v_val_3025_);
v___x_3027_ = v___x_3022_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_val_3025_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
else
{
lean_object* v___x_3029_; lean_object* v___x_3030_; 
lean_dec(v_fst_3024_);
lean_del_object(v___x_3022_);
v___x_3029_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__10, &l_Lean_Meta_simpIfTarget___closed__10_once, _init_l_Lean_Meta_simpIfTarget___closed__10);
v___x_3030_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3029_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_);
return v___x_3030_;
}
}
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
v_a_3032_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_3019_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_3019_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
else
{
lean_object* v_a_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3047_; 
lean_dec(v_a_3011_);
lean_dec(v_mvarId_3001_);
v_a_3040_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3042_ = v___x_3012_;
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_dec(v___x_3012_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3045_; 
if (v_isShared_3043_ == 0)
{
v___x_3045_ = v___x_3042_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_a_3040_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
}
else
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3055_; 
lean_dec(v_mvarId_3001_);
v_a_3048_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3050_ = v___x_3010_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_3010_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3053_; 
if (v_isShared_3051_ == 0)
{
v___x_3053_ = v___x_3050_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_a_3048_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfTarget___boxed(lean_object* v_mvarId_3106_, lean_object* v_useDecide_3107_, lean_object* v_useNewSemantics_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_){
_start:
{
uint8_t v_useDecide_boxed_3114_; uint8_t v_useNewSemantics_boxed_3115_; lean_object* v_res_3116_; 
v_useDecide_boxed_3114_ = lean_unbox(v_useDecide_3107_);
v_useNewSemantics_boxed_3115_ = lean_unbox(v_useNewSemantics_3108_);
v_res_3116_ = l_Lean_Meta_simpIfTarget(v_mvarId_3106_, v_useDecide_boxed_3114_, v_useNewSemantics_boxed_3115_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_);
lean_dec(v_a_3112_);
lean_dec_ref(v_a_3111_);
lean_dec(v_a_3110_);
lean_dec_ref(v_a_3109_);
return v_res_3116_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfLocalDecl___closed__1(void){
_start:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3118_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__9));
v___x_3119_ = lean_unsigned_to_nat(93u);
v___x_3120_ = lean_unsigned_to_nat(305u);
v___x_3121_ = ((lean_object*)(l_Lean_Meta_simpIfLocalDecl___closed__0));
v___x_3122_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_3123_ = l_mkPanicMessageWithDecl(v___x_3122_, v___x_3121_, v___x_3120_, v___x_3119_, v___x_3118_);
return v___x_3123_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfLocalDecl___closed__2(void){
_start:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3124_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__9));
v___x_3125_ = lean_unsigned_to_nat(133u);
v___x_3126_ = lean_unsigned_to_nat(309u);
v___x_3127_ = ((lean_object*)(l_Lean_Meta_simpIfLocalDecl___closed__0));
v___x_3128_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_3129_ = l_mkPanicMessageWithDecl(v___x_3128_, v___x_3127_, v___x_3126_, v___x_3125_, v___x_3124_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfLocalDecl(lean_object* v_mvarId_3130_, lean_object* v_fvarId_3131_, uint8_t v_useNewSemantics_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_){
_start:
{
if (v_useNewSemantics_3132_ == 0)
{
lean_object* v_options_3186_; lean_object* v___x_3187_; uint8_t v___x_3188_; uint8_t v___x_3189_; 
v_options_3186_ = lean_ctor_get(v_a_3135_, 2);
v___x_3187_ = l_Lean_Meta_backward_split;
v___x_3188_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v_options_3186_, v___x_3187_);
v___x_3189_ = lean_bool_not(v___x_3188_);
if (v___x_3189_ == 0)
{
lean_object* v___x_3190_; 
v___x_3190_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v_a_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
lean_inc(v_a_3191_);
lean_dec_ref_known(v___x_3190_, 1);
v___x_3192_ = lean_box(v___x_3189_);
v___x_3193_ = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed), 6, 1);
lean_closure_set(v___x_3193_, 0, v___x_3192_);
lean_inc(v_mvarId_3130_);
v___x_3194_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_3130_, v___x_3193_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_object* v_a_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
lean_inc(v_a_3195_);
lean_dec_ref_known(v___x_3194_, 1);
v___x_3196_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__11));
v___x_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3197_, 0, v_a_3195_);
v___x_3198_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__6, &l_Lean_Meta_simpIfTarget___closed__6_once, _init_l_Lean_Meta_simpIfTarget___closed__6);
v___x_3199_ = l_Lean_Meta_simpLocalDecl(v_mvarId_3130_, v_fvarId_3131_, v_a_3191_, v___x_3196_, v___x_3197_, v___x_3189_, v___x_3198_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3212_; 
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3202_ = v___x_3199_;
v_isShared_3203_ = v_isSharedCheck_3212_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3199_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3212_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v_fst_3204_; 
v_fst_3204_ = lean_ctor_get(v_a_3200_, 0);
lean_inc(v_fst_3204_);
lean_dec(v_a_3200_);
if (lean_obj_tag(v_fst_3204_) == 1)
{
lean_object* v_val_3205_; lean_object* v_snd_3206_; lean_object* v___x_3208_; 
v_val_3205_ = lean_ctor_get(v_fst_3204_, 0);
lean_inc(v_val_3205_);
lean_dec_ref_known(v_fst_3204_, 1);
v_snd_3206_ = lean_ctor_get(v_val_3205_, 1);
lean_inc(v_snd_3206_);
lean_dec(v_val_3205_);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 0, v_snd_3206_);
v___x_3208_ = v___x_3202_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_snd_3206_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
else
{
lean_object* v___x_3210_; lean_object* v___x_3211_; 
lean_dec(v_fst_3204_);
lean_del_object(v___x_3202_);
v___x_3210_ = lean_obj_once(&l_Lean_Meta_simpIfLocalDecl___closed__2, &l_Lean_Meta_simpIfLocalDecl___closed__2_once, _init_l_Lean_Meta_simpIfLocalDecl___closed__2);
v___x_3211_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3210_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_);
return v___x_3211_;
}
}
}
else
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
v_a_3213_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3215_ = v___x_3199_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3199_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3218_; 
if (v_isShared_3216_ == 0)
{
v___x_3218_ = v___x_3215_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
}
else
{
lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3228_; 
lean_dec(v_a_3191_);
lean_dec(v_fvarId_3131_);
lean_dec(v_mvarId_3130_);
v_a_3221_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3223_ = v___x_3194_;
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v___x_3194_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3226_; 
if (v_isShared_3224_ == 0)
{
v___x_3226_ = v___x_3223_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3221_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
}
else
{
lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3236_; 
lean_dec(v_fvarId_3131_);
lean_dec(v_mvarId_3130_);
v_a_3229_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3231_ = v___x_3190_;
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_dec(v___x_3190_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3234_; 
if (v_isShared_3232_ == 0)
{
v___x_3234_ = v___x_3231_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_a_3229_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
}
}
else
{
goto v___jp_3138_;
}
}
else
{
goto v___jp_3138_;
}
v___jp_3138_:
{
lean_object* v___x_3139_; 
v___x_3139_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_3133_, v_a_3135_, v_a_3136_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; lean_object* v___x_3141_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_a_3140_);
lean_dec_ref_known(v___x_3139_, 1);
lean_inc(v_mvarId_3130_);
v___x_3141_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(v_mvarId_3130_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_a_3142_; uint8_t v___x_3143_; lean_object* v___x_3144_; lean_object* v_a_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
lean_inc(v_a_3142_);
lean_dec_ref_known(v___x_3141_, 1);
v___x_3143_ = 0;
v___x_3144_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_a_3142_, v___x_3143_);
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_a_3145_);
lean_dec_ref(v___x_3144_);
v___x_3146_ = lean_box(0);
v___x_3147_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__6, &l_Lean_Meta_simpIfTarget___closed__6_once, _init_l_Lean_Meta_simpIfTarget___closed__6);
v___x_3148_ = l_Lean_Meta_simpLocalDecl(v_mvarId_3130_, v_fvarId_3131_, v_a_3140_, v_a_3145_, v___x_3146_, v___x_3143_, v___x_3147_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_);
if (lean_obj_tag(v___x_3148_) == 0)
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3161_; 
v_a_3149_ = lean_ctor_get(v___x_3148_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3148_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3151_ = v___x_3148_;
v_isShared_3152_ = v_isSharedCheck_3161_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___x_3148_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3161_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v_fst_3153_; 
v_fst_3153_ = lean_ctor_get(v_a_3149_, 0);
lean_inc(v_fst_3153_);
lean_dec(v_a_3149_);
if (lean_obj_tag(v_fst_3153_) == 1)
{
lean_object* v_val_3154_; lean_object* v_snd_3155_; lean_object* v___x_3157_; 
v_val_3154_ = lean_ctor_get(v_fst_3153_, 0);
lean_inc(v_val_3154_);
lean_dec_ref_known(v_fst_3153_, 1);
v_snd_3155_ = lean_ctor_get(v_val_3154_, 1);
lean_inc(v_snd_3155_);
lean_dec(v_val_3154_);
if (v_isShared_3152_ == 0)
{
lean_ctor_set(v___x_3151_, 0, v_snd_3155_);
v___x_3157_ = v___x_3151_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_snd_3155_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
else
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
lean_dec(v_fst_3153_);
lean_del_object(v___x_3151_);
v___x_3159_ = lean_obj_once(&l_Lean_Meta_simpIfLocalDecl___closed__1, &l_Lean_Meta_simpIfLocalDecl___closed__1_once, _init_l_Lean_Meta_simpIfLocalDecl___closed__1);
v___x_3160_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3159_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_);
return v___x_3160_;
}
}
}
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
v_a_3162_ = lean_ctor_get(v___x_3148_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3148_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3148_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3148_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
lean_dec(v_a_3140_);
lean_dec(v_fvarId_3131_);
lean_dec(v_mvarId_3130_);
v_a_3170_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_3141_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3141_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3175_; 
if (v_isShared_3173_ == 0)
{
v___x_3175_ = v___x_3172_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3170_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
}
else
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3185_; 
lean_dec(v_fvarId_3131_);
lean_dec(v_mvarId_3130_);
v_a_3178_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3180_ = v___x_3139_;
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3139_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3183_; 
if (v_isShared_3181_ == 0)
{
v___x_3183_ = v___x_3180_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3178_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfLocalDecl___boxed(lean_object* v_mvarId_3237_, lean_object* v_fvarId_3238_, lean_object* v_useNewSemantics_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_){
_start:
{
uint8_t v_useNewSemantics_boxed_3245_; lean_object* v_res_3246_; 
v_useNewSemantics_boxed_3245_ = lean_unbox(v_useNewSemantics_3239_);
v_res_3246_ = l_Lean_Meta_simpIfLocalDecl(v_mvarId_3237_, v_fvarId_3238_, v_useNewSemantics_boxed_3245_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_);
lean_dec(v_a_3243_);
lean_dec_ref(v_a_3242_);
lean_dec(v_a_3241_);
lean_dec_ref(v_a_3240_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(lean_object* v_x_x3f_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_){
_start:
{
lean_object* v___x_3253_; 
v___x_3253_ = l_Lean_Meta_saveState___redArg(v___y_3249_, v___y_3251_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3298_; 
v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3256_ = v___x_3253_;
v_isShared_3257_ = v_isSharedCheck_3298_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3253_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3298_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___y_3259_; uint8_t v___y_3260_; lean_object* v_a_3282_; lean_object* v___x_3285_; 
lean_inc(v___y_3251_);
lean_inc_ref(v___y_3250_);
lean_inc(v___y_3249_);
lean_inc_ref(v___y_3248_);
v___x_3285_ = lean_apply_5(v_x_x3f_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, lean_box(0));
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v_a_3286_; 
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
lean_inc(v_a_3286_);
if (lean_obj_tag(v_a_3286_) == 0)
{
lean_object* v___x_3287_; 
lean_dec_ref_known(v___x_3285_, 1);
v___x_3287_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3254_, v___y_3249_, v___y_3251_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3294_; 
lean_del_object(v___x_3256_);
lean_dec(v_a_3254_);
v_isSharedCheck_3294_ = !lean_is_exclusive(v___x_3287_);
if (v_isSharedCheck_3294_ == 0)
{
lean_object* v_unused_3295_; 
v_unused_3295_ = lean_ctor_get(v___x_3287_, 0);
lean_dec(v_unused_3295_);
v___x_3289_ = v___x_3287_;
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
else
{
lean_dec(v___x_3287_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v___x_3292_; 
if (v_isShared_3290_ == 0)
{
lean_ctor_set(v___x_3289_, 0, v_a_3286_);
v___x_3292_ = v___x_3289_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_a_3286_);
v___x_3292_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
return v___x_3292_;
}
}
}
else
{
lean_object* v_a_3296_; 
v_a_3296_ = lean_ctor_get(v___x_3287_, 0);
lean_inc(v_a_3296_);
lean_dec_ref_known(v___x_3287_, 1);
v_a_3282_ = v_a_3296_;
goto v___jp_3281_;
}
}
else
{
lean_dec_ref_known(v_a_3286_, 1);
lean_del_object(v___x_3256_);
lean_dec(v_a_3254_);
return v___x_3285_;
}
}
else
{
lean_object* v_a_3297_; 
v_a_3297_ = lean_ctor_get(v___x_3285_, 0);
lean_inc(v_a_3297_);
lean_dec_ref_known(v___x_3285_, 1);
v_a_3282_ = v_a_3297_;
goto v___jp_3281_;
}
v___jp_3258_:
{
if (v___y_3260_ == 0)
{
lean_object* v___x_3261_; 
lean_del_object(v___x_3256_);
v___x_3261_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3254_, v___y_3249_, v___y_3251_);
lean_dec(v_a_3254_);
if (lean_obj_tag(v___x_3261_) == 0)
{
lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3268_; 
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3261_);
if (v_isSharedCheck_3268_ == 0)
{
lean_object* v_unused_3269_; 
v_unused_3269_ = lean_ctor_get(v___x_3261_, 0);
lean_dec(v_unused_3269_);
v___x_3263_ = v___x_3261_;
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
else
{
lean_dec(v___x_3261_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3266_; 
if (v_isShared_3264_ == 0)
{
lean_ctor_set_tag(v___x_3263_, 1);
lean_ctor_set(v___x_3263_, 0, v___y_3259_);
v___x_3266_ = v___x_3263_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v___y_3259_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
else
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3277_; 
lean_dec_ref(v___y_3259_);
v_a_3270_ = lean_ctor_get(v___x_3261_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3261_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3272_ = v___x_3261_;
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3261_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3275_; 
if (v_isShared_3273_ == 0)
{
v___x_3275_ = v___x_3272_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3270_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
}
else
{
lean_object* v___x_3279_; 
lean_dec(v_a_3254_);
if (v_isShared_3257_ == 0)
{
lean_ctor_set_tag(v___x_3256_, 1);
lean_ctor_set(v___x_3256_, 0, v___y_3259_);
v___x_3279_ = v___x_3256_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v___y_3259_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
}
v___jp_3281_:
{
uint8_t v___x_3283_; 
v___x_3283_ = l_Lean_Exception_isInterrupt(v_a_3282_);
if (v___x_3283_ == 0)
{
uint8_t v___x_3284_; 
lean_inc_ref(v_a_3282_);
v___x_3284_ = l_Lean_Exception_isRuntime(v_a_3282_);
v___y_3259_ = v_a_3282_;
v___y_3260_ = v___x_3284_;
goto v___jp_3258_;
}
else
{
v___y_3259_ = v_a_3282_;
v___y_3260_ = v___x_3283_;
goto v___jp_3258_;
}
}
}
}
else
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3306_; 
lean_dec_ref(v_x_x3f_3247_);
v_a_3299_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3301_ = v___x_3253_;
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3253_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3304_; 
if (v_isShared_3302_ == 0)
{
v___x_3304_ = v___x_3301_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_a_3299_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg___boxed(lean_object* v_x_x3f_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v_x_x3f_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0(lean_object* v_00_u03b1_3314_, lean_object* v_x_x3f_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
lean_object* v___x_3321_; 
v___x_3321_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v_x_x3f_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_);
return v___x_3321_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___boxed(lean_object* v_00_u03b1_3322_, lean_object* v_x_x3f_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
lean_object* v_res_3329_; 
v_res_3329_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0(v_00_u03b1_3322_, v_x_x3f_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
return v_res_3329_;
}
}
static lean_object* _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; 
v___x_3334_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1));
v___x_3335_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4));
v___x_3336_ = l_Lean_Name_append(v___x_3335_, v___x_3334_);
return v___x_3336_;
}
}
static lean_object* _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3338_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__3));
v___x_3339_ = l_Lean_stringToMessageData(v___x_3338_);
return v___x_3339_;
}
}
static lean_object* _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3341_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__5));
v___x_3342_ = l_Lean_stringToMessageData(v___x_3341_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0(lean_object* v_mvarId_3343_, lean_object* v_hName_x3f_3344_, uint8_t v_useNewSemantics_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
lean_object* v___x_3354_; 
lean_inc(v_mvarId_3343_);
v___x_3354_ = l_Lean_MVarId_getType(v_mvarId_3343_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_object* v_a_3355_; lean_object* v___x_3356_; 
v_a_3355_ = lean_ctor_get(v___x_3354_, 0);
lean_inc(v_a_3355_);
lean_dec_ref_known(v___x_3354_, 1);
v___x_3356_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(v_mvarId_3343_, v_a_3355_, v_hName_x3f_3344_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3453_; 
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3359_ = v___x_3356_;
v_isShared_3360_ = v_isSharedCheck_3453_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___x_3356_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3453_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
if (lean_obj_tag(v_a_3357_) == 1)
{
lean_object* v_val_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3448_; 
lean_del_object(v___x_3359_);
v_val_3361_ = lean_ctor_get(v_a_3357_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v_a_3357_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3363_ = v_a_3357_;
v_isShared_3364_ = v_isSharedCheck_3448_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_val_3361_);
lean_dec(v_a_3357_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3448_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v_fst_3365_; lean_object* v_snd_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3447_; 
v_fst_3365_ = lean_ctor_get(v_val_3361_, 0);
v_snd_3366_ = lean_ctor_get(v_val_3361_, 1);
v_isSharedCheck_3447_ = !lean_is_exclusive(v_val_3361_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3368_ = v_val_3361_;
v_isShared_3369_ = v_isSharedCheck_3447_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_snd_3366_);
lean_inc(v_fst_3365_);
lean_dec(v_val_3361_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3447_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v_mvarId_3370_; lean_object* v_fvarId_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3446_; 
v_mvarId_3370_ = lean_ctor_get(v_fst_3365_, 0);
v_fvarId_3371_ = lean_ctor_get(v_fst_3365_, 1);
v_isSharedCheck_3446_ = !lean_is_exclusive(v_fst_3365_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3373_ = v_fst_3365_;
v_isShared_3374_ = v_isSharedCheck_3446_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_fvarId_3371_);
lean_inc(v_mvarId_3370_);
lean_dec(v_fst_3365_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3446_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
uint8_t v___x_3375_; lean_object* v___x_3376_; 
v___x_3375_ = 0;
lean_inc(v_mvarId_3370_);
v___x_3376_ = l_Lean_Meta_simpIfTarget(v_mvarId_3370_, v___x_3375_, v_useNewSemantics_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v_a_3377_; lean_object* v_mvarId_3378_; lean_object* v_fvarId_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3437_; 
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
lean_inc(v_a_3377_);
lean_dec_ref_known(v___x_3376_, 1);
v_mvarId_3378_ = lean_ctor_get(v_snd_3366_, 0);
v_fvarId_3379_ = lean_ctor_get(v_snd_3366_, 1);
v_isSharedCheck_3437_ = !lean_is_exclusive(v_snd_3366_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3381_ = v_snd_3366_;
v_isShared_3382_ = v_isSharedCheck_3437_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_fvarId_3379_);
lean_inc(v_mvarId_3378_);
lean_dec(v_snd_3366_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3437_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3383_; 
lean_inc(v_mvarId_3378_);
v___x_3383_ = l_Lean_Meta_simpIfTarget(v_mvarId_3378_, v___x_3375_, v_useNewSemantics_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v_a_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3428_; 
v_a_3384_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3386_ = v___x_3383_;
v_isShared_3387_ = v_isSharedCheck_3428_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_a_3384_);
lean_dec(v___x_3383_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3428_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
uint8_t v___x_3404_; 
v___x_3404_ = l_Lean_instBEqMVarId_beq(v_mvarId_3370_, v_a_3377_);
lean_dec(v_mvarId_3370_);
if (v___x_3404_ == 0)
{
lean_dec(v_mvarId_3378_);
goto v___jp_3388_;
}
else
{
uint8_t v___x_3405_; 
v___x_3405_ = l_Lean_instBEqMVarId_beq(v_mvarId_3378_, v_a_3384_);
lean_dec(v_mvarId_3378_);
if (v___x_3405_ == 0)
{
goto v___jp_3388_;
}
else
{
lean_object* v_options_3406_; uint8_t v_hasTrace_3407_; 
lean_del_object(v___x_3386_);
lean_del_object(v___x_3381_);
lean_dec(v_fvarId_3379_);
lean_del_object(v___x_3373_);
lean_dec(v_fvarId_3371_);
lean_del_object(v___x_3368_);
lean_del_object(v___x_3363_);
v_options_3406_ = lean_ctor_get(v___y_3348_, 2);
v_hasTrace_3407_ = lean_ctor_get_uint8(v_options_3406_, sizeof(void*)*1);
if (v_hasTrace_3407_ == 0)
{
lean_dec(v_a_3384_);
lean_dec(v_a_3377_);
goto v___jp_3351_;
}
else
{
lean_object* v_inheritedTraceOptions_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; uint8_t v___x_3411_; 
v_inheritedTraceOptions_3408_ = lean_ctor_get(v___y_3348_, 13);
v___x_3409_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1));
v___x_3410_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2);
v___x_3411_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3408_, v_options_3406_, v___x_3410_);
if (v___x_3411_ == 0)
{
lean_dec(v_a_3384_);
lean_dec(v_a_3377_);
goto v___jp_3351_;
}
else
{
lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3412_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4);
v___x_3413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3413_, 0, v_a_3377_);
v___x_3414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3412_);
lean_ctor_set(v___x_3414_, 1, v___x_3413_);
v___x_3415_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6);
v___x_3416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3414_);
lean_ctor_set(v___x_3416_, 1, v___x_3415_);
v___x_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3417_, 0, v_a_3384_);
v___x_3418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3416_);
lean_ctor_set(v___x_3418_, 1, v___x_3417_);
v___x_3419_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_3409_, v___x_3418_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_dec_ref_known(v___x_3419_, 1);
goto v___jp_3351_;
}
else
{
lean_object* v_a_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3427_; 
v_a_3420_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3422_ = v___x_3419_;
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_a_3420_);
lean_dec(v___x_3419_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3425_; 
if (v_isShared_3423_ == 0)
{
v___x_3425_ = v___x_3422_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_a_3420_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
}
}
}
}
}
v___jp_3388_:
{
lean_object* v___x_3390_; 
if (v_isShared_3382_ == 0)
{
lean_ctor_set(v___x_3381_, 1, v_fvarId_3371_);
lean_ctor_set(v___x_3381_, 0, v_a_3377_);
v___x_3390_ = v___x_3381_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v_a_3377_);
lean_ctor_set(v_reuseFailAlloc_3403_, 1, v_fvarId_3371_);
v___x_3390_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
lean_object* v___x_3392_; 
if (v_isShared_3374_ == 0)
{
lean_ctor_set(v___x_3373_, 1, v_fvarId_3379_);
lean_ctor_set(v___x_3373_, 0, v_a_3384_);
v___x_3392_ = v___x_3373_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3384_);
lean_ctor_set(v_reuseFailAlloc_3402_, 1, v_fvarId_3379_);
v___x_3392_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
lean_object* v___x_3394_; 
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 1, v___x_3392_);
lean_ctor_set(v___x_3368_, 0, v___x_3390_);
v___x_3394_ = v___x_3368_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v___x_3390_);
lean_ctor_set(v_reuseFailAlloc_3401_, 1, v___x_3392_);
v___x_3394_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
lean_object* v___x_3396_; 
if (v_isShared_3364_ == 0)
{
lean_ctor_set(v___x_3363_, 0, v___x_3394_);
v___x_3396_ = v___x_3363_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v___x_3394_);
v___x_3396_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
lean_object* v___x_3398_; 
if (v_isShared_3387_ == 0)
{
lean_ctor_set(v___x_3386_, 0, v___x_3396_);
v___x_3398_ = v___x_3386_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v___x_3396_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
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
lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3436_; 
lean_del_object(v___x_3381_);
lean_dec(v_fvarId_3379_);
lean_dec(v_mvarId_3378_);
lean_dec(v_a_3377_);
lean_del_object(v___x_3373_);
lean_dec(v_fvarId_3371_);
lean_dec(v_mvarId_3370_);
lean_del_object(v___x_3368_);
lean_del_object(v___x_3363_);
v_a_3429_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3431_ = v___x_3383_;
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_dec(v___x_3383_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3434_; 
if (v_isShared_3432_ == 0)
{
v___x_3434_ = v___x_3431_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_a_3429_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
}
}
}
else
{
lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
lean_del_object(v___x_3373_);
lean_dec(v_fvarId_3371_);
lean_dec(v_mvarId_3370_);
lean_del_object(v___x_3368_);
lean_dec(v_snd_3366_);
lean_del_object(v___x_3363_);
v_a_3438_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3440_ = v___x_3376_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_dec(v___x_3376_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
if (v_isShared_3441_ == 0)
{
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3438_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3449_; lean_object* v___x_3451_; 
lean_dec(v_a_3357_);
v___x_3449_ = lean_box(0);
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 0, v___x_3449_);
v___x_3451_ = v___x_3359_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v___x_3449_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
}
else
{
return v___x_3356_;
}
}
else
{
lean_object* v_a_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3461_; 
lean_dec(v_hName_x3f_3344_);
lean_dec(v_mvarId_3343_);
v_a_3454_ = lean_ctor_get(v___x_3354_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3354_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3456_ = v___x_3354_;
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_a_3454_);
lean_dec(v___x_3354_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3459_; 
if (v_isShared_3457_ == 0)
{
v___x_3459_ = v___x_3456_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_a_3454_);
v___x_3459_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
return v___x_3459_;
}
}
}
v___jp_3351_:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3352_ = lean_box(0);
v___x_3353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3352_);
return v___x_3353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0___boxed(lean_object* v_mvarId_3462_, lean_object* v_hName_x3f_3463_, lean_object* v_useNewSemantics_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
uint8_t v_useNewSemantics_boxed_3470_; lean_object* v_res_3471_; 
v_useNewSemantics_boxed_3470_ = lean_unbox(v_useNewSemantics_3464_);
v_res_3471_ = l_Lean_Meta_splitIfTarget_x3f___lam__0(v_mvarId_3462_, v_hName_x3f_3463_, v_useNewSemantics_boxed_3470_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
return v_res_3471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f(lean_object* v_mvarId_3472_, lean_object* v_hName_x3f_3473_, uint8_t v_useNewSemantics_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_){
_start:
{
lean_object* v___x_3480_; lean_object* v___f_3481_; lean_object* v___x_3482_; 
v___x_3480_ = lean_box(v_useNewSemantics_3474_);
v___f_3481_ = lean_alloc_closure((void*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3481_, 0, v_mvarId_3472_);
lean_closure_set(v___f_3481_, 1, v_hName_x3f_3473_);
lean_closure_set(v___f_3481_, 2, v___x_3480_);
v___x_3482_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v___f_3481_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_);
return v___x_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___boxed(lean_object* v_mvarId_3483_, lean_object* v_hName_x3f_3484_, lean_object* v_useNewSemantics_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_){
_start:
{
uint8_t v_useNewSemantics_boxed_3491_; lean_object* v_res_3492_; 
v_useNewSemantics_boxed_3491_ = lean_unbox(v_useNewSemantics_3485_);
v_res_3492_ = l_Lean_Meta_splitIfTarget_x3f(v_mvarId_3483_, v_hName_x3f_3484_, v_useNewSemantics_boxed_3491_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_);
lean_dec(v_a_3489_);
lean_dec_ref(v_a_3488_);
lean_dec(v_a_3487_);
lean_dec_ref(v_a_3486_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___lam__0(lean_object* v___x_3493_, lean_object* v_mvarId_3494_, lean_object* v_hName_x3f_3495_, lean_object* v_fvarId_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_){
_start:
{
lean_object* v___x_3505_; 
lean_inc(v___y_3500_);
lean_inc_ref(v___y_3499_);
lean_inc(v___y_3498_);
lean_inc_ref(v___y_3497_);
v___x_3505_ = lean_infer_type(v___x_3493_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_object* v_a_3506_; lean_object* v___x_3507_; 
v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_a_3506_);
lean_dec_ref_known(v___x_3505_, 1);
v___x_3507_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(v_mvarId_3494_, v_a_3506_, v_hName_x3f_3495_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3602_; 
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3510_ = v___x_3507_;
v_isShared_3511_ = v_isSharedCheck_3602_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3507_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3602_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
if (lean_obj_tag(v_a_3508_) == 1)
{
lean_object* v_val_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3597_; 
lean_del_object(v___x_3510_);
v_val_3512_ = lean_ctor_get(v_a_3508_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v_a_3508_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3514_ = v_a_3508_;
v_isShared_3515_ = v_isSharedCheck_3597_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_val_3512_);
lean_dec(v_a_3508_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3597_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v_fst_3516_; lean_object* v_snd_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3596_; 
v_fst_3516_ = lean_ctor_get(v_val_3512_, 0);
v_snd_3517_ = lean_ctor_get(v_val_3512_, 1);
v_isSharedCheck_3596_ = !lean_is_exclusive(v_val_3512_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3519_ = v_val_3512_;
v_isShared_3520_ = v_isSharedCheck_3596_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_snd_3517_);
lean_inc(v_fst_3516_);
lean_dec(v_val_3512_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3596_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v_mvarId_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3594_; 
v_mvarId_3521_ = lean_ctor_get(v_fst_3516_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v_fst_3516_);
if (v_isSharedCheck_3594_ == 0)
{
lean_object* v_unused_3595_; 
v_unused_3595_ = lean_ctor_get(v_fst_3516_, 1);
lean_dec(v_unused_3595_);
v___x_3523_ = v_fst_3516_;
v_isShared_3524_ = v_isSharedCheck_3594_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_mvarId_3521_);
lean_dec(v_fst_3516_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3594_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
uint8_t v___x_3525_; lean_object* v___x_3526_; 
v___x_3525_ = 0;
lean_inc(v_fvarId_3496_);
lean_inc(v_mvarId_3521_);
v___x_3526_ = l_Lean_Meta_simpIfLocalDecl(v_mvarId_3521_, v_fvarId_3496_, v___x_3525_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v_a_3527_; lean_object* v_mvarId_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3584_; 
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
lean_inc(v_a_3527_);
lean_dec_ref_known(v___x_3526_, 1);
v_mvarId_3528_ = lean_ctor_get(v_snd_3517_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v_snd_3517_);
if (v_isSharedCheck_3584_ == 0)
{
lean_object* v_unused_3585_; 
v_unused_3585_ = lean_ctor_get(v_snd_3517_, 1);
lean_dec(v_unused_3585_);
v___x_3530_ = v_snd_3517_;
v_isShared_3531_ = v_isSharedCheck_3584_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_mvarId_3528_);
lean_dec(v_snd_3517_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3584_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3532_; 
lean_inc(v_mvarId_3528_);
v___x_3532_ = l_Lean_Meta_simpIfLocalDecl(v_mvarId_3528_, v_fvarId_3496_, v___x_3525_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3575_; 
v_a_3533_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3535_ = v___x_3532_;
v_isShared_3536_ = v_isSharedCheck_3575_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3532_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3575_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
uint8_t v___x_3547_; 
v___x_3547_ = l_Lean_instBEqMVarId_beq(v_mvarId_3521_, v_a_3527_);
lean_dec(v_mvarId_3521_);
if (v___x_3547_ == 0)
{
lean_del_object(v___x_3530_);
lean_dec(v_mvarId_3528_);
lean_del_object(v___x_3523_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
goto v___jp_3537_;
}
else
{
uint8_t v___x_3548_; 
v___x_3548_ = l_Lean_instBEqMVarId_beq(v_mvarId_3528_, v_a_3533_);
lean_dec(v_mvarId_3528_);
if (v___x_3548_ == 0)
{
lean_del_object(v___x_3530_);
lean_del_object(v___x_3523_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
goto v___jp_3537_;
}
else
{
lean_object* v_options_3549_; uint8_t v_hasTrace_3550_; 
lean_del_object(v___x_3535_);
lean_del_object(v___x_3519_);
lean_del_object(v___x_3514_);
v_options_3549_ = lean_ctor_get(v___y_3499_, 2);
v_hasTrace_3550_ = lean_ctor_get_uint8(v_options_3549_, sizeof(void*)*1);
if (v_hasTrace_3550_ == 0)
{
lean_dec(v_a_3533_);
lean_del_object(v___x_3530_);
lean_dec(v_a_3527_);
lean_del_object(v___x_3523_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
goto v___jp_3502_;
}
else
{
lean_object* v_inheritedTraceOptions_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; uint8_t v___x_3554_; 
v_inheritedTraceOptions_3551_ = lean_ctor_get(v___y_3499_, 13);
v___x_3552_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1));
v___x_3553_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2);
v___x_3554_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3551_, v_options_3549_, v___x_3553_);
if (v___x_3554_ == 0)
{
lean_dec(v_a_3533_);
lean_del_object(v___x_3530_);
lean_dec(v_a_3527_);
lean_del_object(v___x_3523_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
goto v___jp_3502_;
}
else
{
lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3558_; 
v___x_3555_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4);
v___x_3556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3556_, 0, v_a_3527_);
if (v_isShared_3531_ == 0)
{
lean_ctor_set_tag(v___x_3530_, 7);
lean_ctor_set(v___x_3530_, 1, v___x_3556_);
lean_ctor_set(v___x_3530_, 0, v___x_3555_);
v___x_3558_ = v___x_3530_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v___x_3555_);
lean_ctor_set(v_reuseFailAlloc_3574_, 1, v___x_3556_);
v___x_3558_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
lean_object* v___x_3559_; lean_object* v___x_3561_; 
v___x_3559_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6);
if (v_isShared_3524_ == 0)
{
lean_ctor_set_tag(v___x_3523_, 7);
lean_ctor_set(v___x_3523_, 1, v___x_3559_);
lean_ctor_set(v___x_3523_, 0, v___x_3558_);
v___x_3561_ = v___x_3523_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v___x_3558_);
lean_ctor_set(v_reuseFailAlloc_3573_, 1, v___x_3559_);
v___x_3561_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3562_, 0, v_a_3533_);
v___x_3563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3563_, 0, v___x_3561_);
lean_ctor_set(v___x_3563_, 1, v___x_3562_);
v___x_3564_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_3552_, v___x_3563_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_dec_ref_known(v___x_3564_, 1);
goto v___jp_3502_;
}
else
{
lean_object* v_a_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3572_; 
v_a_3565_ = lean_ctor_get(v___x_3564_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3567_ = v___x_3564_;
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_a_3565_);
lean_dec(v___x_3564_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3570_; 
if (v_isShared_3568_ == 0)
{
v___x_3570_ = v___x_3567_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_a_3565_);
v___x_3570_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
return v___x_3570_;
}
}
}
}
}
}
}
}
}
v___jp_3537_:
{
lean_object* v___x_3539_; 
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 1, v_a_3533_);
lean_ctor_set(v___x_3519_, 0, v_a_3527_);
v___x_3539_ = v___x_3519_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3527_);
lean_ctor_set(v_reuseFailAlloc_3546_, 1, v_a_3533_);
v___x_3539_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
lean_object* v___x_3541_; 
if (v_isShared_3515_ == 0)
{
lean_ctor_set(v___x_3514_, 0, v___x_3539_);
v___x_3541_ = v___x_3514_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3539_);
v___x_3541_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
lean_object* v___x_3543_; 
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 0, v___x_3541_);
v___x_3543_ = v___x_3535_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v___x_3541_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
}
}
}
else
{
lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3583_; 
lean_del_object(v___x_3530_);
lean_dec(v_mvarId_3528_);
lean_dec(v_a_3527_);
lean_del_object(v___x_3523_);
lean_dec(v_mvarId_3521_);
lean_del_object(v___x_3519_);
lean_del_object(v___x_3514_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
v_a_3576_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3578_ = v___x_3532_;
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___x_3532_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3581_; 
if (v_isShared_3579_ == 0)
{
v___x_3581_ = v___x_3578_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_a_3576_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
}
}
}
else
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3593_; 
lean_del_object(v___x_3523_);
lean_dec(v_mvarId_3521_);
lean_del_object(v___x_3519_);
lean_dec(v_snd_3517_);
lean_del_object(v___x_3514_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec(v_fvarId_3496_);
v_a_3586_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3588_ = v___x_3526_;
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___x_3526_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3591_; 
if (v_isShared_3589_ == 0)
{
v___x_3591_ = v___x_3588_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_a_3586_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3598_; lean_object* v___x_3600_; 
lean_dec(v_a_3508_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec(v_fvarId_3496_);
v___x_3598_ = lean_box(0);
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 0, v___x_3598_);
v___x_3600_ = v___x_3510_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v___x_3598_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
else
{
lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3610_; 
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec(v_fvarId_3496_);
v_a_3603_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3605_ = v___x_3507_;
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3507_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3608_; 
if (v_isShared_3606_ == 0)
{
v___x_3608_ = v___x_3605_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_a_3603_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
}
else
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec(v_fvarId_3496_);
lean_dec(v_hName_x3f_3495_);
lean_dec(v_mvarId_3494_);
v_a_3611_ = lean_ctor_get(v___x_3505_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3505_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3505_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
v___jp_3502_:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3503_ = lean_box(0);
v___x_3504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3503_);
return v___x_3504_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___lam__0___boxed(lean_object* v___x_3619_, lean_object* v_mvarId_3620_, lean_object* v_hName_x3f_3621_, lean_object* v_fvarId_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Lean_Meta_splitIfLocalDecl_x3f___lam__0(v___x_3619_, v_mvarId_3620_, v_hName_x3f_3621_, v_fvarId_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f(lean_object* v_mvarId_3629_, lean_object* v_fvarId_3630_, lean_object* v_hName_x3f_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_){
_start:
{
lean_object* v___x_3637_; lean_object* v___f_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; 
lean_inc(v_fvarId_3630_);
v___x_3637_ = l_Lean_mkFVar(v_fvarId_3630_);
lean_inc(v_mvarId_3629_);
v___f_3638_ = lean_alloc_closure((void*)(l_Lean_Meta_splitIfLocalDecl_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3638_, 0, v___x_3637_);
lean_closure_set(v___f_3638_, 1, v_mvarId_3629_);
lean_closure_set(v___f_3638_, 2, v_hName_x3f_3631_);
lean_closure_set(v___f_3638_, 3, v_fvarId_3630_);
v___x_3639_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3639_, 0, lean_box(0));
lean_closure_set(v___x_3639_, 1, v_mvarId_3629_);
lean_closure_set(v___x_3639_, 2, v___f_3638_);
v___x_3640_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v___x_3639_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_);
return v___x_3640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___boxed(lean_object* v_mvarId_3641_, lean_object* v_fvarId_3642_, lean_object* v_hName_x3f_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_){
_start:
{
lean_object* v_res_3649_; 
v_res_3649_ = l_Lean_Meta_splitIfLocalDecl_x3f(v_mvarId_3641_, v_fvarId_3642_, v_hName_x3f_3643_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_);
lean_dec(v_a_3647_);
lean_dec_ref(v_a_3646_);
lean_dec(v_a_3645_);
lean_dec_ref(v_a_3644_);
return v_res_3649_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; 
v___x_3670_ = lean_unsigned_to_nat(3526097586u);
v___x_3671_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_));
v___x_3672_ = l_Lean_Name_num___override(v___x_3671_, v___x_3670_);
return v___x_3672_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; 
v___x_3674_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_));
v___x_3675_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3676_ = l_Lean_Name_str___override(v___x_3675_, v___x_3674_);
return v___x_3676_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; 
v___x_3678_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_));
v___x_3679_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3680_ = l_Lean_Name_str___override(v___x_3679_, v___x_3678_);
return v___x_3680_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; 
v___x_3681_ = lean_unsigned_to_nat(2u);
v___x_3682_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3683_ = l_Lean_Name_num___override(v___x_3682_, v___x_3681_);
return v___x_3683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3685_; uint8_t v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; 
v___x_3685_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10));
v___x_3686_ = 0;
v___x_3687_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3688_ = l_Lean_registerTraceClass(v___x_3685_, v___x_3686_, v___x_3687_);
return v___x_3688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2____boxed(lean_object* v_a_3689_){
_start:
{
lean_object* v_res_3690_; 
v_res_3690_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_();
return v_res_3690_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_SplitIf(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_backward_split = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_backward_split);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_SplitIf(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_SplitIf(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_SplitIf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_SplitIf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_SplitIf(builtin);
}
#ifdef __cplusplus
}
#endif
