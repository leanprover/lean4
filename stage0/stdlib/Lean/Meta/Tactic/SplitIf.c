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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_num_indices(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Lean_mkPtrSet___redArg(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
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
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isMatcherAppCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
lean_object* l_Lean_Expr_getBoundedAppFn(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_fget(lean_object*, lean_object*);
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
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FindSplitImpl_visit_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FindSplitImpl_visit_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FindSplitImpl_visit_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FindSplitImpl_visit_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__2;
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
static const lean_string_object l_Lean_Meta_SplitIf_getSimpContext___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ite_eq_left"};
static const lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__6 = (const lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__6_value;
static const lean_ctor_object l_Lean_Meta_SplitIf_getSimpContext___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__6_value),LEAN_SCALAR_PTR_LITERAL(224, 237, 116, 5, 155, 59, 56, 160)}};
static const lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__7 = (const lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__7_value;
static const lean_string_object l_Lean_Meta_SplitIf_getSimpContext___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ite_eq_right"};
static const lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__8 = (const lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__8_value;
static const lean_ctor_object l_Lean_Meta_SplitIf_getSimpContext___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 39, 8, 237, 213, 91, 107, 69)}};
static const lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__9 = (const lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__9_value;
static const lean_string_object l_Lean_Meta_SplitIf_getSimpContext___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "dite_eq_left"};
static const lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__10 = (const lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__10_value;
static const lean_ctor_object l_Lean_Meta_SplitIf_getSimpContext___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__10_value),LEAN_SCALAR_PTR_LITERAL(239, 169, 41, 13, 119, 67, 249, 86)}};
static const lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__11 = (const lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__11_value;
static const lean_string_object l_Lean_Meta_SplitIf_getSimpContext___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "dite_eq_right"};
static const lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__12 = (const lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__12_value;
static const lean_ctor_object l_Lean_Meta_SplitIf_getSimpContext___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__12_value),LEAN_SCALAR_PTR_LITERAL(138, 158, 15, 234, 166, 144, 231, 97)}};
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "splitIf"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(181, 95, 169, 53, 171, 116, 20, 182)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "discharge\? "};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "<not-available>"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__15_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__16_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17;
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__7_value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(140, 203, 248, 13, 200, 236, 3, 225)}};
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
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Meta_SplitKind_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lean_Meta_SplitKind_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ite_elim___redArg(lean_object* v_ite_23_){
_start:
{
lean_inc(v_ite_23_);
return v_ite_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ite_elim___redArg___boxed(lean_object* v_ite_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Meta_SplitKind_ite_elim___redArg(v_ite_24_);
lean_dec(v_ite_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ite_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_ite_29_){
_start:
{
lean_inc(v_ite_29_);
return v_ite_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ite_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_ite_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lean_Meta_SplitKind_ite_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_ite_33_);
lean_dec(v_ite_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_match_elim___redArg(lean_object* v_match_36_){
_start:
{
lean_inc(v_match_36_);
return v_match_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_match_elim___redArg___boxed(lean_object* v_match_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Meta_SplitKind_match_elim___redArg(v_match_37_);
lean_dec(v_match_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_match_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_match_42_){
_start:
{
lean_inc(v_match_42_);
return v_match_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_match_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_match_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lean_Meta_SplitKind_match_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_match_46_);
lean_dec(v_match_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_both_elim___redArg(lean_object* v_both_49_){
_start:
{
lean_inc(v_both_49_);
return v_both_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_both_elim___redArg___boxed(lean_object* v_both_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Meta_SplitKind_both_elim___redArg(v_both_50_);
lean_dec(v_both_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_both_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_both_55_){
_start:
{
lean_inc(v_both_55_);
return v_both_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_both_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_both_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lean_Meta_SplitKind_both_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_both_59_);
lean_dec(v_both_59_);
return v_res_61_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SplitKind_considerIte(uint8_t v_x_62_){
_start:
{
switch(v_x_62_)
{
case 0:
{
uint8_t v___x_63_; 
v___x_63_ = 1;
return v___x_63_;
}
case 2:
{
uint8_t v___x_64_; 
v___x_64_ = 1;
return v___x_64_;
}
default: 
{
uint8_t v___x_65_; 
v___x_65_ = 0;
return v___x_65_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_considerIte___boxed(lean_object* v_x_66_){
_start:
{
uint8_t v_x_26__boxed_67_; uint8_t v_res_68_; lean_object* v_r_69_; 
v_x_26__boxed_67_ = lean_unbox(v_x_66_);
v_res_68_ = l_Lean_Meta_SplitKind_considerIte(v_x_26__boxed_67_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SplitKind_considerMatch(uint8_t v_x_70_){
_start:
{
switch(v_x_70_)
{
case 1:
{
uint8_t v___x_71_; 
v___x_71_ = 1;
return v___x_71_;
}
case 2:
{
uint8_t v___x_72_; 
v___x_72_ = 1;
return v___x_72_;
}
default: 
{
uint8_t v___x_73_; 
v___x_73_ = 0;
return v___x_73_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_considerMatch___boxed(lean_object* v_x_74_){
_start:
{
uint8_t v_x_26__boxed_75_; uint8_t v_res_76_; lean_object* v_r_77_; 
v_x_26__boxed_75_ = lean_unbox(v_x_74_);
v_res_76_ = l_Lean_Meta_SplitKind_considerMatch(v_x_26__boxed_75_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_m_78_, lean_object* v_query_79_, lean_object* v_x_80_, lean_object* v_x_81_, lean_object* v_x_82_){
_start:
{
lean_object* v_zero_83_; uint8_t v_isZero_84_; 
v_zero_83_ = lean_unsigned_to_nat(0u);
v_isZero_84_ = lean_nat_dec_eq(v_x_81_, v_zero_83_);
if (v_isZero_84_ == 1)
{
lean_dec(v_x_82_);
lean_dec(v_x_81_);
if (lean_obj_tag(v_x_80_) == 0)
{
lean_object* v___x_85_; 
v___x_85_ = lean_box(2);
return v___x_85_;
}
else
{
lean_object* v_val_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_93_; 
v_val_86_ = lean_ctor_get(v_x_80_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v_x_80_);
if (v_isSharedCheck_93_ == 0)
{
v___x_88_ = v_x_80_;
v_isShared_89_ = v_isSharedCheck_93_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_val_86_);
lean_dec(v_x_80_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_93_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_91_; 
if (v_isShared_89_ == 0)
{
v___x_91_ = v___x_88_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_val_86_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
}
else
{
lean_object* v_keyArray_94_; lean_object* v_valueArray_95_; lean_object* v___x_96_; uint8_t v_isSome_97_; 
v_keyArray_94_ = lean_ctor_get(v_m_78_, 1);
v_valueArray_95_ = lean_ctor_get(v_m_78_, 2);
v___x_96_ = lean_array_fget_borrowed(v_keyArray_94_, v_x_82_);
v_isSome_97_ = lean_noption_is_some(v___x_96_);
if (v_isSome_97_ == 0)
{
lean_dec(v_x_81_);
if (lean_obj_tag(v_x_80_) == 0)
{
lean_object* v___x_98_; 
v___x_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_98_, 0, v_x_82_);
return v___x_98_;
}
else
{
lean_object* v_val_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_106_; 
lean_dec(v_x_82_);
v_val_99_ = lean_ctor_get(v_x_80_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v_x_80_);
if (v_isSharedCheck_106_ == 0)
{
v___x_101_ = v_x_80_;
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_val_99_);
lean_dec(v_x_80_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_104_; 
if (v_isShared_102_ == 0)
{
v___x_104_ = v___x_101_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_val_99_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
}
else
{
lean_object* v_one_107_; lean_object* v_n_108_; lean_object* v___y_110_; 
v_one_107_ = lean_unsigned_to_nat(1u);
v_n_108_ = lean_nat_sub(v_x_81_, v_one_107_);
lean_dec(v_x_81_);
if (v_isSome_97_ == 0)
{
goto v___jp_116_;
}
else
{
lean_object* v___x_118_; uint8_t v_isSome_119_; 
v___x_118_ = lean_array_fget_borrowed(v_valueArray_95_, v_x_82_);
v_isSome_119_ = lean_noption_is_some(v___x_118_);
if (v_isSome_119_ == 0)
{
goto v___jp_116_;
}
else
{
lean_object* v_val_120_; uint8_t v___x_121_; 
lean_inc(v___x_96_);
v_val_120_ = lean_noption_get(v___x_96_);
v___x_121_ = lean_expr_eqv(v_val_120_, v_query_79_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
lean_dec(v_val_120_);
v___x_122_ = lean_array_get_size(v_keyArray_94_);
v___x_123_ = lean_nat_add(v_x_82_, v_one_107_);
lean_dec(v_x_82_);
v___x_124_ = lean_nat_dec_lt(v___x_123_, v___x_122_);
if (v___x_124_ == 0)
{
lean_dec(v___x_123_);
v_x_81_ = v_n_108_;
v_x_82_ = v_zero_83_;
goto _start;
}
else
{
v_x_81_ = v_n_108_;
v_x_82_ = v___x_123_;
goto _start;
}
}
else
{
lean_object* v_val_127_; lean_object* v___x_128_; 
lean_dec(v_n_108_);
lean_dec(v_x_80_);
lean_inc(v___x_118_);
v_val_127_ = lean_noption_get(v___x_118_);
v___x_128_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_128_, 0, v_x_82_);
lean_ctor_set(v___x_128_, 1, v_val_120_);
lean_ctor_set(v___x_128_, 2, v_val_127_);
return v___x_128_;
}
}
}
v___jp_109_:
{
lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_111_ = lean_array_get_size(v_keyArray_94_);
v___x_112_ = lean_nat_add(v_x_82_, v_one_107_);
lean_dec(v_x_82_);
v___x_113_ = lean_nat_dec_lt(v___x_112_, v___x_111_);
if (v___x_113_ == 0)
{
lean_dec(v___x_112_);
v_x_80_ = v___y_110_;
v_x_81_ = v_n_108_;
v_x_82_ = v_zero_83_;
goto _start;
}
else
{
v_x_80_ = v___y_110_;
v_x_81_ = v_n_108_;
v_x_82_ = v___x_112_;
goto _start;
}
}
v___jp_116_:
{
if (lean_obj_tag(v_x_80_) == 0)
{
lean_object* v___x_117_; 
lean_inc(v_x_82_);
v___x_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_117_, 0, v_x_82_);
v___y_110_ = v___x_117_;
goto v___jp_109_;
}
else
{
v___y_110_ = v_x_80_;
goto v___jp_109_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_m_129_, lean_object* v_query_130_, lean_object* v_x_131_, lean_object* v_x_132_, lean_object* v_x_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_m_129_, v_query_130_, v_x_131_, v_x_132_, v_x_133_);
lean_dec_ref(v_query_130_);
lean_dec_ref(v_m_129_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_m_135_, lean_object* v_query_136_){
_start:
{
lean_object* v_keyArray_137_; lean_object* v___x_138_; uint64_t v___x_139_; uint64_t v___x_140_; uint64_t v___x_141_; uint64_t v_fold_142_; uint64_t v___x_143_; uint64_t v___x_144_; uint64_t v___x_145_; size_t v___x_146_; size_t v___x_147_; size_t v___x_148_; size_t v___x_149_; size_t v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v_keyArray_137_ = lean_ctor_get(v_m_135_, 1);
v___x_138_ = lean_array_get_size(v_keyArray_137_);
v___x_139_ = l_Lean_Expr_hash(v_query_136_);
v___x_140_ = 32ULL;
v___x_141_ = lean_uint64_shift_right(v___x_139_, v___x_140_);
v_fold_142_ = lean_uint64_xor(v___x_139_, v___x_141_);
v___x_143_ = 16ULL;
v___x_144_ = lean_uint64_shift_right(v_fold_142_, v___x_143_);
v___x_145_ = lean_uint64_xor(v_fold_142_, v___x_144_);
v___x_146_ = lean_uint64_to_usize(v___x_145_);
v___x_147_ = lean_usize_of_nat(v___x_138_);
v___x_148_ = ((size_t)1ULL);
v___x_149_ = lean_usize_sub(v___x_147_, v___x_148_);
v___x_150_ = lean_usize_land(v___x_146_, v___x_149_);
v___x_151_ = lean_usize_to_nat(v___x_150_);
v___x_152_ = lean_box(0);
v___x_153_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_m_135_, v_query_136_, v___x_152_, v___x_138_, v___x_151_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_154_, lean_object* v_query_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0_spec__1___redArg(v_m_154_, v_query_155_);
lean_dec_ref(v_query_155_);
lean_dec_ref(v_m_154_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg(lean_object* v_m_157_, lean_object* v_query_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0_spec__1___redArg(v_m_157_, v_query_158_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v_index_160_; lean_object* v_key_161_; lean_object* v_value_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_169_; 
v_index_160_ = lean_ctor_get(v___x_159_, 0);
v_key_161_ = lean_ctor_get(v___x_159_, 1);
v_value_162_ = lean_ctor_get(v___x_159_, 2);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_169_ == 0)
{
v___x_164_ = v___x_159_;
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_value_162_);
lean_inc(v_key_161_);
lean_inc(v_index_160_);
lean_dec(v___x_159_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
if (v_isShared_165_ == 0)
{
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_index_160_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_key_161_);
lean_ctor_set(v_reuseFailAlloc_168_, 2, v_value_162_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
else
{
lean_object* v___x_170_; 
lean_dec(v___x_159_);
v___x_170_ = lean_box(1);
return v___x_170_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_m_171_, lean_object* v_query_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg(v_m_171_, v_query_172_);
lean_dec_ref(v_query_172_);
lean_dec_ref(v_m_171_);
return v_res_173_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(lean_object* v_m_174_, lean_object* v_a_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg(v_m_174_, v_a_175_);
if (lean_obj_tag(v___x_176_) == 0)
{
uint8_t v___x_177_; 
lean_dec_ref_known(v___x_176_, 3);
v___x_177_ = 1;
return v___x_177_;
}
else
{
uint8_t v___x_178_; 
v___x_178_ = 0;
return v___x_178_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg___boxed(lean_object* v_m_179_, lean_object* v_a_180_){
_start:
{
uint8_t v_res_181_; lean_object* v_r_182_; 
v_res_181_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(v_m_179_, v_a_180_);
lean_dec_ref(v_a_180_);
lean_dec_ref(v_m_179_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg(lean_object* v_upperBound_191_, lean_object* v_args_192_, lean_object* v_a_193_, lean_object* v_b_194_){
_start:
{
uint8_t v___x_195_; 
v___x_195_ = lean_nat_dec_lt(v_a_193_, v_upperBound_191_);
if (v___x_195_ == 0)
{
lean_dec(v_a_193_);
lean_inc_ref(v_b_194_);
return v_b_194_;
}
else
{
lean_object* v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_196_ = l_Lean_instInhabitedExpr;
v___x_197_ = lean_array_get_borrowed(v___x_196_, v_args_192_, v_a_193_);
v___x_198_ = l_Lean_Expr_hasLooseBVars(v___x_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0));
v___x_200_ = lean_unsigned_to_nat(1u);
v___x_201_ = lean_nat_add(v_a_193_, v___x_200_);
lean_dec(v_a_193_);
v_a_193_ = v___x_201_;
v_b_194_ = v___x_199_;
goto _start;
}
else
{
lean_object* v___x_203_; 
lean_dec(v_a_193_);
v___x_203_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__2));
return v___x_203_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___boxed(lean_object* v_upperBound_204_, lean_object* v_args_205_, lean_object* v_a_206_, lean_object* v_b_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg(v_upperBound_204_, v_args_205_, v_a_206_, v_b_207_);
lean_dec_ref(v_b_207_);
lean_dec_ref(v_args_205_);
lean_dec(v_upperBound_204_);
return v_res_208_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0(void){
_start:
{
lean_object* v___x_209_; lean_object* v_dummy_210_; 
v___x_209_ = lean_box(0);
v_dummy_210_ = l_Lean_Expr_sort___override(v___x_209_);
return v_dummy_210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f(lean_object* v_env_217_, lean_object* v_ctx_218_, lean_object* v_e_219_){
_start:
{
lean_object* v_exceptionSet_220_; uint8_t v_kind_221_; lean_object* v_e_223_; lean_object* v___y_251_; lean_object* v___y_252_; uint8_t v___y_253_; uint8_t v___x_263_; 
v_exceptionSet_220_ = lean_ctor_get(v_ctx_218_, 0);
v_kind_221_ = lean_ctor_get_uint8(v_ctx_218_, sizeof(void*)*1);
v___x_263_ = l_Lean_Meta_SplitKind_considerIte(v_kind_221_);
if (v___x_263_ == 0)
{
goto v___jp_227_;
}
else
{
lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_264_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__2));
v___x_265_ = l_Lean_Expr_isAppOf(v_e_219_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__4));
v___x_267_ = l_Lean_Expr_isAppOf(v_e_219_, v___x_266_);
if (v___x_267_ == 0)
{
goto v___jp_227_;
}
else
{
goto v___jp_256_;
}
}
else
{
goto v___jp_256_;
}
}
v___jp_222_:
{
uint8_t v___x_224_; 
v___x_224_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(v_exceptionSet_220_, v_e_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; 
v___x_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_225_, 0, v_e_223_);
return v___x_225_;
}
else
{
lean_object* v___x_226_; 
lean_dec_ref(v_e_223_);
v___x_226_ = lean_box(0);
return v___x_226_;
}
}
v___jp_227_:
{
uint8_t v___x_228_; 
v___x_228_ = l_Lean_Meta_SplitKind_considerMatch(v_kind_221_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; 
lean_dec_ref(v_e_219_);
lean_dec_ref(v_env_217_);
v___x_229_ = lean_box(0);
return v___x_229_;
}
else
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_217_, v_e_219_);
if (lean_obj_tag(v___x_230_) == 1)
{
lean_object* v_val_231_; lean_object* v_numDiscrs_232_; lean_object* v_nargs_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v_dummy_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v_args_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v_fst_243_; 
v_val_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_val_231_);
lean_dec_ref_known(v___x_230_, 1);
v_numDiscrs_232_ = lean_ctor_get(v_val_231_, 1);
v_nargs_233_ = l_Lean_Expr_getAppNumArgs(v_e_219_);
v___x_234_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_231_);
v___x_235_ = lean_nat_add(v___x_234_, v_numDiscrs_232_);
v_dummy_236_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0);
lean_inc(v_nargs_233_);
v___x_237_ = lean_mk_array(v_nargs_233_, v_dummy_236_);
v___x_238_ = lean_unsigned_to_nat(1u);
v___x_239_ = lean_nat_sub(v_nargs_233_, v___x_238_);
lean_dec(v_nargs_233_);
lean_inc_ref(v_e_219_);
v_args_240_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_219_, v___x_237_, v___x_239_);
v___x_241_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0));
v___x_242_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg(v___x_235_, v_args_240_, v___x_234_, v___x_241_);
lean_dec(v___x_235_);
v_fst_243_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_fst_243_);
lean_dec_ref(v___x_242_);
if (lean_obj_tag(v_fst_243_) == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_244_ = lean_array_get_size(v_args_240_);
lean_dec_ref(v_args_240_);
v___x_245_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_231_);
lean_dec(v_val_231_);
v___x_246_ = lean_nat_sub(v___x_244_, v___x_245_);
lean_dec(v___x_245_);
v___x_247_ = l_Lean_Expr_getBoundedAppFn(v___x_246_, v_e_219_);
lean_dec_ref(v_e_219_);
v_e_223_ = v___x_247_;
goto v___jp_222_;
}
else
{
lean_object* v_val_248_; 
lean_dec_ref(v_args_240_);
lean_dec(v_val_231_);
lean_dec_ref(v_e_219_);
v_val_248_ = lean_ctor_get(v_fst_243_, 0);
lean_inc(v_val_248_);
lean_dec_ref_known(v_fst_243_, 1);
return v_val_248_;
}
}
else
{
lean_object* v___x_249_; 
lean_dec(v___x_230_);
lean_dec_ref(v_e_219_);
v___x_249_ = lean_box(0);
return v___x_249_;
}
}
}
v___jp_250_:
{
if (v___y_253_ == 0)
{
lean_dec(v___y_252_);
goto v___jp_227_;
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec_ref(v_env_217_);
v___x_254_ = lean_nat_sub(v___y_252_, v___y_251_);
lean_dec(v___y_252_);
v___x_255_ = l_Lean_Expr_getBoundedAppFn(v___x_254_, v_e_219_);
lean_dec_ref(v_e_219_);
v_e_223_ = v___x_255_;
goto v___jp_222_;
}
}
v___jp_256_:
{
lean_object* v_numArgs_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v_numArgs_257_ = l_Lean_Expr_getAppNumArgs(v_e_219_);
v___x_258_ = lean_unsigned_to_nat(5u);
v___x_259_ = lean_nat_dec_le(v___x_258_, v_numArgs_257_);
if (v___x_259_ == 0)
{
v___y_251_ = v___x_258_;
v___y_252_ = v_numArgs_257_;
v___y_253_ = v___x_259_;
goto v___jp_250_;
}
else
{
lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_260_ = lean_unsigned_to_nat(3u);
v___x_261_ = l_Lean_Expr_getRevArg_x21(v_e_219_, v___x_260_);
v___x_262_ = l_Lean_Expr_hasLooseBVars(v___x_261_);
lean_dec_ref(v___x_261_);
if (v___x_262_ == 0)
{
v___y_251_ = v___x_258_;
v___y_252_ = v_numArgs_257_;
v___y_253_ = v___x_259_;
goto v___jp_250_;
}
else
{
lean_dec(v_numArgs_257_);
goto v___jp_227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___boxed(lean_object* v_env_268_, lean_object* v_ctx_269_, lean_object* v_e_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f(v_env_268_, v_ctx_269_, v_e_270_);
lean_dec_ref(v_ctx_269_);
return v_res_271_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0(lean_object* v_00_u03b2_272_, lean_object* v_m_273_, lean_object* v_a_274_){
_start:
{
uint8_t v___x_275_; 
v___x_275_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(v_m_273_, v_a_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___boxed(lean_object* v_00_u03b2_276_, lean_object* v_m_277_, lean_object* v_a_278_){
_start:
{
uint8_t v_res_279_; lean_object* v_r_280_; 
v_res_279_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0(v_00_u03b2_276_, v_m_277_, v_a_278_);
lean_dec_ref(v_a_278_);
lean_dec_ref(v_m_277_);
v_r_280_ = lean_box(v_res_279_);
return v_r_280_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1(lean_object* v_upperBound_281_, lean_object* v_args_282_, lean_object* v_inst_283_, lean_object* v_R_284_, lean_object* v_a_285_, lean_object* v_b_286_, lean_object* v_c_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg(v_upperBound_281_, v_args_282_, v_a_285_, v_b_286_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___boxed(lean_object* v_upperBound_289_, lean_object* v_args_290_, lean_object* v_inst_291_, lean_object* v_R_292_, lean_object* v_a_293_, lean_object* v_b_294_, lean_object* v_c_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1(v_upperBound_289_, v_args_290_, v_inst_291_, v_R_292_, v_a_293_, v_b_294_, v_c_295_);
lean_dec_ref(v_b_294_);
lean_dec_ref(v_args_290_);
lean_dec(v_upperBound_289_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0(lean_object* v_00_u03b2_297_, lean_object* v_m_298_, lean_object* v_query_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg(v_m_298_, v_query_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_301_, lean_object* v_m_302_, lean_object* v_query_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0(v_00_u03b2_301_, v_m_302_, v_query_303_);
lean_dec_ref(v_query_303_);
lean_dec_ref(v_m_302_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_305_, lean_object* v_m_306_, lean_object* v_query_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0_spec__1___redArg(v_m_306_, v_query_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_309_, lean_object* v_m_310_, lean_object* v_query_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0_spec__1(v_00_u03b2_309_, v_m_310_, v_query_311_);
lean_dec_ref(v_query_311_);
lean_dec_ref(v_m_310_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_313_, lean_object* v_m_314_, lean_object* v_query_315_, lean_object* v_x_316_, lean_object* v_x_317_, lean_object* v_x_318_, lean_object* v_x_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_m_314_, v_query_315_, v_x_316_, v_x_317_, v_x_318_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_321_, lean_object* v_m_322_, lean_object* v_query_323_, lean_object* v_x_324_, lean_object* v_x_325_, lean_object* v_x_326_, lean_object* v_x_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_321_, v_m_322_, v_query_323_, v_x_324_, v_x_325_, v_x_326_, v_x_327_);
lean_dec_ref(v_query_323_);
lean_dec_ref(v_m_322_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___redArg(lean_object* v_e_333_, lean_object* v_a_334_){
_start:
{
lean_object* v___f_336_; lean_object* v___f_337_; uint8_t v___x_338_; 
v___f_336_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__0));
v___f_337_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__1));
lean_inc_ref(v_e_333_);
v___x_338_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_336_, v___f_337_, v_a_334_, v_e_333_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; lean_object* v___y_341_; lean_object* v___y_346_; lean_object* v_i_347_; lean_object* v___y_353_; lean_object* v___y_363_; lean_object* v_i_364_; lean_object* v___x_379_; 
v___x_339_ = lean_box(0);
lean_inc_ref(v_e_333_);
v___x_379_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_336_, v___f_337_, v_a_334_, v_e_333_);
switch(lean_obj_tag(v___x_379_))
{
case 0:
{
lean_dec_ref_known(v___x_379_, 3);
lean_dec_ref(v_e_333_);
v___y_341_ = v_a_334_;
goto v___jp_340_;
}
case 1:
{
lean_object* v_index_380_; lean_object* v_size_381_; lean_object* v_keyArray_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
v_index_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_index_380_);
lean_dec_ref_known(v___x_379_, 1);
v_size_381_ = lean_ctor_get(v_a_334_, 0);
v_keyArray_382_ = lean_ctor_get(v_a_334_, 1);
v___x_383_ = lean_unsigned_to_nat(1u);
v___x_384_ = lean_nat_add(v_size_381_, v___x_383_);
v___x_385_ = lean_array_get_size(v_keyArray_382_);
v___x_386_ = lean_nat_dec_lt(v___x_384_, v___x_385_);
if (v___x_386_ == 0)
{
lean_dec(v___x_384_);
lean_dec(v_index_380_);
goto v___jp_369_;
}
else
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_387_ = lean_unsigned_to_nat(4u);
v___x_388_ = lean_nat_mul(v___x_384_, v___x_387_);
v___x_389_ = lean_unsigned_to_nat(3u);
v___x_390_ = lean_nat_mul(v___x_385_, v___x_389_);
v___x_391_ = lean_nat_dec_le(v___x_388_, v___x_390_);
lean_dec(v___x_390_);
lean_dec(v___x_388_);
if (v___x_391_ == 0)
{
lean_dec(v___x_384_);
lean_dec(v_index_380_);
goto v___jp_369_;
}
else
{
lean_object* v___x_392_; 
v___x_392_ = l_Std_DHashMap_Raw_setEntry___redArg(v_a_334_, v___x_384_, v_index_380_, v_e_333_, v___x_339_);
lean_dec(v_index_380_);
v___y_341_ = v___x_392_;
goto v___jp_340_;
}
}
}
default: 
{
lean_object* v_size_393_; lean_object* v_keyArray_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
v_size_393_ = lean_ctor_get(v_a_334_, 0);
v_keyArray_394_ = lean_ctor_get(v_a_334_, 1);
v___x_395_ = lean_unsigned_to_nat(1u);
v___x_396_ = lean_nat_add(v_size_393_, v___x_395_);
v___x_397_ = lean_array_get_size(v_keyArray_394_);
v___x_398_ = lean_nat_dec_lt(v___x_396_, v___x_397_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; 
lean_dec(v___x_396_);
v___x_399_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_336_, v___f_337_, v_a_334_);
v___y_353_ = v___x_399_;
goto v___jp_352_;
}
else
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_400_ = lean_unsigned_to_nat(4u);
v___x_401_ = lean_nat_mul(v___x_396_, v___x_400_);
lean_dec(v___x_396_);
v___x_402_ = lean_unsigned_to_nat(3u);
v___x_403_ = lean_nat_mul(v___x_397_, v___x_402_);
v___x_404_ = lean_nat_dec_le(v___x_401_, v___x_403_);
lean_dec(v___x_403_);
lean_dec(v___x_401_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; 
v___x_405_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_336_, v___f_337_, v_a_334_);
v___y_353_ = v___x_405_;
goto v___jp_352_;
}
else
{
v___y_353_ = v_a_334_;
goto v___jp_352_;
}
}
}
}
v___jp_340_:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_342_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__2));
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___y_341_);
v___x_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
return v___x_344_;
}
v___jp_345_:
{
lean_object* v_size_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v_size_348_ = lean_ctor_get(v___y_346_, 0);
v___x_349_ = lean_unsigned_to_nat(1u);
v___x_350_ = lean_nat_add(v_size_348_, v___x_349_);
v___x_351_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_346_, v___x_350_, v_i_347_, v_e_333_, v___x_339_);
lean_dec(v_i_347_);
v___y_341_ = v___x_351_;
goto v___jp_340_;
}
v___jp_352_:
{
lean_object* v___x_354_; 
lean_inc_ref(v_e_333_);
v___x_354_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_336_, v___f_337_, v___y_353_, v_e_333_);
switch(lean_obj_tag(v___x_354_))
{
case 0:
{
lean_object* v_index_355_; lean_object* v_size_356_; lean_object* v___x_357_; 
v_index_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_index_355_);
lean_dec_ref_known(v___x_354_, 3);
v_size_356_ = lean_ctor_get(v___y_353_, 0);
lean_inc(v_size_356_);
v___x_357_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_353_, v_size_356_, v_index_355_, v_e_333_, v___x_339_);
lean_dec(v_index_355_);
v___y_341_ = v___x_357_;
goto v___jp_340_;
}
case 1:
{
lean_object* v_index_358_; 
v_index_358_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_index_358_);
lean_dec_ref_known(v___x_354_, 1);
v___y_346_ = v___y_353_;
v_i_347_ = v_index_358_;
goto v___jp_345_;
}
default: 
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_unsigned_to_nat(0u);
v___x_360_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_353_, v___x_359_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_index_361_; 
v_index_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc(v_index_361_);
lean_dec_ref_known(v___x_360_, 1);
v___y_346_ = v___y_353_;
v_i_347_ = v_index_361_;
goto v___jp_345_;
}
else
{
lean_dec_ref(v_e_333_);
v___y_341_ = v___y_353_;
goto v___jp_340_;
}
}
}
}
v___jp_362_:
{
lean_object* v_size_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_size_365_ = lean_ctor_get(v___y_363_, 0);
v___x_366_ = lean_unsigned_to_nat(1u);
v___x_367_ = lean_nat_add(v_size_365_, v___x_366_);
v___x_368_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_363_, v___x_367_, v_i_364_, v_e_333_, v___x_339_);
lean_dec(v_i_364_);
v___y_341_ = v___x_368_;
goto v___jp_340_;
}
v___jp_369_:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_336_, v___f_337_, v_a_334_);
lean_inc_ref(v_e_333_);
v___x_371_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_336_, v___f_337_, v___x_370_, v_e_333_);
switch(lean_obj_tag(v___x_371_))
{
case 0:
{
lean_object* v_index_372_; lean_object* v_size_373_; lean_object* v___x_374_; 
v_index_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_index_372_);
lean_dec_ref_known(v___x_371_, 3);
v_size_373_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_size_373_);
v___x_374_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_370_, v_size_373_, v_index_372_, v_e_333_, v___x_339_);
lean_dec(v_index_372_);
v___y_341_ = v___x_374_;
goto v___jp_340_;
}
case 1:
{
lean_object* v_index_375_; 
v_index_375_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_index_375_);
lean_dec_ref_known(v___x_371_, 1);
v___y_363_ = v___x_370_;
v_i_364_ = v_index_375_;
goto v___jp_362_;
}
default: 
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = lean_unsigned_to_nat(0u);
v___x_377_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_370_, v___x_376_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v_index_378_; 
v_index_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc(v_index_378_);
lean_dec_ref_known(v___x_377_, 1);
v___y_363_ = v___x_370_;
v_i_364_ = v_index_378_;
goto v___jp_362_;
}
else
{
lean_dec_ref(v_e_333_);
v___y_341_ = v___x_370_;
goto v___jp_340_;
}
}
}
}
}
else
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
lean_dec_ref(v_e_333_);
v___x_406_ = lean_box(0);
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v_a_334_);
v___x_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___redArg___boxed(lean_object* v_e_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Meta_FindSplitImpl_checkVisited___redArg(v_e_409_, v_a_410_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited(lean_object* v_e_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v___f_421_; lean_object* v___f_422_; uint8_t v___x_423_; 
v___f_421_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__0));
v___f_422_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__1));
lean_inc_ref(v_e_413_);
v___x_423_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_421_, v___f_422_, v_a_415_, v_e_413_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; lean_object* v___y_426_; lean_object* v___y_431_; lean_object* v_i_432_; lean_object* v___y_438_; lean_object* v___y_448_; lean_object* v_i_449_; lean_object* v___x_464_; 
v___x_424_ = lean_box(0);
lean_inc_ref(v_e_413_);
v___x_464_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_421_, v___f_422_, v_a_415_, v_e_413_);
switch(lean_obj_tag(v___x_464_))
{
case 0:
{
lean_dec_ref_known(v___x_464_, 3);
lean_dec_ref(v_e_413_);
v___y_426_ = v_a_415_;
goto v___jp_425_;
}
case 1:
{
lean_object* v_index_465_; lean_object* v_size_466_; lean_object* v_keyArray_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v_index_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_index_465_);
lean_dec_ref_known(v___x_464_, 1);
v_size_466_ = lean_ctor_get(v_a_415_, 0);
v_keyArray_467_ = lean_ctor_get(v_a_415_, 1);
v___x_468_ = lean_unsigned_to_nat(1u);
v___x_469_ = lean_nat_add(v_size_466_, v___x_468_);
v___x_470_ = lean_array_get_size(v_keyArray_467_);
v___x_471_ = lean_nat_dec_lt(v___x_469_, v___x_470_);
if (v___x_471_ == 0)
{
lean_dec(v___x_469_);
lean_dec(v_index_465_);
goto v___jp_454_;
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_472_ = lean_unsigned_to_nat(4u);
v___x_473_ = lean_nat_mul(v___x_469_, v___x_472_);
v___x_474_ = lean_unsigned_to_nat(3u);
v___x_475_ = lean_nat_mul(v___x_470_, v___x_474_);
v___x_476_ = lean_nat_dec_le(v___x_473_, v___x_475_);
lean_dec(v___x_475_);
lean_dec(v___x_473_);
if (v___x_476_ == 0)
{
lean_dec(v___x_469_);
lean_dec(v_index_465_);
goto v___jp_454_;
}
else
{
lean_object* v___x_477_; 
v___x_477_ = l_Std_DHashMap_Raw_setEntry___redArg(v_a_415_, v___x_469_, v_index_465_, v_e_413_, v___x_424_);
lean_dec(v_index_465_);
v___y_426_ = v___x_477_;
goto v___jp_425_;
}
}
}
default: 
{
lean_object* v_size_478_; lean_object* v_keyArray_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v_size_478_ = lean_ctor_get(v_a_415_, 0);
v_keyArray_479_ = lean_ctor_get(v_a_415_, 1);
v___x_480_ = lean_unsigned_to_nat(1u);
v___x_481_ = lean_nat_add(v_size_478_, v___x_480_);
v___x_482_ = lean_array_get_size(v_keyArray_479_);
v___x_483_ = lean_nat_dec_lt(v___x_481_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; 
lean_dec(v___x_481_);
v___x_484_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_421_, v___f_422_, v_a_415_);
v___y_438_ = v___x_484_;
goto v___jp_437_;
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_485_ = lean_unsigned_to_nat(4u);
v___x_486_ = lean_nat_mul(v___x_481_, v___x_485_);
lean_dec(v___x_481_);
v___x_487_ = lean_unsigned_to_nat(3u);
v___x_488_ = lean_nat_mul(v___x_482_, v___x_487_);
v___x_489_ = lean_nat_dec_le(v___x_486_, v___x_488_);
lean_dec(v___x_488_);
lean_dec(v___x_486_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; 
v___x_490_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_421_, v___f_422_, v_a_415_);
v___y_438_ = v___x_490_;
goto v___jp_437_;
}
else
{
v___y_438_ = v_a_415_;
goto v___jp_437_;
}
}
}
}
v___jp_425_:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_427_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__2));
v___x_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v___y_426_);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
return v___x_429_;
}
v___jp_430_:
{
lean_object* v_size_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v_size_433_ = lean_ctor_get(v___y_431_, 0);
v___x_434_ = lean_unsigned_to_nat(1u);
v___x_435_ = lean_nat_add(v_size_433_, v___x_434_);
v___x_436_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_431_, v___x_435_, v_i_432_, v_e_413_, v___x_424_);
lean_dec(v_i_432_);
v___y_426_ = v___x_436_;
goto v___jp_425_;
}
v___jp_437_:
{
lean_object* v___x_439_; 
lean_inc_ref(v_e_413_);
v___x_439_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_421_, v___f_422_, v___y_438_, v_e_413_);
switch(lean_obj_tag(v___x_439_))
{
case 0:
{
lean_object* v_index_440_; lean_object* v_size_441_; lean_object* v___x_442_; 
v_index_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_index_440_);
lean_dec_ref_known(v___x_439_, 3);
v_size_441_ = lean_ctor_get(v___y_438_, 0);
lean_inc(v_size_441_);
v___x_442_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_438_, v_size_441_, v_index_440_, v_e_413_, v___x_424_);
lean_dec(v_index_440_);
v___y_426_ = v___x_442_;
goto v___jp_425_;
}
case 1:
{
lean_object* v_index_443_; 
v_index_443_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_index_443_);
lean_dec_ref_known(v___x_439_, 1);
v___y_431_ = v___y_438_;
v_i_432_ = v_index_443_;
goto v___jp_430_;
}
default: 
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_438_, v___x_444_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_index_446_; 
v_index_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_index_446_);
lean_dec_ref_known(v___x_445_, 1);
v___y_431_ = v___y_438_;
v_i_432_ = v_index_446_;
goto v___jp_430_;
}
else
{
lean_dec_ref(v_e_413_);
v___y_426_ = v___y_438_;
goto v___jp_425_;
}
}
}
}
v___jp_447_:
{
lean_object* v_size_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v_size_450_ = lean_ctor_get(v___y_448_, 0);
v___x_451_ = lean_unsigned_to_nat(1u);
v___x_452_ = lean_nat_add(v_size_450_, v___x_451_);
v___x_453_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_448_, v___x_452_, v_i_449_, v_e_413_, v___x_424_);
lean_dec(v_i_449_);
v___y_426_ = v___x_453_;
goto v___jp_425_;
}
v___jp_454_:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_421_, v___f_422_, v_a_415_);
lean_inc_ref(v_e_413_);
v___x_456_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_421_, v___f_422_, v___x_455_, v_e_413_);
switch(lean_obj_tag(v___x_456_))
{
case 0:
{
lean_object* v_index_457_; lean_object* v_size_458_; lean_object* v___x_459_; 
v_index_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_index_457_);
lean_dec_ref_known(v___x_456_, 3);
v_size_458_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_size_458_);
v___x_459_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_455_, v_size_458_, v_index_457_, v_e_413_, v___x_424_);
lean_dec(v_index_457_);
v___y_426_ = v___x_459_;
goto v___jp_425_;
}
case 1:
{
lean_object* v_index_460_; 
v_index_460_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_index_460_);
lean_dec_ref_known(v___x_456_, 1);
v___y_448_ = v___x_455_;
v_i_449_ = v_index_460_;
goto v___jp_447_;
}
default: 
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_455_, v___x_461_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_index_463_; 
v_index_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_index_463_);
lean_dec_ref_known(v___x_462_, 1);
v___y_448_ = v___x_455_;
v_i_449_ = v_index_463_;
goto v___jp_447_;
}
else
{
lean_dec_ref(v_e_413_);
v___y_426_ = v___x_455_;
goto v___jp_425_;
}
}
}
}
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
lean_dec_ref(v_e_413_);
v___x_491_ = lean_box(0);
v___x_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
lean_ctor_set(v___x_492_, 1, v_a_415_);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___boxed(lean_object* v_e_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_Meta_FindSplitImpl_checkVisited(v_e_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
lean_dec_ref(v_a_495_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5___redArg(lean_object* v_m_503_, lean_object* v_query_504_, lean_object* v_x_505_, lean_object* v_x_506_, lean_object* v_x_507_){
_start:
{
lean_object* v_zero_508_; uint8_t v_isZero_509_; 
v_zero_508_ = lean_unsigned_to_nat(0u);
v_isZero_509_ = lean_nat_dec_eq(v_x_506_, v_zero_508_);
if (v_isZero_509_ == 1)
{
lean_dec(v_x_507_);
lean_dec(v_x_506_);
if (lean_obj_tag(v_x_505_) == 0)
{
lean_object* v___x_510_; 
v___x_510_ = lean_box(2);
return v___x_510_;
}
else
{
lean_object* v_val_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
v_val_511_ = lean_ctor_get(v_x_505_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v_x_505_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v_x_505_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_val_511_);
lean_dec(v_x_505_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_val_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
else
{
lean_object* v_keyArray_519_; lean_object* v_valueArray_520_; lean_object* v___x_521_; uint8_t v_isSome_522_; 
v_keyArray_519_ = lean_ctor_get(v_m_503_, 1);
v_valueArray_520_ = lean_ctor_get(v_m_503_, 2);
v___x_521_ = lean_array_fget_borrowed(v_keyArray_519_, v_x_507_);
v_isSome_522_ = lean_noption_is_some(v___x_521_);
if (v_isSome_522_ == 0)
{
lean_dec(v_x_506_);
if (lean_obj_tag(v_x_505_) == 0)
{
lean_object* v___x_523_; 
v___x_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_523_, 0, v_x_507_);
return v___x_523_;
}
else
{
lean_object* v_val_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
lean_dec(v_x_507_);
v_val_524_ = lean_ctor_get(v_x_505_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v_x_505_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v_x_505_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_val_524_);
lean_dec(v_x_505_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_val_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
else
{
lean_object* v_one_532_; lean_object* v_n_533_; lean_object* v___y_535_; 
v_one_532_ = lean_unsigned_to_nat(1u);
v_n_533_ = lean_nat_sub(v_x_506_, v_one_532_);
lean_dec(v_x_506_);
if (v_isSome_522_ == 0)
{
goto v___jp_541_;
}
else
{
lean_object* v___x_543_; uint8_t v_isSome_544_; 
v___x_543_ = lean_array_fget_borrowed(v_valueArray_520_, v_x_507_);
v_isSome_544_ = lean_noption_is_some(v___x_543_);
if (v_isSome_544_ == 0)
{
goto v___jp_541_;
}
else
{
lean_object* v_val_545_; size_t v___x_546_; size_t v___x_547_; uint8_t v___x_548_; 
lean_inc(v___x_521_);
v_val_545_ = lean_noption_get(v___x_521_);
v___x_546_ = lean_ptr_addr(v_val_545_);
v___x_547_ = lean_ptr_addr(v_query_504_);
v___x_548_ = lean_usize_dec_eq(v___x_546_, v___x_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
lean_dec(v_val_545_);
v___x_549_ = lean_array_get_size(v_keyArray_519_);
v___x_550_ = lean_nat_add(v_x_507_, v_one_532_);
lean_dec(v_x_507_);
v___x_551_ = lean_nat_dec_lt(v___x_550_, v___x_549_);
if (v___x_551_ == 0)
{
lean_dec(v___x_550_);
v_x_506_ = v_n_533_;
v_x_507_ = v_zero_508_;
goto _start;
}
else
{
v_x_506_ = v_n_533_;
v_x_507_ = v___x_550_;
goto _start;
}
}
else
{
lean_object* v_val_554_; lean_object* v___x_555_; 
lean_dec(v_n_533_);
lean_dec(v_x_505_);
lean_inc(v___x_543_);
v_val_554_ = lean_noption_get(v___x_543_);
v___x_555_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_555_, 0, v_x_507_);
lean_ctor_set(v___x_555_, 1, v_val_545_);
lean_ctor_set(v___x_555_, 2, v_val_554_);
return v___x_555_;
}
}
}
v___jp_534_:
{
lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_536_ = lean_array_get_size(v_keyArray_519_);
v___x_537_ = lean_nat_add(v_x_507_, v_one_532_);
lean_dec(v_x_507_);
v___x_538_ = lean_nat_dec_lt(v___x_537_, v___x_536_);
if (v___x_538_ == 0)
{
lean_dec(v___x_537_);
v_x_505_ = v___y_535_;
v_x_506_ = v_n_533_;
v_x_507_ = v_zero_508_;
goto _start;
}
else
{
v_x_505_ = v___y_535_;
v_x_506_ = v_n_533_;
v_x_507_ = v___x_537_;
goto _start;
}
}
v___jp_541_:
{
if (lean_obj_tag(v_x_505_) == 0)
{
lean_object* v___x_542_; 
lean_inc(v_x_507_);
v___x_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_542_, 0, v_x_507_);
v___y_535_ = v___x_542_;
goto v___jp_534_;
}
else
{
v___y_535_ = v_x_505_;
goto v___jp_534_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5___redArg___boxed(lean_object* v_m_556_, lean_object* v_query_557_, lean_object* v_x_558_, lean_object* v_x_559_, lean_object* v_x_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5___redArg(v_m_556_, v_query_557_, v_x_558_, v_x_559_, v_x_560_);
lean_dec_ref(v_query_557_);
lean_dec_ref(v_m_556_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FindSplitImpl_visit_spec__4___redArg(lean_object* v_m_562_, lean_object* v_query_563_){
_start:
{
lean_object* v_keyArray_564_; lean_object* v___x_565_; size_t v___x_566_; uint64_t v___x_567_; uint64_t v___x_568_; uint64_t v___x_569_; uint64_t v___x_570_; uint64_t v___x_571_; uint64_t v_fold_572_; uint64_t v___x_573_; uint64_t v___x_574_; uint64_t v___x_575_; size_t v___x_576_; size_t v___x_577_; size_t v___x_578_; size_t v___x_579_; size_t v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v_keyArray_564_ = lean_ctor_get(v_m_562_, 1);
v___x_565_ = lean_array_get_size(v_keyArray_564_);
v___x_566_ = lean_ptr_addr(v_query_563_);
v___x_567_ = lean_usize_to_uint64(v___x_566_);
v___x_568_ = 11ULL;
v___x_569_ = lean_uint64_mix_hash(v___x_567_, v___x_568_);
v___x_570_ = 32ULL;
v___x_571_ = lean_uint64_shift_right(v___x_569_, v___x_570_);
v_fold_572_ = lean_uint64_xor(v___x_569_, v___x_571_);
v___x_573_ = 16ULL;
v___x_574_ = lean_uint64_shift_right(v_fold_572_, v___x_573_);
v___x_575_ = lean_uint64_xor(v_fold_572_, v___x_574_);
v___x_576_ = lean_uint64_to_usize(v___x_575_);
v___x_577_ = lean_usize_of_nat(v___x_565_);
v___x_578_ = ((size_t)1ULL);
v___x_579_ = lean_usize_sub(v___x_577_, v___x_578_);
v___x_580_ = lean_usize_land(v___x_576_, v___x_579_);
v___x_581_ = lean_usize_to_nat(v___x_580_);
v___x_582_ = lean_box(0);
v___x_583_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5___redArg(v_m_562_, v_query_563_, v___x_582_, v___x_565_, v___x_581_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FindSplitImpl_visit_spec__4___redArg___boxed(lean_object* v_m_584_, lean_object* v_query_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FindSplitImpl_visit_spec__4___redArg(v_m_584_, v_query_585_);
lean_dec_ref(v_query_585_);
lean_dec_ref(v_m_584_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5_spec__7_spec__8___redArg(lean_object* v_b_587_, lean_object* v_acc_588_, lean_object* v_i_589_){
_start:
{
lean_object* v___y_591_; lean_object* v_keyArray_599_; lean_object* v_valueArray_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v_keyArray_599_ = lean_ctor_get(v_b_587_, 1);
v_valueArray_600_ = lean_ctor_get(v_b_587_, 2);
v___x_601_ = lean_array_get_size(v_keyArray_599_);
v___x_602_ = lean_nat_dec_lt(v_i_589_, v___x_601_);
if (v___x_602_ == 0)
{
lean_dec(v_i_589_);
return v_acc_588_;
}
else
{
lean_object* v___x_603_; uint8_t v_isSome_604_; 
v___x_603_ = lean_array_fget_borrowed(v_keyArray_599_, v_i_589_);
v_isSome_604_ = lean_noption_is_some(v___x_603_);
if (v_isSome_604_ == 0)
{
goto v___jp_595_;
}
else
{
lean_object* v___x_605_; uint8_t v_isSome_606_; 
v___x_605_ = lean_array_fget_borrowed(v_valueArray_600_, v_i_589_);
v_isSome_606_ = lean_noption_is_some(v___x_605_);
if (v_isSome_606_ == 0)
{
goto v___jp_595_;
}
else
{
lean_object* v_val_607_; lean_object* v_val_608_; lean_object* v_i_610_; lean_object* v___x_615_; 
lean_inc(v___x_603_);
v_val_607_ = lean_noption_get(v___x_603_);
lean_inc(v___x_605_);
v_val_608_ = lean_noption_get(v___x_605_);
v___x_615_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FindSplitImpl_visit_spec__4___redArg(v_acc_588_, v_val_607_);
switch(lean_obj_tag(v___x_615_))
{
case 0:
{
lean_object* v_index_616_; lean_object* v_size_617_; lean_object* v___x_618_; 
v_index_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_index_616_);
lean_dec_ref_known(v___x_615_, 3);
v_size_617_ = lean_ctor_get(v_acc_588_, 0);
lean_inc(v_size_617_);
v___x_618_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_588_, v_size_617_, v_index_616_, v_val_607_, v_val_608_);
lean_dec(v_index_616_);
v___y_591_ = v___x_618_;
goto v___jp_590_;
}
case 1:
{
lean_object* v_index_619_; 
v_index_619_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_index_619_);
lean_dec_ref_known(v___x_615_, 1);
v_i_610_ = v_index_619_;
goto v___jp_609_;
}
default: 
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_588_, v___x_620_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_index_622_; 
v_index_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_index_622_);
lean_dec_ref_known(v___x_621_, 1);
v_i_610_ = v_index_622_;
goto v___jp_609_;
}
else
{
lean_dec(v_val_608_);
lean_dec(v_val_607_);
v___y_591_ = v_acc_588_;
goto v___jp_590_;
}
}
}
v___jp_609_:
{
lean_object* v_size_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_size_611_ = lean_ctor_get(v_acc_588_, 0);
v___x_612_ = lean_unsigned_to_nat(1u);
v___x_613_ = lean_nat_add(v_size_611_, v___x_612_);
v___x_614_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_588_, v___x_613_, v_i_610_, v_val_607_, v_val_608_);
lean_dec(v_i_610_);
v___y_591_ = v___x_614_;
goto v___jp_590_;
}
}
}
}
v___jp_590_:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_unsigned_to_nat(1u);
v___x_593_ = lean_nat_add(v_i_589_, v___x_592_);
lean_dec(v_i_589_);
v_acc_588_ = v___y_591_;
v_i_589_ = v___x_593_;
goto _start;
}
v___jp_595_:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_unsigned_to_nat(1u);
v___x_597_ = lean_nat_add(v_i_589_, v___x_596_);
lean_dec(v_i_589_);
v_i_589_ = v___x_597_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5_spec__7_spec__8___redArg___boxed(lean_object* v_b_623_, lean_object* v_acc_624_, lean_object* v_i_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5_spec__7_spec__8___redArg(v_b_623_, v_acc_624_, v_i_625_);
lean_dec_ref(v_b_623_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5_spec__7___redArg(lean_object* v_init_627_, lean_object* v_b_628_){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5_spec__7_spec__8___redArg(v_b_628_, v_init_627_, v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5_spec__7___redArg___boxed(lean_object* v_init_631_, lean_object* v_b_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5_spec__7___redArg(v_init_631_, v_b_632_);
lean_dec_ref(v_b_632_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5___redArg(lean_object* v_m_634_){
_start:
{
lean_object* v_keyArray_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v_cellCount_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v_target_642_; lean_object* v___x_643_; 
v_keyArray_635_ = lean_ctor_get(v_m_634_, 1);
v___x_636_ = lean_array_get_size(v_keyArray_635_);
v___x_637_ = lean_unsigned_to_nat(2u);
v_cellCount_638_ = lean_nat_mul(v___x_636_, v___x_637_);
v___x_639_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_638_);
v___x_640_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_638_);
v___x_641_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_638_);
v_target_642_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_642_, 0, v___x_639_);
lean_ctor_set(v_target_642_, 1, v___x_640_);
lean_ctor_set(v_target_642_, 2, v___x_641_);
v___x_643_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5_spec__7___redArg(v_target_642_, v_m_634_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5___redArg___boxed(lean_object* v_m_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5___redArg(v_m_644_);
lean_dec_ref(v_m_644_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(lean_object* v_m_646_, lean_object* v_query_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FindSplitImpl_visit_spec__4___redArg(v_m_646_, v_query_647_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_index_649_; lean_object* v_key_650_; lean_object* v_value_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
v_index_649_ = lean_ctor_get(v___x_648_, 0);
v_key_650_ = lean_ctor_get(v___x_648_, 1);
v_value_651_ = lean_ctor_get(v___x_648_, 2);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_648_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_value_651_);
lean_inc(v_key_650_);
lean_inc(v_index_649_);
lean_dec(v___x_648_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_index_649_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_key_650_);
lean_ctor_set(v_reuseFailAlloc_657_, 2, v_value_651_);
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
lean_object* v___x_659_; 
lean_dec(v___x_648_);
v___x_659_ = lean_box(1);
return v___x_659_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg___boxed(lean_object* v_m_660_, lean_object* v_query_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(v_m_660_, v_query_661_);
lean_dec_ref(v_query_661_);
lean_dec_ref(v_m_660_);
return v_res_662_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg(lean_object* v_m_663_, lean_object* v_a_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(v_m_663_, v_a_664_);
if (lean_obj_tag(v___x_665_) == 0)
{
uint8_t v___x_666_; 
lean_dec_ref_known(v___x_665_, 3);
v___x_666_ = 1;
return v___x_666_;
}
else
{
uint8_t v___x_667_; 
v___x_667_ = 0;
return v___x_667_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg___boxed(lean_object* v_m_668_, lean_object* v_a_669_){
_start:
{
uint8_t v_res_670_; lean_object* v_r_671_; 
v_res_670_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg(v_m_668_, v_a_669_);
lean_dec_ref(v_a_669_);
lean_dec_ref(v_m_668_);
v_r_671_ = lean_box(v_res_670_);
return v_r_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_visit(lean_object* v_e_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_){
_start:
{
lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_712_; uint8_t v___x_739_; 
v___x_739_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg(v_a_674_, v_e_672_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___y_742_; lean_object* v_i_743_; lean_object* v___y_749_; lean_object* v___y_759_; lean_object* v_i_760_; lean_object* v___x_775_; 
v___x_740_ = lean_box(0);
v___x_775_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FindSplitImpl_visit_spec__4___redArg(v_a_674_, v_e_672_);
switch(lean_obj_tag(v___x_775_))
{
case 0:
{
lean_dec_ref_known(v___x_775_, 3);
v___y_712_ = v_a_674_;
goto v___jp_711_;
}
case 1:
{
lean_object* v_index_776_; lean_object* v_size_777_; lean_object* v_keyArray_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v_index_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_index_776_);
lean_dec_ref_known(v___x_775_, 1);
v_size_777_ = lean_ctor_get(v_a_674_, 0);
v_keyArray_778_ = lean_ctor_get(v_a_674_, 1);
v___x_779_ = lean_unsigned_to_nat(1u);
v___x_780_ = lean_nat_add(v_size_777_, v___x_779_);
v___x_781_ = lean_array_get_size(v_keyArray_778_);
v___x_782_ = lean_nat_dec_lt(v___x_780_, v___x_781_);
if (v___x_782_ == 0)
{
lean_dec(v___x_780_);
lean_dec(v_index_776_);
goto v___jp_765_;
}
else
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_783_ = lean_unsigned_to_nat(4u);
v___x_784_ = lean_nat_mul(v___x_780_, v___x_783_);
v___x_785_ = lean_unsigned_to_nat(3u);
v___x_786_ = lean_nat_mul(v___x_781_, v___x_785_);
v___x_787_ = lean_nat_dec_le(v___x_784_, v___x_786_);
lean_dec(v___x_786_);
lean_dec(v___x_784_);
if (v___x_787_ == 0)
{
lean_dec(v___x_780_);
lean_dec(v_index_776_);
goto v___jp_765_;
}
else
{
lean_object* v___x_788_; 
lean_inc_ref(v_e_672_);
v___x_788_ = l_Std_DHashMap_Raw_setEntry___redArg(v_a_674_, v___x_780_, v_index_776_, v_e_672_, v___x_740_);
lean_dec(v_index_776_);
v___y_712_ = v___x_788_;
goto v___jp_711_;
}
}
}
default: 
{
lean_object* v_size_789_; lean_object* v_keyArray_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_794_; 
v_size_789_ = lean_ctor_get(v_a_674_, 0);
v_keyArray_790_ = lean_ctor_get(v_a_674_, 1);
v___x_791_ = lean_unsigned_to_nat(1u);
v___x_792_ = lean_nat_add(v_size_789_, v___x_791_);
v___x_793_ = lean_array_get_size(v_keyArray_790_);
v___x_794_ = lean_nat_dec_lt(v___x_792_, v___x_793_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; 
lean_dec(v___x_792_);
v___x_795_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5___redArg(v_a_674_);
lean_dec_ref(v_a_674_);
v___y_749_ = v___x_795_;
goto v___jp_748_;
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v___x_796_ = lean_unsigned_to_nat(4u);
v___x_797_ = lean_nat_mul(v___x_792_, v___x_796_);
lean_dec(v___x_792_);
v___x_798_ = lean_unsigned_to_nat(3u);
v___x_799_ = lean_nat_mul(v___x_793_, v___x_798_);
v___x_800_ = lean_nat_dec_le(v___x_797_, v___x_799_);
lean_dec(v___x_799_);
lean_dec(v___x_797_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; 
v___x_801_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5___redArg(v_a_674_);
lean_dec_ref(v_a_674_);
v___y_749_ = v___x_801_;
goto v___jp_748_;
}
else
{
v___y_749_ = v_a_674_;
goto v___jp_748_;
}
}
}
}
v___jp_741_:
{
lean_object* v_size_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v_size_744_ = lean_ctor_get(v___y_742_, 0);
v___x_745_ = lean_unsigned_to_nat(1u);
v___x_746_ = lean_nat_add(v_size_744_, v___x_745_);
lean_inc_ref(v_e_672_);
v___x_747_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_742_, v___x_746_, v_i_743_, v_e_672_, v___x_740_);
lean_dec(v_i_743_);
v___y_712_ = v___x_747_;
goto v___jp_711_;
}
v___jp_748_:
{
lean_object* v___x_750_; 
v___x_750_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FindSplitImpl_visit_spec__4___redArg(v___y_749_, v_e_672_);
switch(lean_obj_tag(v___x_750_))
{
case 0:
{
lean_object* v_index_751_; lean_object* v_size_752_; lean_object* v___x_753_; 
v_index_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_index_751_);
lean_dec_ref_known(v___x_750_, 3);
v_size_752_ = lean_ctor_get(v___y_749_, 0);
lean_inc(v_size_752_);
lean_inc_ref(v_e_672_);
v___x_753_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_749_, v_size_752_, v_index_751_, v_e_672_, v___x_740_);
lean_dec(v_index_751_);
v___y_712_ = v___x_753_;
goto v___jp_711_;
}
case 1:
{
lean_object* v_index_754_; 
v_index_754_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_index_754_);
lean_dec_ref_known(v___x_750_, 1);
v___y_742_ = v___y_749_;
v_i_743_ = v_index_754_;
goto v___jp_741_;
}
default: 
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_unsigned_to_nat(0u);
v___x_756_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_749_, v___x_755_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_index_757_; 
v_index_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_index_757_);
lean_dec_ref_known(v___x_756_, 1);
v___y_742_ = v___y_749_;
v_i_743_ = v_index_757_;
goto v___jp_741_;
}
else
{
v___y_712_ = v___y_749_;
goto v___jp_711_;
}
}
}
}
v___jp_758_:
{
lean_object* v_size_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v_size_761_ = lean_ctor_get(v___y_759_, 0);
v___x_762_ = lean_unsigned_to_nat(1u);
v___x_763_ = lean_nat_add(v_size_761_, v___x_762_);
lean_inc_ref(v_e_672_);
v___x_764_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_759_, v___x_763_, v_i_760_, v_e_672_, v___x_740_);
lean_dec(v_i_760_);
v___y_712_ = v___x_764_;
goto v___jp_711_;
}
v___jp_765_:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5___redArg(v_a_674_);
lean_dec_ref(v_a_674_);
v___x_767_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FindSplitImpl_visit_spec__4___redArg(v___x_766_, v_e_672_);
switch(lean_obj_tag(v___x_767_))
{
case 0:
{
lean_object* v_index_768_; lean_object* v_size_769_; lean_object* v___x_770_; 
v_index_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_index_768_);
lean_dec_ref_known(v___x_767_, 3);
v_size_769_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_size_769_);
lean_inc_ref(v_e_672_);
v___x_770_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_766_, v_size_769_, v_index_768_, v_e_672_, v___x_740_);
lean_dec(v_index_768_);
v___y_712_ = v___x_770_;
goto v___jp_711_;
}
case 1:
{
lean_object* v_index_771_; 
v_index_771_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_index_771_);
lean_dec_ref_known(v___x_767_, 1);
v___y_759_ = v___x_766_;
v_i_760_ = v_index_771_;
goto v___jp_758_;
}
default: 
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = lean_unsigned_to_nat(0u);
v___x_773_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_766_, v___x_772_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_index_774_; 
v_index_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_index_774_);
lean_dec_ref_known(v___x_773_, 1);
v___y_759_ = v___x_766_;
v_i_760_ = v_index_774_;
goto v___jp_758_;
}
else
{
v___y_712_ = v___x_766_;
goto v___jp_711_;
}
}
}
}
}
else
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
lean_dec_ref(v_e_672_);
v___x_802_ = lean_box(0);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
lean_ctor_set(v___x_803_, 1, v_a_674_);
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
return v___x_804_;
}
v___jp_680_:
{
switch(lean_obj_tag(v_e_672_))
{
case 6:
{
lean_object* v_body_687_; 
v_body_687_ = lean_ctor_get(v_e_672_, 2);
lean_inc_ref(v_body_687_);
lean_dec_ref_known(v_e_672_, 3);
v_e_672_ = v_body_687_;
v_a_673_ = v___y_681_;
v_a_674_ = v___y_682_;
v_a_675_ = v___y_683_;
v_a_676_ = v___y_684_;
v_a_677_ = v___y_685_;
v_a_678_ = v___y_686_;
goto _start;
}
case 11:
{
lean_object* v_struct_689_; 
v_struct_689_ = lean_ctor_get(v_e_672_, 2);
lean_inc_ref(v_struct_689_);
lean_dec_ref_known(v_e_672_, 3);
v_e_672_ = v_struct_689_;
v_a_673_ = v___y_681_;
v_a_674_ = v___y_682_;
v_a_675_ = v___y_683_;
v_a_676_ = v___y_684_;
v_a_677_ = v___y_685_;
v_a_678_ = v___y_686_;
goto _start;
}
case 10:
{
lean_object* v_expr_691_; 
v_expr_691_ = lean_ctor_get(v_e_672_, 1);
lean_inc_ref(v_expr_691_);
lean_dec_ref_known(v_e_672_, 2);
v_e_672_ = v_expr_691_;
v_a_673_ = v___y_681_;
v_a_674_ = v___y_682_;
v_a_675_ = v___y_683_;
v_a_676_ = v___y_684_;
v_a_677_ = v___y_685_;
v_a_678_ = v___y_686_;
goto _start;
}
case 7:
{
lean_object* v_binderType_693_; lean_object* v_body_694_; lean_object* v___x_695_; 
v_binderType_693_ = lean_ctor_get(v_e_672_, 1);
lean_inc_ref(v_binderType_693_);
v_body_694_ = lean_ctor_get(v_e_672_, 2);
lean_inc_ref(v_body_694_);
lean_dec_ref_known(v_e_672_, 3);
v___x_695_ = l_Lean_Meta_FindSplitImpl_visit(v_binderType_693_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v_fst_697_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
v_fst_697_ = lean_ctor_get(v_a_696_, 0);
if (lean_obj_tag(v_fst_697_) == 0)
{
lean_object* v_snd_698_; 
lean_dec_ref_known(v___x_695_, 1);
v_snd_698_ = lean_ctor_get(v_a_696_, 1);
lean_inc(v_snd_698_);
lean_dec(v_a_696_);
v_e_672_ = v_body_694_;
v_a_673_ = v___y_681_;
v_a_674_ = v_snd_698_;
v_a_675_ = v___y_683_;
v_a_676_ = v___y_684_;
v_a_677_ = v___y_685_;
v_a_678_ = v___y_686_;
goto _start;
}
else
{
lean_dec(v_a_696_);
lean_dec_ref(v_body_694_);
return v___x_695_;
}
}
else
{
lean_dec_ref(v_body_694_);
return v___x_695_;
}
}
case 8:
{
lean_object* v_value_700_; lean_object* v_body_701_; lean_object* v___x_702_; 
v_value_700_ = lean_ctor_get(v_e_672_, 2);
lean_inc_ref(v_value_700_);
v_body_701_ = lean_ctor_get(v_e_672_, 3);
lean_inc_ref(v_body_701_);
lean_dec_ref_known(v_e_672_, 4);
v___x_702_ = l_Lean_Meta_FindSplitImpl_visit(v_value_700_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v_fst_704_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
v_fst_704_ = lean_ctor_get(v_a_703_, 0);
if (lean_obj_tag(v_fst_704_) == 0)
{
lean_object* v_snd_705_; 
lean_dec_ref_known(v___x_702_, 1);
v_snd_705_ = lean_ctor_get(v_a_703_, 1);
lean_inc(v_snd_705_);
lean_dec(v_a_703_);
v_e_672_ = v_body_701_;
v_a_673_ = v___y_681_;
v_a_674_ = v_snd_705_;
v_a_675_ = v___y_683_;
v_a_676_ = v___y_684_;
v_a_677_ = v___y_685_;
v_a_678_ = v___y_686_;
goto _start;
}
else
{
lean_dec(v_a_703_);
lean_dec_ref(v_body_701_);
return v___x_702_;
}
}
else
{
lean_dec_ref(v_body_701_);
return v___x_702_;
}
}
case 5:
{
lean_object* v___x_707_; 
v___x_707_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f(v_e_672_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
return v___x_707_;
}
default: 
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
lean_dec_ref(v_e_672_);
v___x_708_ = lean_box(0);
v___x_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v___y_682_);
v___x_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
return v___x_710_;
}
}
}
v___jp_711_:
{
lean_object* v___x_713_; lean_object* v_env_714_; lean_object* v___x_715_; 
v___x_713_ = lean_st_ref_get(v_a_678_);
v_env_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc_ref(v_env_714_);
lean_dec(v___x_713_);
lean_inc_ref(v_e_672_);
v___x_715_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f(v_env_714_, v_a_673_, v_e_672_);
if (lean_obj_tag(v___x_715_) == 1)
{
lean_object* v___x_716_; lean_object* v___x_717_; 
lean_dec_ref(v_e_672_);
v___x_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
lean_ctor_set(v___x_716_, 1, v___y_712_);
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
return v___x_717_;
}
else
{
uint8_t v___x_718_; 
lean_dec(v___x_715_);
v___x_718_ = l_Lean_Expr_hasLooseBVars(v_e_672_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; 
lean_inc_ref(v_e_672_);
v___x_719_ = l_Lean_Meta_isProof(v_e_672_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_730_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_730_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_730_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_730_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
uint8_t v___x_724_; 
v___x_724_ = lean_unbox(v_a_720_);
lean_dec(v_a_720_);
if (v___x_724_ == 0)
{
lean_del_object(v___x_722_);
v___y_681_ = v_a_673_;
v___y_682_ = v___y_712_;
v___y_683_ = v_a_675_;
v___y_684_ = v_a_676_;
v___y_685_ = v_a_677_;
v___y_686_ = v_a_678_;
goto v___jp_680_;
}
else
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
lean_dec_ref(v_e_672_);
v___x_725_ = lean_box(0);
v___x_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
lean_ctor_set(v___x_726_, 1, v___y_712_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v___x_726_);
v___x_728_ = v___x_722_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec_ref(v___y_712_);
lean_dec_ref(v_e_672_);
v_a_731_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_719_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_719_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
else
{
v___y_681_ = v_a_673_;
v___y_682_ = v___y_712_;
v___y_683_ = v_a_675_;
v___y_684_ = v_a_676_;
v___y_685_ = v_a_677_;
v___y_686_ = v_a_678_;
goto v___jp_680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(lean_object* v_upperBound_805_, lean_object* v_args_806_, lean_object* v_info_807_, lean_object* v_a_808_, lean_object* v_b_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v_a_818_; lean_object* v_snd_819_; lean_object* v_a_823_; lean_object* v_snd_824_; uint8_t v___x_828_; 
v___x_828_ = lean_nat_dec_lt(v_a_808_, v_upperBound_805_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; 
lean_dec(v_a_808_);
v___x_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_829_, 0, v_b_809_);
lean_ctor_set(v___x_829_, 1, v___y_811_);
v___x_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
return v___x_830_;
}
else
{
lean_object* v_paramInfo_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; uint8_t v___x_836_; 
lean_dec_ref(v_b_809_);
v_paramInfo_831_ = lean_ctor_get(v_info_807_, 0);
v___x_832_ = lean_box(0);
v___x_833_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0));
v___x_834_ = lean_array_fget_borrowed(v_args_806_, v_a_808_);
v___x_835_ = lean_array_get_size(v_paramInfo_831_);
v___x_836_ = lean_nat_dec_lt(v_a_808_, v___x_835_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; 
lean_inc(v___x_834_);
v___x_837_ = l_Lean_Meta_FindSplitImpl_visit(v___x_834_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v_fst_839_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref_known(v___x_837_, 1);
v_fst_839_ = lean_ctor_get(v_a_838_, 0);
if (lean_obj_tag(v_fst_839_) == 1)
{
lean_object* v_snd_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_848_; 
lean_inc_ref(v_fst_839_);
lean_dec(v_a_808_);
v_snd_840_ = lean_ctor_get(v_a_838_, 1);
v_isSharedCheck_848_ = !lean_is_exclusive(v_a_838_);
if (v_isSharedCheck_848_ == 0)
{
lean_object* v_unused_849_; 
v_unused_849_ = lean_ctor_get(v_a_838_, 0);
lean_dec(v_unused_849_);
v___x_842_ = v_a_838_;
v_isShared_843_ = v_isSharedCheck_848_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_snd_840_);
lean_dec(v_a_838_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_848_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_844_, 0, v_fst_839_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 1, v___x_832_);
lean_ctor_set(v___x_842_, 0, v___x_844_);
v___x_846_ = v___x_842_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v___x_832_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
v_a_818_ = v___x_846_;
v_snd_819_ = v_snd_840_;
goto v___jp_817_;
}
}
}
else
{
lean_object* v_snd_850_; 
v_snd_850_ = lean_ctor_get(v_a_838_, 1);
lean_inc(v_snd_850_);
lean_dec(v_a_838_);
v_a_823_ = v___x_833_;
v_snd_824_ = v_snd_850_;
goto v___jp_822_;
}
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_dec(v_a_808_);
v_a_851_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_837_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_837_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
else
{
lean_object* v___x_859_; uint8_t v_isProp_860_; 
v___x_859_ = lean_array_fget_borrowed(v_paramInfo_831_, v_a_808_);
v_isProp_860_ = lean_ctor_get_uint8(v___x_859_, sizeof(void*)*1 + 2);
if (v_isProp_860_ == 0)
{
uint8_t v___x_861_; 
v___x_861_ = l_Lean_Meta_ParamInfo_isExplicit(v___x_859_);
if (v___x_861_ == 0)
{
v_a_823_ = v___x_833_;
v_snd_824_ = v___y_811_;
goto v___jp_822_;
}
else
{
lean_object* v___x_862_; 
lean_inc(v___x_834_);
v___x_862_ = l_Lean_Meta_FindSplitImpl_visit(v___x_834_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v_fst_864_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref_known(v___x_862_, 1);
v_fst_864_ = lean_ctor_get(v_a_863_, 0);
if (lean_obj_tag(v_fst_864_) == 1)
{
lean_object* v_snd_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_873_; 
lean_inc_ref(v_fst_864_);
lean_dec(v_a_808_);
v_snd_865_ = lean_ctor_get(v_a_863_, 1);
v_isSharedCheck_873_ = !lean_is_exclusive(v_a_863_);
if (v_isSharedCheck_873_ == 0)
{
lean_object* v_unused_874_; 
v_unused_874_ = lean_ctor_get(v_a_863_, 0);
lean_dec(v_unused_874_);
v___x_867_ = v_a_863_;
v_isShared_868_ = v_isSharedCheck_873_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_snd_865_);
lean_dec(v_a_863_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_873_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_869_, 0, v_fst_864_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 1, v___x_832_);
lean_ctor_set(v___x_867_, 0, v___x_869_);
v___x_871_ = v___x_867_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v___x_832_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
v_a_818_ = v___x_871_;
v_snd_819_ = v_snd_865_;
goto v___jp_817_;
}
}
}
else
{
lean_object* v_snd_875_; 
v_snd_875_ = lean_ctor_get(v_a_863_, 1);
lean_inc(v_snd_875_);
lean_dec(v_a_863_);
v_a_823_ = v___x_833_;
v_snd_824_ = v_snd_875_;
goto v___jp_822_;
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec(v_a_808_);
v_a_876_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_862_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_862_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
}
else
{
v_a_823_ = v___x_833_;
v_snd_824_ = v___y_811_;
goto v___jp_822_;
}
}
}
v___jp_817_:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v_a_818_);
lean_ctor_set(v___x_820_, 1, v_snd_819_);
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
return v___x_821_;
}
v___jp_822_:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = lean_unsigned_to_nat(1u);
v___x_826_ = lean_nat_add(v_a_808_, v___x_825_);
lean_dec(v_a_808_);
lean_inc_ref(v_a_823_);
v_a_808_ = v___x_826_;
v_b_809_ = v_a_823_;
v___y_811_ = v_snd_824_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1(lean_object* v_x_888_, lean_object* v_x_889_, lean_object* v_x_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v_info_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; 
if (lean_obj_tag(v_x_888_) == 5)
{
lean_object* v_fn_940_; lean_object* v_arg_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v_fn_940_ = lean_ctor_get(v_x_888_, 0);
lean_inc_ref(v_fn_940_);
v_arg_941_ = lean_ctor_get(v_x_888_, 1);
lean_inc_ref(v_arg_941_);
lean_dec_ref_known(v_x_888_, 2);
v___x_942_ = lean_array_set(v_x_889_, v_x_890_, v_arg_941_);
v___x_943_ = lean_unsigned_to_nat(1u);
v___x_944_ = lean_nat_sub(v_x_890_, v___x_943_);
lean_dec(v_x_890_);
v_x_888_ = v_fn_940_;
v_x_889_ = v___x_942_;
v_x_890_ = v___x_944_;
goto _start;
}
else
{
uint8_t v___x_946_; 
lean_dec(v_x_890_);
v___x_946_ = l_Lean_Expr_hasLooseBVars(v_x_888_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_box(0);
lean_inc_ref(v_x_888_);
v___x_948_ = l_Lean_Meta_getFunInfo(v_x_888_, v___x_947_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_949_);
lean_dec_ref_known(v___x_948_, 1);
v_info_899_ = v_a_949_;
v___y_900_ = v___y_891_;
v___y_901_ = v___y_892_;
v___y_902_ = v___y_893_;
v___y_903_ = v___y_894_;
v___y_904_ = v___y_895_;
v___y_905_ = v___y_896_;
goto v___jp_898_;
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec_ref(v___y_892_);
lean_dec_ref(v_x_889_);
lean_dec_ref(v_x_888_);
v_a_950_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_948_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_948_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
else
{
lean_object* v___x_958_; 
v___x_958_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___closed__1));
v_info_899_ = v___x_958_;
v___y_900_ = v___y_891_;
v___y_901_ = v___y_892_;
v___y_902_ = v___y_893_;
v___y_903_ = v___y_894_;
v___y_904_ = v___y_895_;
v___y_905_ = v___y_896_;
goto v___jp_898_;
}
}
v___jp_898_:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_906_ = lean_array_get_size(v_x_889_);
v___x_907_ = lean_unsigned_to_nat(0u);
v___x_908_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0));
v___x_909_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(v___x_906_, v_x_889_, v_info_899_, v___x_907_, v___x_908_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec_ref(v_info_899_);
lean_dec_ref(v_x_889_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_931_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_931_ == 0)
{
v___x_912_ = v___x_909_;
v_isShared_913_ = v_isSharedCheck_931_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_909_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_931_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v_fst_914_; lean_object* v_fst_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_929_; 
v_fst_914_ = lean_ctor_get(v_a_910_, 0);
lean_inc(v_fst_914_);
v_fst_915_ = lean_ctor_get(v_fst_914_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v_fst_914_);
if (v_isSharedCheck_929_ == 0)
{
lean_object* v_unused_930_; 
v_unused_930_ = lean_ctor_get(v_fst_914_, 1);
lean_dec(v_unused_930_);
v___x_917_ = v_fst_914_;
v_isShared_918_ = v_isSharedCheck_929_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_fst_915_);
lean_dec(v_fst_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_929_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
if (lean_obj_tag(v_fst_915_) == 0)
{
lean_object* v_snd_919_; lean_object* v___x_920_; 
lean_del_object(v___x_917_);
lean_del_object(v___x_912_);
v_snd_919_ = lean_ctor_get(v_a_910_, 1);
lean_inc(v_snd_919_);
lean_dec(v_a_910_);
v___x_920_ = l_Lean_Meta_FindSplitImpl_visit(v_x_888_, v___y_900_, v_snd_919_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
return v___x_920_;
}
else
{
lean_object* v_snd_921_; lean_object* v_val_922_; lean_object* v___x_924_; 
lean_dec_ref(v_x_888_);
v_snd_921_ = lean_ctor_get(v_a_910_, 1);
lean_inc(v_snd_921_);
lean_dec(v_a_910_);
v_val_922_ = lean_ctor_get(v_fst_915_, 0);
lean_inc(v_val_922_);
lean_dec_ref_known(v_fst_915_, 1);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 1, v_snd_921_);
lean_ctor_set(v___x_917_, 0, v_val_922_);
v___x_924_ = v___x_917_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_val_922_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v_snd_921_);
v___x_924_ = v_reuseFailAlloc_928_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
lean_object* v___x_926_; 
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v___x_924_);
v___x_926_ = v___x_912_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_924_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
}
}
else
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
lean_dec_ref(v_x_888_);
v_a_932_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_909_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_909_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f(lean_object* v_e_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v_dummy_967_; lean_object* v_nargs_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v_dummy_967_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0);
v_nargs_968_ = l_Lean_Expr_getAppNumArgs(v_e_959_);
lean_inc(v_nargs_968_);
v___x_969_ = lean_mk_array(v_nargs_968_, v_dummy_967_);
v___x_970_ = lean_unsigned_to_nat(1u);
v___x_971_ = lean_nat_sub(v_nargs_968_, v___x_970_);
lean_dec(v_nargs_968_);
v___x_972_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1(v_e_959_, v___x_969_, v___x_971_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f___boxed(lean_object* v_e_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f(v_e_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
lean_dec(v_a_979_);
lean_dec_ref(v_a_978_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec_ref(v_a_974_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___boxed(lean_object* v_x_982_, lean_object* v_x_983_, lean_object* v_x_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1(v_x_982_, v_x_983_, v_x_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec_ref(v___y_985_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg___boxed(lean_object* v_upperBound_993_, lean_object* v_args_994_, lean_object* v_info_995_, lean_object* v_a_996_, lean_object* v_b_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(v_upperBound_993_, v_args_994_, v_info_995_, v_a_996_, v_b_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec_ref(v___y_998_);
lean_dec_ref(v_info_995_);
lean_dec_ref(v_args_994_);
lean_dec(v_upperBound_993_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_visit___boxed(lean_object* v_e_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lean_Meta_FindSplitImpl_visit(v_e_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec_ref(v_a_1007_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0(lean_object* v_upperBound_1015_, lean_object* v_args_1016_, lean_object* v_info_1017_, lean_object* v_inst_1018_, lean_object* v_R_1019_, lean_object* v_a_1020_, lean_object* v_b_1021_, lean_object* v_c_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(v_upperBound_1015_, v_args_1016_, v_info_1017_, v_a_1020_, v_b_1021_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___boxed(lean_object* v_upperBound_1031_, lean_object* v_args_1032_, lean_object* v_info_1033_, lean_object* v_inst_1034_, lean_object* v_R_1035_, lean_object* v_a_1036_, lean_object* v_b_1037_, lean_object* v_c_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0(v_upperBound_1031_, v_args_1032_, v_info_1033_, v_inst_1034_, v_R_1035_, v_a_1036_, v_b_1037_, v_c_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec_ref(v___y_1039_);
lean_dec_ref(v_info_1033_);
lean_dec_ref(v_args_1032_);
lean_dec(v_upperBound_1031_);
return v_res_1046_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3(lean_object* v_00_u03b2_1047_, lean_object* v_m_1048_, lean_object* v_a_1049_){
_start:
{
uint8_t v___x_1050_; 
v___x_1050_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg(v_m_1048_, v_a_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___boxed(lean_object* v_00_u03b2_1051_, lean_object* v_m_1052_, lean_object* v_a_1053_){
_start:
{
uint8_t v_res_1054_; lean_object* v_r_1055_; 
v_res_1054_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3(v_00_u03b2_1051_, v_m_1052_, v_a_1053_);
lean_dec_ref(v_a_1053_);
lean_dec_ref(v_m_1052_);
v_r_1055_ = lean_box(v_res_1054_);
return v_r_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FindSplitImpl_visit_spec__4(lean_object* v_00_u03b2_1056_, lean_object* v_m_1057_, lean_object* v_query_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FindSplitImpl_visit_spec__4___redArg(v_m_1057_, v_query_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FindSplitImpl_visit_spec__4___boxed(lean_object* v_00_u03b2_1060_, lean_object* v_m_1061_, lean_object* v_query_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FindSplitImpl_visit_spec__4(v_00_u03b2_1060_, v_m_1061_, v_query_1062_);
lean_dec_ref(v_query_1062_);
lean_dec_ref(v_m_1061_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5(lean_object* v_00_u03b2_1064_, lean_object* v_m_1065_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5___redArg(v_m_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5___boxed(lean_object* v_00_u03b2_1067_, lean_object* v_m_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5(v_00_u03b2_1067_, v_m_1068_);
lean_dec_ref(v_m_1068_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3(lean_object* v_00_u03b2_1070_, lean_object* v_m_1071_, lean_object* v_query_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(v_m_1071_, v_query_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___boxed(lean_object* v_00_u03b2_1074_, lean_object* v_m_1075_, lean_object* v_query_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3(v_00_u03b2_1074_, v_m_1075_, v_query_1076_);
lean_dec_ref(v_query_1076_);
lean_dec_ref(v_m_1075_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5(lean_object* v_00_u03b2_1078_, lean_object* v_m_1079_, lean_object* v_query_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5___redArg(v_m_1079_, v_query_1080_, v_x_1081_, v_x_1082_, v_x_1083_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5___boxed(lean_object* v_00_u03b2_1086_, lean_object* v_m_1087_, lean_object* v_query_1088_, lean_object* v_x_1089_, lean_object* v_x_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5(v_00_u03b2_1086_, v_m_1087_, v_query_1088_, v_x_1089_, v_x_1090_, v_x_1091_, v_x_1092_);
lean_dec_ref(v_query_1088_);
lean_dec_ref(v_m_1087_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5_spec__7(lean_object* v_00_u03b2_1094_, lean_object* v_init_1095_, lean_object* v_b_1096_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5_spec__7___redArg(v_init_1095_, v_b_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5_spec__7___boxed(lean_object* v_00_u03b2_1098_, lean_object* v_init_1099_, lean_object* v_b_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5_spec__7(v_00_u03b2_1098_, v_init_1099_, v_b_1100_);
lean_dec_ref(v_b_1100_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5_spec__7_spec__8(lean_object* v_00_u03b2_1102_, lean_object* v_b_1103_, lean_object* v_acc_1104_, lean_object* v_i_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5_spec__7_spec__8___redArg(v_b_1103_, v_acc_1104_, v_i_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5_spec__7_spec__8___boxed(lean_object* v_00_u03b2_1107_, lean_object* v_b_1108_, lean_object* v_acc_1109_, lean_object* v_i_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FindSplitImpl_visit_spec__5_spec__7_spec__8(v_00_u03b2_1107_, v_b_1108_, v_acc_1109_, v_i_1110_);
lean_dec_ref(v_b_1108_);
return v_res_1111_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = lean_unsigned_to_nat(64u);
v___x_1113_ = l_Lean_mkPtrSet___redArg(v___x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1(uint8_t v_kind_1114_, lean_object* v_exceptionSet_1115_, lean_object* v_e_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1122_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1122_, 0, v_exceptionSet_1115_);
lean_ctor_set_uint8(v___x_1122_, sizeof(void*)*1, v_kind_1114_);
v___x_1123_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0);
v___x_1124_ = l_Lean_Meta_FindSplitImpl_visit(v_e_1116_, v___x_1122_, v___x_1123_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
lean_dec_ref_known(v___x_1122_, 1);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1133_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1133_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1133_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v_fst_1129_; lean_object* v___x_1131_; 
v_fst_1129_ = lean_ctor_get(v_a_1125_, 0);
lean_inc(v_fst_1129_);
lean_dec(v_a_1125_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v_fst_1129_);
v___x_1131_ = v___x_1127_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_fst_1129_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
v_a_1134_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1124_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1124_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___boxed(lean_object* v_kind_1142_, lean_object* v_exceptionSet_1143_, lean_object* v_e_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_){
_start:
{
uint8_t v_kind_boxed_1150_; lean_object* v_res_1151_; 
v_kind_boxed_1150_ = lean_unbox(v_kind_1142_);
v_res_1151_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1(v_kind_boxed_1150_, v_exceptionSet_1143_, v_e_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
lean_dec(v_a_1148_);
lean_dec_ref(v_a_1147_);
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1145_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(lean_object* v_msgData_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v___x_1158_; lean_object* v_env_1159_; lean_object* v___x_1160_; lean_object* v_mctx_1161_; lean_object* v_lctx_1162_; lean_object* v_options_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1158_ = lean_st_ref_get(v___y_1156_);
v_env_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc_ref(v_env_1159_);
lean_dec(v___x_1158_);
v___x_1160_ = lean_st_ref_get(v___y_1154_);
v_mctx_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc_ref(v_mctx_1161_);
lean_dec(v___x_1160_);
v_lctx_1162_ = lean_ctor_get(v___y_1153_, 2);
v_options_1163_ = lean_ctor_get(v___y_1155_, 2);
lean_inc_ref(v_options_1163_);
lean_inc_ref(v_lctx_1162_);
v___x_1164_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1164_, 0, v_env_1159_);
lean_ctor_set(v___x_1164_, 1, v_mctx_1161_);
lean_ctor_set(v___x_1164_, 2, v_lctx_1162_);
lean_ctor_set(v___x_1164_, 3, v_options_1163_);
v___x_1165_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
lean_ctor_set(v___x_1165_, 1, v_msgData_1152_);
v___x_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0___boxed(lean_object* v_msgData_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(v_msgData_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
return v_res_1173_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1174_; double v___x_1175_; 
v___x_1174_ = lean_unsigned_to_nat(0u);
v___x_1175_ = lean_float_of_nat(v___x_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(lean_object* v_cls_1179_, lean_object* v_msg_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v_ref_1186_; lean_object* v___x_1187_; lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1232_; 
v_ref_1186_ = lean_ctor_get(v___y_1183_, 5);
v___x_1187_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(v_msg_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1190_ = v___x_1187_;
v_isShared_1191_ = v_isSharedCheck_1232_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1187_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1232_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; lean_object* v_traceState_1193_; lean_object* v_env_1194_; lean_object* v_nextMacroScope_1195_; lean_object* v_ngen_1196_; lean_object* v_auxDeclNGen_1197_; lean_object* v_cache_1198_; lean_object* v_messages_1199_; lean_object* v_infoState_1200_; lean_object* v_snapshotTasks_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1231_; 
v___x_1192_ = lean_st_ref_take(v___y_1184_);
v_traceState_1193_ = lean_ctor_get(v___x_1192_, 4);
v_env_1194_ = lean_ctor_get(v___x_1192_, 0);
v_nextMacroScope_1195_ = lean_ctor_get(v___x_1192_, 1);
v_ngen_1196_ = lean_ctor_get(v___x_1192_, 2);
v_auxDeclNGen_1197_ = lean_ctor_get(v___x_1192_, 3);
v_cache_1198_ = lean_ctor_get(v___x_1192_, 5);
v_messages_1199_ = lean_ctor_get(v___x_1192_, 6);
v_infoState_1200_ = lean_ctor_get(v___x_1192_, 7);
v_snapshotTasks_1201_ = lean_ctor_get(v___x_1192_, 8);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1203_ = v___x_1192_;
v_isShared_1204_ = v_isSharedCheck_1231_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_snapshotTasks_1201_);
lean_inc(v_infoState_1200_);
lean_inc(v_messages_1199_);
lean_inc(v_cache_1198_);
lean_inc(v_traceState_1193_);
lean_inc(v_auxDeclNGen_1197_);
lean_inc(v_ngen_1196_);
lean_inc(v_nextMacroScope_1195_);
lean_inc(v_env_1194_);
lean_dec(v___x_1192_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1231_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
uint64_t v_tid_1205_; lean_object* v_traces_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1230_; 
v_tid_1205_ = lean_ctor_get_uint64(v_traceState_1193_, sizeof(void*)*1);
v_traces_1206_ = lean_ctor_get(v_traceState_1193_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_traceState_1193_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1208_ = v_traceState_1193_;
v_isShared_1209_ = v_isSharedCheck_1230_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_traces_1206_);
lean_dec(v_traceState_1193_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1230_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; double v___x_1211_; uint8_t v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1210_ = lean_box(0);
v___x_1211_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0);
v___x_1212_ = 0;
v___x_1213_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__1));
v___x_1214_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1214_, 0, v_cls_1179_);
lean_ctor_set(v___x_1214_, 1, v___x_1210_);
lean_ctor_set(v___x_1214_, 2, v___x_1213_);
lean_ctor_set_float(v___x_1214_, sizeof(void*)*3, v___x_1211_);
lean_ctor_set_float(v___x_1214_, sizeof(void*)*3 + 8, v___x_1211_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*3 + 16, v___x_1212_);
v___x_1215_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__2));
v___x_1216_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1214_);
lean_ctor_set(v___x_1216_, 1, v_a_1188_);
lean_ctor_set(v___x_1216_, 2, v___x_1215_);
lean_inc(v_ref_1186_);
v___x_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1217_, 0, v_ref_1186_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
v___x_1218_ = l_Lean_PersistentArray_push___redArg(v_traces_1206_, v___x_1217_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1218_);
v___x_1220_ = v___x_1208_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1218_);
lean_ctor_set_uint64(v_reuseFailAlloc_1229_, sizeof(void*)*1, v_tid_1205_);
v___x_1220_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1222_; 
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 4, v___x_1220_);
v___x_1222_ = v___x_1203_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_env_1194_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_nextMacroScope_1195_);
lean_ctor_set(v_reuseFailAlloc_1228_, 2, v_ngen_1196_);
lean_ctor_set(v_reuseFailAlloc_1228_, 3, v_auxDeclNGen_1197_);
lean_ctor_set(v_reuseFailAlloc_1228_, 4, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1228_, 5, v_cache_1198_);
lean_ctor_set(v_reuseFailAlloc_1228_, 6, v_messages_1199_);
lean_ctor_set(v_reuseFailAlloc_1228_, 7, v_infoState_1200_);
lean_ctor_set(v_reuseFailAlloc_1228_, 8, v_snapshotTasks_1201_);
v___x_1222_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1226_; 
v___x_1223_ = lean_st_ref_put(v___y_1184_, v___x_1222_);
v___x_1224_ = lean_box(0);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1224_);
v___x_1226_ = v___x_1190_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___boxed(lean_object* v_cls_1233_, lean_object* v_msg_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v_cls_1233_, v_msg_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
return v_res_1240_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5(void){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1249_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__2));
v___x_1250_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4));
v___x_1251_ = l_Lean_Name_append(v___x_1250_, v___x_1249_);
return v___x_1251_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7(void){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__6));
v___x_1254_ = l_Lean_stringToMessageData(v___x_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f(uint8_t v_kind_1255_, lean_object* v_exceptionSet_1256_, lean_object* v_e_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1263_, 0, v_exceptionSet_1256_);
lean_ctor_set_uint8(v___x_1263_, sizeof(void*)*1, v_kind_1255_);
v___x_1264_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0);
v___x_1265_ = l_Lean_Meta_FindSplitImpl_visit(v_e_1257_, v___x_1263_, v___x_1264_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
lean_dec_ref_known(v___x_1263_, 1);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1312_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1312_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1312_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v_fst_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1310_; 
v_fst_1270_ = lean_ctor_get(v_a_1266_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v_a_1266_);
if (v_isSharedCheck_1310_ == 0)
{
lean_object* v_unused_1311_; 
v_unused_1311_ = lean_ctor_get(v_a_1266_, 1);
lean_dec(v_unused_1311_);
v___x_1272_ = v_a_1266_;
v_isShared_1273_ = v_isSharedCheck_1310_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_fst_1270_);
lean_dec(v_a_1266_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1310_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
if (lean_obj_tag(v_fst_1270_) == 1)
{
lean_object* v_options_1274_; lean_object* v_val_1275_; lean_object* v_inheritedTraceOptions_1276_; uint8_t v_hasTrace_1277_; lean_object* v___x_1279_; 
v_options_1274_ = lean_ctor_get(v_a_1260_, 2);
v_val_1275_ = lean_ctor_get(v_fst_1270_, 0);
v_inheritedTraceOptions_1276_ = lean_ctor_get(v_a_1260_, 13);
v_hasTrace_1277_ = lean_ctor_get_uint8(v_options_1274_, sizeof(void*)*1);
lean_inc_ref(v_fst_1270_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v_fst_1270_);
v___x_1279_ = v___x_1268_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_fst_1270_);
v___x_1279_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
if (v_hasTrace_1277_ == 0)
{
lean_dec_ref_known(v_fst_1270_, 1);
lean_del_object(v___x_1272_);
return v___x_1279_;
}
else
{
lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1280_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__2));
v___x_1281_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5);
v___x_1282_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1276_, v_options_1274_, v___x_1281_);
if (v___x_1282_ == 0)
{
lean_dec_ref_known(v_fst_1270_, 1);
lean_del_object(v___x_1272_);
return v___x_1279_;
}
else
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1286_; 
lean_dec_ref(v___x_1279_);
v___x_1283_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7);
lean_inc(v_val_1275_);
v___x_1284_ = l_Lean_indentExpr(v_val_1275_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set_tag(v___x_1272_, 7);
lean_ctor_set(v___x_1272_, 1, v___x_1284_);
lean_ctor_set(v___x_1272_, 0, v___x_1283_);
v___x_1286_ = v___x_1272_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1283_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1287_; 
v___x_1287_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_1280_, v___x_1286_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1294_ == 0)
{
lean_object* v_unused_1295_; 
v_unused_1295_ = lean_ctor_get(v___x_1287_, 0);
lean_dec(v_unused_1295_);
v___x_1289_ = v___x_1287_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_dec(v___x_1287_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v_fst_1270_);
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_fst_1270_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec_ref_known(v_fst_1270_, 1);
v_a_1296_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1287_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1287_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
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
}
}
}
else
{
lean_object* v___x_1306_; lean_object* v___x_1308_; 
lean_del_object(v___x_1272_);
lean_dec(v_fst_1270_);
v___x_1306_ = lean_box(0);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1306_);
v___x_1308_ = v___x_1268_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1306_);
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
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
v_a_1313_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1265_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1265_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___boxed(lean_object* v_kind_1321_, lean_object* v_exceptionSet_1322_, lean_object* v_e_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
uint8_t v_kind_boxed_1329_; lean_object* v_res_1330_; 
v_kind_boxed_1329_ = lean_unbox(v_kind_1321_);
v_res_1330_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f(v_kind_boxed_1329_, v_exceptionSet_1322_, v_e_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(uint8_t v_kind_1331_, lean_object* v_exceptionSet_1332_, lean_object* v_e_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_){
_start:
{
lean_object* v___y_1340_; lean_object* v___x_1343_; 
lean_inc_ref(v_exceptionSet_1332_);
v___x_1343_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f(v_kind_1331_, v_exceptionSet_1332_, v_e_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
if (lean_obj_tag(v_a_1344_) == 1)
{
lean_object* v_val_1345_; uint8_t v___y_1347_; uint8_t v___x_1353_; 
v_val_1345_ = lean_ctor_get(v_a_1344_, 0);
lean_inc(v_val_1345_);
lean_dec_ref_known(v_a_1344_, 1);
v___x_1353_ = l_Lean_Expr_isIte(v_val_1345_);
if (v___x_1353_ == 0)
{
uint8_t v___x_1354_; 
v___x_1354_ = l_Lean_Expr_isDIte(v_val_1345_);
v___y_1347_ = v___x_1354_;
goto v___jp_1346_;
}
else
{
v___y_1347_ = v___x_1353_;
goto v___jp_1346_;
}
v___jp_1346_:
{
if (v___y_1347_ == 0)
{
lean_dec(v_val_1345_);
lean_dec_ref(v_exceptionSet_1332_);
return v___x_1343_;
}
else
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_dec_ref_known(v___x_1343_, 1);
v___x_1348_ = lean_unsigned_to_nat(3u);
v___x_1349_ = l_Lean_Expr_getRevArg_x21(v_val_1345_, v___x_1348_);
v___x_1350_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(v_kind_1331_, v_exceptionSet_1332_, v___x_1349_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_a_1351_);
lean_dec_ref_known(v___x_1350_, 1);
if (lean_obj_tag(v_a_1351_) == 0)
{
v___y_1340_ = v_val_1345_;
goto v___jp_1339_;
}
else
{
lean_object* v_val_1352_; 
lean_dec(v_val_1345_);
v_val_1352_ = lean_ctor_get(v_a_1351_, 0);
lean_inc(v_val_1352_);
lean_dec_ref_known(v_a_1351_, 1);
v___y_1340_ = v_val_1352_;
goto v___jp_1339_;
}
}
else
{
lean_dec(v_val_1345_);
return v___x_1350_;
}
}
}
}
else
{
lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1362_; 
lean_dec(v_a_1344_);
lean_dec_ref(v_exceptionSet_1332_);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1362_ == 0)
{
lean_object* v_unused_1363_; 
v_unused_1363_ = lean_ctor_get(v___x_1343_, 0);
lean_dec(v_unused_1363_);
v___x_1356_ = v___x_1343_;
v_isShared_1357_ = v_isSharedCheck_1362_;
goto v_resetjp_1355_;
}
else
{
lean_dec(v___x_1343_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1362_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1358_; lean_object* v___x_1360_; 
v___x_1358_ = lean_box(0);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 0, v___x_1358_);
v___x_1360_ = v___x_1356_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
else
{
lean_dec_ref(v_exceptionSet_1332_);
return v___x_1343_;
}
v___jp_1339_:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1341_, 0, v___y_1340_);
v___x_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
return v___x_1342_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go___boxed(lean_object* v_kind_1364_, lean_object* v_exceptionSet_1365_, lean_object* v_e_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_){
_start:
{
uint8_t v_kind_boxed_1372_; lean_object* v_res_1373_; 
v_kind_boxed_1372_ = lean_unbox(v_kind_1364_);
v_res_1373_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(v_kind_boxed_1372_, v_exceptionSet_1365_, v_e_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(lean_object* v_e_1374_, lean_object* v___y_1375_){
_start:
{
uint8_t v___x_1377_; 
v___x_1377_ = l_Lean_Expr_hasMVar(v_e_1374_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; 
v___x_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1378_, 0, v_e_1374_);
return v___x_1378_;
}
else
{
lean_object* v___x_1379_; lean_object* v_mctx_1380_; lean_object* v___x_1381_; lean_object* v_fst_1382_; lean_object* v_snd_1383_; lean_object* v___x_1384_; lean_object* v_cache_1385_; lean_object* v_zetaDeltaFVarIds_1386_; lean_object* v_postponed_1387_; lean_object* v_diag_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1397_; 
v___x_1379_ = lean_st_ref_get(v___y_1375_);
v_mctx_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc_ref(v_mctx_1380_);
lean_dec(v___x_1379_);
v___x_1381_ = l_Lean_instantiateMVarsCore(v_mctx_1380_, v_e_1374_);
v_fst_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_fst_1382_);
v_snd_1383_ = lean_ctor_get(v___x_1381_, 1);
lean_inc(v_snd_1383_);
lean_dec_ref(v___x_1381_);
v___x_1384_ = lean_st_ref_take(v___y_1375_);
v_cache_1385_ = lean_ctor_get(v___x_1384_, 1);
v_zetaDeltaFVarIds_1386_ = lean_ctor_get(v___x_1384_, 2);
v_postponed_1387_ = lean_ctor_get(v___x_1384_, 3);
v_diag_1388_ = lean_ctor_get(v___x_1384_, 4);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1397_ == 0)
{
lean_object* v_unused_1398_; 
v_unused_1398_ = lean_ctor_get(v___x_1384_, 0);
lean_dec(v_unused_1398_);
v___x_1390_ = v___x_1384_;
v_isShared_1391_ = v_isSharedCheck_1397_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_diag_1388_);
lean_inc(v_postponed_1387_);
lean_inc(v_zetaDeltaFVarIds_1386_);
lean_inc(v_cache_1385_);
lean_dec(v___x_1384_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1397_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 0, v_snd_1383_);
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_snd_1383_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_cache_1385_);
lean_ctor_set(v_reuseFailAlloc_1396_, 2, v_zetaDeltaFVarIds_1386_);
lean_ctor_set(v_reuseFailAlloc_1396_, 3, v_postponed_1387_);
lean_ctor_set(v_reuseFailAlloc_1396_, 4, v_diag_1388_);
v___x_1393_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = lean_st_ref_put(v___y_1375_, v___x_1393_);
v___x_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1395_, 0, v_fst_1382_);
return v___x_1395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg___boxed(lean_object* v_e_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_1399_, v___y_1400_);
lean_dec(v___y_1400_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0(lean_object* v_e_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_1403_, v___y_1405_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___boxed(lean_object* v_e_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0(v_e_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f(lean_object* v_e_1417_, uint8_t v_kind_1418_, lean_object* v_exceptionSet_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_){
_start:
{
lean_object* v___x_1425_; lean_object* v_a_1426_; lean_object* v___x_1427_; 
v___x_1425_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_1417_, v_a_1421_);
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1426_);
lean_dec_ref(v___x_1425_);
v___x_1427_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(v_kind_1418_, v_exceptionSet_1419_, v_a_1426_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f___boxed(lean_object* v_e_1428_, lean_object* v_kind_1429_, lean_object* v_exceptionSet_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_){
_start:
{
uint8_t v_kind_boxed_1436_; lean_object* v_res_1437_; 
v_kind_boxed_1436_ = lean_unbox(v_kind_1429_);
v_res_1437_ = l_Lean_Meta_findSplit_x3f(v_e_1428_, v_kind_boxed_1436_, v_exceptionSet_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
return v_res_1437_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0(void){
_start:
{
lean_object* v_cellCount_1438_; lean_object* v___x_1439_; 
v_cellCount_1438_ = lean_unsigned_to_nat(16u);
v___x_1439_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1438_);
return v___x_1439_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1(void){
_start:
{
lean_object* v_cellCount_1440_; lean_object* v___x_1441_; 
v_cellCount_1440_ = lean_unsigned_to_nat(16u);
v___x_1441_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1440_);
return v___x_1441_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__2(void){
_start:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1442_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1);
v___x_1443_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0);
v___x_1444_ = lean_unsigned_to_nat(0u);
v___x_1445_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
lean_ctor_set(v___x_1445_, 1, v___x_1443_);
lean_ctor_set(v___x_1445_, 2, v___x_1442_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(lean_object* v_e_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
uint8_t v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1452_ = 0;
v___x_1453_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__2, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__2);
v___x_1454_ = l_Lean_Meta_findSplit_x3f(v_e_1446_, v___x_1452_, v___x_1453_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1479_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1457_ = v___x_1454_;
v_isShared_1458_ = v_isSharedCheck_1479_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1479_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
if (lean_obj_tag(v_a_1455_) == 1)
{
lean_object* v_val_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1474_; 
v_val_1459_ = lean_ctor_get(v_a_1455_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_a_1455_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1461_ = v_a_1455_;
v_isShared_1462_ = v_isSharedCheck_1474_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_val_1459_);
lean_dec(v_a_1455_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1474_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1469_; 
v___x_1463_ = lean_unsigned_to_nat(3u);
v___x_1464_ = l_Lean_Expr_getRevArg_x21(v_val_1459_, v___x_1463_);
v___x_1465_ = lean_unsigned_to_nat(2u);
v___x_1466_ = l_Lean_Expr_getRevArg_x21(v_val_1459_, v___x_1465_);
lean_dec(v_val_1459_);
v___x_1467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1464_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 0, v___x_1467_);
v___x_1469_ = v___x_1461_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1467_);
v___x_1469_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
lean_object* v___x_1471_; 
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 0, v___x_1469_);
v___x_1471_ = v___x_1457_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1469_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
else
{
lean_object* v___x_1475_; lean_object* v___x_1477_; 
lean_dec(v_a_1455_);
v___x_1475_ = lean_box(0);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 0, v___x_1475_);
v___x_1477_ = v___x_1457_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1475_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
v_a_1480_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1454_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1454_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___boxed(lean_object* v_e_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(v_e_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_);
lean_dec(v_a_1492_);
lean_dec_ref(v_a_1491_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(lean_object* v_name_1495_, lean_object* v_decl_1496_, lean_object* v_ref_1497_){
_start:
{
lean_object* v_defValue_1499_; lean_object* v_descr_1500_; lean_object* v_deprecation_x3f_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v_defValue_1499_ = lean_ctor_get(v_decl_1496_, 0);
v_descr_1500_ = lean_ctor_get(v_decl_1496_, 1);
v_deprecation_x3f_1501_ = lean_ctor_get(v_decl_1496_, 2);
v___x_1502_ = lean_alloc_ctor(1, 0, 1);
v___x_1503_ = lean_unbox(v_defValue_1499_);
lean_ctor_set_uint8(v___x_1502_, 0, v___x_1503_);
lean_inc(v_deprecation_x3f_1501_);
lean_inc_ref(v_descr_1500_);
lean_inc_n(v_name_1495_, 2);
v___x_1504_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1504_, 0, v_name_1495_);
lean_ctor_set(v___x_1504_, 1, v_ref_1497_);
lean_ctor_set(v___x_1504_, 2, v___x_1502_);
lean_ctor_set(v___x_1504_, 3, v_descr_1500_);
lean_ctor_set(v___x_1504_, 4, v_deprecation_x3f_1501_);
v___x_1505_ = lean_register_option(v_name_1495_, v___x_1504_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1513_; 
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1513_ == 0)
{
lean_object* v_unused_1514_; 
v_unused_1514_ = lean_ctor_get(v___x_1505_, 0);
lean_dec(v_unused_1514_);
v___x_1507_ = v___x_1505_;
v_isShared_1508_ = v_isSharedCheck_1513_;
goto v_resetjp_1506_;
}
else
{
lean_dec(v___x_1505_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1513_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1509_; lean_object* v___x_1511_; 
lean_inc(v_defValue_1499_);
v___x_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1509_, 0, v_name_1495_);
lean_ctor_set(v___x_1509_, 1, v_defValue_1499_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v___x_1509_);
v___x_1511_ = v___x_1507_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1509_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
else
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
lean_dec(v_name_1495_);
v_a_1515_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1517_ = v___x_1505_;
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1505_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1520_; 
if (v_isShared_1518_ == 0)
{
v___x_1520_ = v___x_1517_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1515_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1523_, lean_object* v_decl_1524_, lean_object* v_ref_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(v_name_1523_, v_decl_1524_, v_ref_1525_);
lean_dec_ref(v_decl_1524_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1546_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_));
v___x_1547_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_));
v___x_1548_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_));
v___x_1549_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(v___x_1546_, v___x_1547_, v___x_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4____boxed(lean_object* v_a_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_();
return v_res_1551_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1552_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0);
v___x_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0(lean_object* v_00_u03b2_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1);
return v___x_1556_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1557_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0);
v___x_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1(lean_object* v_00_u03b2_1560_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1);
return v___x_1561_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__0(void){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_1562_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__1(void){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0(lean_box(0));
return v___x_1563_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__2(void){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1(lean_box(0));
return v___x_1564_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__3(void){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1565_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__4(void){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__3, &l_Lean_Meta_SplitIf_getSimpContext___closed__3_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__3);
v___x_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1566_);
return v___x_1567_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__5(void){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v_s_1572_; 
v___x_1568_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__4, &l_Lean_Meta_SplitIf_getSimpContext___closed__4_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__4);
v___x_1569_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__2, &l_Lean_Meta_SplitIf_getSimpContext___closed__2_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__2);
v___x_1570_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__1, &l_Lean_Meta_SplitIf_getSimpContext___closed__1_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__1);
v___x_1571_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__0, &l_Lean_Meta_SplitIf_getSimpContext___closed__0_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__0);
v_s_1572_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_s_1572_, 0, v___x_1571_);
lean_ctor_set(v_s_1572_, 1, v___x_1571_);
lean_ctor_set(v_s_1572_, 2, v___x_1570_);
lean_ctor_set(v_s_1572_, 3, v___x_1569_);
lean_ctor_set(v_s_1572_, 4, v___x_1570_);
lean_ctor_set(v_s_1572_, 5, v___x_1568_);
return v_s_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_getSimpContext(lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_){
_start:
{
lean_object* v_s_1590_; lean_object* v___x_1591_; uint8_t v___x_1592_; uint8_t v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v_s_1590_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__5, &l_Lean_Meta_SplitIf_getSimpContext___closed__5_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__5);
v___x_1591_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__7));
v___x_1592_ = 1;
v___x_1593_ = 0;
v___x_1594_ = lean_unsigned_to_nat(1000u);
v___x_1595_ = l_Lean_Meta_SimpTheorems_addConst(v_s_1590_, v___x_1591_, v___x_1592_, v___x_1593_, v___x_1594_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1596_);
lean_dec_ref_known(v___x_1595_, 1);
v___x_1597_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__9));
v___x_1598_ = l_Lean_Meta_SimpTheorems_addConst(v_a_1596_, v___x_1597_, v___x_1592_, v___x_1593_, v___x_1594_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1598_, 1);
v___x_1600_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__11));
v___x_1601_ = l_Lean_Meta_SimpTheorems_addConst(v_a_1599_, v___x_1600_, v___x_1592_, v___x_1593_, v___x_1594_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1602_);
lean_dec_ref_known(v___x_1601_, 1);
v___x_1603_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__13));
v___x_1604_ = l_Lean_Meta_SimpTheorems_addConst(v_a_1602_, v___x_1603_, v___x_1592_, v___x_1593_, v___x_1594_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; lean_object* v___x_1606_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1605_);
lean_dec_ref_known(v___x_1604_, 1);
v___x_1606_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_1588_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1607_; lean_object* v___x_1608_; lean_object* v_maxSteps_1609_; lean_object* v_maxDischargeDepth_1610_; uint8_t v_contextual_1611_; uint8_t v_memoize_1612_; uint8_t v_singlePass_1613_; uint8_t v_zeta_1614_; uint8_t v_beta_1615_; uint8_t v_eta_1616_; uint8_t v_etaStruct_1617_; uint8_t v_iota_1618_; uint8_t v_proj_1619_; uint8_t v_decide_1620_; uint8_t v_arith_1621_; uint8_t v_autoUnfold_1622_; uint8_t v_failIfUnchanged_1623_; uint8_t v_ground_1624_; uint8_t v_unfoldPartialApp_1625_; uint8_t v_zetaDelta_1626_; uint8_t v_index_1627_; uint8_t v_implicitDefEqProofs_1628_; uint8_t v_zetaUnused_1629_; uint8_t v_catchRuntime_1630_; uint8_t v_zetaHave_1631_; uint8_t v_congrConsts_1632_; uint8_t v_bitVecOfNat_1633_; uint8_t v_warnExponents_1634_; uint8_t v_suggestions_1635_; lean_object* v_maxSuggestions_1636_; uint8_t v_locals_1637_; uint8_t v_instances_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_a_1607_);
lean_dec_ref_known(v___x_1606_, 1);
v___x_1608_ = l_Lean_Meta_Simp_neutralConfig;
v_maxSteps_1609_ = lean_ctor_get(v___x_1608_, 0);
v_maxDischargeDepth_1610_ = lean_ctor_get(v___x_1608_, 1);
v_contextual_1611_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*3);
v_memoize_1612_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*3 + 1);
v_singlePass_1613_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*3 + 2);
v_zeta_1614_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*3 + 3);
v_beta_1615_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*3 + 4);
v_eta_1616_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*3 + 5);
v_etaStruct_1617_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*3 + 6);
v_iota_1618_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*3 + 7);
v_proj_1619_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*3 + 8);
v_decide_1620_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*3 + 9);
v_arith_1621_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*3 + 10);
v_autoUnfold_1622_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*3 + 11);
v_failIfUnchanged_1623_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*3 + 13);
v_ground_1624_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_1625_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*3 + 15);
v_zetaDelta_1626_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*3 + 16);
v_index_1627_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_1628_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*3 + 18);
v_zetaUnused_1629_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*3 + 19);
v_catchRuntime_1630_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*3 + 20);
v_zetaHave_1631_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*3 + 21);
v_congrConsts_1632_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*3 + 23);
v_bitVecOfNat_1633_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*3 + 24);
v_warnExponents_1634_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*3 + 25);
v_suggestions_1635_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*3 + 26);
v_maxSuggestions_1636_ = lean_ctor_get(v___x_1608_, 2);
v_locals_1637_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*3 + 27);
v_instances_1638_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*3 + 28);
lean_inc(v_maxSuggestions_1636_);
lean_inc(v_maxDischargeDepth_1610_);
lean_inc(v_maxSteps_1609_);
v___x_1639_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1639_, 0, v_maxSteps_1609_);
lean_ctor_set(v___x_1639_, 1, v_maxDischargeDepth_1610_);
lean_ctor_set(v___x_1639_, 2, v_maxSuggestions_1636_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3, v_contextual_1611_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 1, v_memoize_1612_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 2, v_singlePass_1613_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 3, v_zeta_1614_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 4, v_beta_1615_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 5, v_eta_1616_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 6, v_etaStruct_1617_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 7, v_iota_1618_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 8, v_proj_1619_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 9, v_decide_1620_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 10, v_arith_1621_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 11, v_autoUnfold_1622_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 12, v___x_1593_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 13, v_failIfUnchanged_1623_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 14, v_ground_1624_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 15, v_unfoldPartialApp_1625_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 16, v_zetaDelta_1626_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 17, v_index_1627_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_1628_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 19, v_zetaUnused_1629_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 20, v_catchRuntime_1630_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 21, v_zetaHave_1631_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 22, v___x_1592_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 23, v_congrConsts_1632_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 24, v_bitVecOfNat_1633_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 25, v_warnExponents_1634_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 26, v_suggestions_1635_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 27, v_locals_1637_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 28, v_instances_1638_);
v___x_1640_ = lean_unsigned_to_nat(1u);
v___x_1641_ = lean_mk_empty_array_with_capacity(v___x_1640_);
v___x_1642_ = lean_array_push(v___x_1641_, v_a_1605_);
v___x_1643_ = l_Lean_Options_empty;
v___x_1644_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1639_, v___x_1642_, v_a_1607_, v___x_1643_, v_a_1585_, v_a_1587_, v_a_1588_);
return v___x_1644_;
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
lean_dec(v_a_1605_);
v_a_1645_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1606_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1606_);
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
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
v_a_1653_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1604_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1604_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
v_a_1661_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1601_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1601_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
v_a_1669_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1598_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1598_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
v_a_1677_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v___x_1595_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1595_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_getSimpContext___boxed(lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_);
lean_dec(v_a_1688_);
lean_dec_ref(v_a_1687_);
lean_dec(v_a_1686_);
lean_dec_ref(v_a_1685_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_1695_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1699_; lean_object* v_maxSteps_1700_; lean_object* v_maxDischargeDepth_1701_; uint8_t v_contextual_1702_; uint8_t v_memoize_1703_; uint8_t v_singlePass_1704_; uint8_t v_zeta_1705_; uint8_t v_beta_1706_; uint8_t v_eta_1707_; uint8_t v_etaStruct_1708_; uint8_t v_iota_1709_; uint8_t v_proj_1710_; uint8_t v_decide_1711_; uint8_t v_arith_1712_; uint8_t v_autoUnfold_1713_; uint8_t v_failIfUnchanged_1714_; uint8_t v_ground_1715_; uint8_t v_unfoldPartialApp_1716_; uint8_t v_zetaDelta_1717_; uint8_t v_index_1718_; uint8_t v_implicitDefEqProofs_1719_; uint8_t v_zetaUnused_1720_; uint8_t v_catchRuntime_1721_; uint8_t v_zetaHave_1722_; uint8_t v_congrConsts_1723_; uint8_t v_bitVecOfNat_1724_; uint8_t v_warnExponents_1725_; uint8_t v_suggestions_1726_; lean_object* v_maxSuggestions_1727_; uint8_t v_locals_1728_; uint8_t v_instances_1729_; uint8_t v___x_1730_; uint8_t v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_a_1698_);
lean_dec_ref_known(v___x_1697_, 1);
v___x_1699_ = l_Lean_Meta_Simp_neutralConfig;
v_maxSteps_1700_ = lean_ctor_get(v___x_1699_, 0);
v_maxDischargeDepth_1701_ = lean_ctor_get(v___x_1699_, 1);
v_contextual_1702_ = lean_ctor_get_uint8(v___x_1699_, sizeof(void*)*3);
v_memoize_1703_ = lean_ctor_get_uint8(v___x_1699_, sizeof(void*)*3 + 1);
v_singlePass_1704_ = lean_ctor_get_uint8(v___x_1699_, sizeof(void*)*3 + 2);
v_zeta_1705_ = lean_ctor_get_uint8(v___x_1699_, sizeof(void*)*3 + 3);
v_beta_1706_ = lean_ctor_get_uint8(v___x_1699_, sizeof(void*)*3 + 4);
v_eta_1707_ = lean_ctor_get_uint8(v___x_1699_, sizeof(void*)*3 + 5);
v_etaStruct_1708_ = lean_ctor_get_uint8(v___x_1699_, sizeof(void*)*3 + 6);
v_iota_1709_ = lean_ctor_get_uint8(v___x_1699_, sizeof(void*)*3 + 7);
v_proj_1710_ = lean_ctor_get_uint8(v___x_1699_, sizeof(void*)*3 + 8);
v_decide_1711_ = lean_ctor_get_uint8(v___x_1699_, sizeof(void*)*3 + 9);
v_arith_1712_ = lean_ctor_get_uint8(v___x_1699_, sizeof(void*)*3 + 10);
v_autoUnfold_1713_ = lean_ctor_get_uint8(v___x_1699_, sizeof(void*)*3 + 11);
v_failIfUnchanged_1714_ = lean_ctor_get_uint8(v___x_1699_, sizeof(void*)*3 + 13);
v_ground_1715_ = lean_ctor_get_uint8(v___x_1699_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_1716_ = lean_ctor_get_uint8(v___x_1699_, sizeof(void*)*3 + 15);
v_zetaDelta_1717_ = lean_ctor_get_uint8(v___x_1699_, sizeof(void*)*3 + 16);
v_index_1718_ = lean_ctor_get_uint8(v___x_1699_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_1719_ = lean_ctor_get_uint8(v___x_1699_, sizeof(void*)*3 + 18);
v_zetaUnused_1720_ = lean_ctor_get_uint8(v___x_1699_, sizeof(void*)*3 + 19);
v_catchRuntime_1721_ = lean_ctor_get_uint8(v___x_1699_, sizeof(void*)*3 + 20);
v_zetaHave_1722_ = lean_ctor_get_uint8(v___x_1699_, sizeof(void*)*3 + 21);
v_congrConsts_1723_ = lean_ctor_get_uint8(v___x_1699_, sizeof(void*)*3 + 23);
v_bitVecOfNat_1724_ = lean_ctor_get_uint8(v___x_1699_, sizeof(void*)*3 + 24);
v_warnExponents_1725_ = lean_ctor_get_uint8(v___x_1699_, sizeof(void*)*3 + 25);
v_suggestions_1726_ = lean_ctor_get_uint8(v___x_1699_, sizeof(void*)*3 + 26);
v_maxSuggestions_1727_ = lean_ctor_get(v___x_1699_, 2);
v_locals_1728_ = lean_ctor_get_uint8(v___x_1699_, sizeof(void*)*3 + 27);
v_instances_1729_ = lean_ctor_get_uint8(v___x_1699_, sizeof(void*)*3 + 28);
v___x_1730_ = 0;
v___x_1731_ = 1;
lean_inc(v_maxSuggestions_1727_);
lean_inc(v_maxDischargeDepth_1701_);
lean_inc(v_maxSteps_1700_);
v___x_1732_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1732_, 0, v_maxSteps_1700_);
lean_ctor_set(v___x_1732_, 1, v_maxDischargeDepth_1701_);
lean_ctor_set(v___x_1732_, 2, v_maxSuggestions_1727_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3, v_contextual_1702_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 1, v_memoize_1703_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 2, v_singlePass_1704_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 3, v_zeta_1705_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 4, v_beta_1706_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 5, v_eta_1707_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 6, v_etaStruct_1708_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 7, v_iota_1709_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 8, v_proj_1710_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 9, v_decide_1711_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 10, v_arith_1712_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 11, v_autoUnfold_1713_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 12, v___x_1730_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 13, v_failIfUnchanged_1714_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 14, v_ground_1715_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 15, v_unfoldPartialApp_1716_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 16, v_zetaDelta_1717_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 17, v_index_1718_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_1719_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 19, v_zetaUnused_1720_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 20, v_catchRuntime_1721_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 21, v_zetaHave_1722_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 22, v___x_1731_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 23, v_congrConsts_1723_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 24, v_bitVecOfNat_1724_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 25, v_warnExponents_1725_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 26, v_suggestions_1726_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 27, v_locals_1728_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 28, v_instances_1729_);
v___x_1733_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg___closed__0));
v___x_1734_ = l_Lean_Options_empty;
v___x_1735_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1732_, v___x_1733_, v_a_1698_, v___x_1734_, v_a_1693_, v_a_1694_, v_a_1695_);
return v___x_1735_;
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
v_a_1736_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1697_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1697_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg___boxed(lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_1744_, v_a_1745_, v_a_1746_);
lean_dec(v_a_1746_);
lean_dec_ref(v_a_1745_);
lean_dec_ref(v_a_1744_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27(lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_1749_, v_a_1751_, v_a_1752_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___boxed(lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27(v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_);
lean_dec(v_a_1758_);
lean_dec_ref(v_a_1757_);
lean_dec(v_a_1756_);
lean_dec_ref(v_a_1755_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(lean_object* v_e_1761_, lean_object* v___y_1762_){
_start:
{
uint8_t v___x_1764_; 
v___x_1764_ = l_Lean_Expr_hasMVar(v_e_1761_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; 
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v_e_1761_);
return v___x_1765_;
}
else
{
lean_object* v___x_1766_; lean_object* v_mctx_1767_; lean_object* v___x_1768_; lean_object* v_fst_1769_; lean_object* v_snd_1770_; lean_object* v___x_1771_; lean_object* v_cache_1772_; lean_object* v_zetaDeltaFVarIds_1773_; lean_object* v_postponed_1774_; lean_object* v_diag_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1784_; 
v___x_1766_ = lean_st_ref_get(v___y_1762_);
v_mctx_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc_ref(v_mctx_1767_);
lean_dec(v___x_1766_);
v___x_1768_ = l_Lean_instantiateMVarsCore(v_mctx_1767_, v_e_1761_);
v_fst_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_fst_1769_);
v_snd_1770_ = lean_ctor_get(v___x_1768_, 1);
lean_inc(v_snd_1770_);
lean_dec_ref(v___x_1768_);
v___x_1771_ = lean_st_ref_take(v___y_1762_);
v_cache_1772_ = lean_ctor_get(v___x_1771_, 1);
v_zetaDeltaFVarIds_1773_ = lean_ctor_get(v___x_1771_, 2);
v_postponed_1774_ = lean_ctor_get(v___x_1771_, 3);
v_diag_1775_ = lean_ctor_get(v___x_1771_, 4);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1784_ == 0)
{
lean_object* v_unused_1785_; 
v_unused_1785_ = lean_ctor_get(v___x_1771_, 0);
lean_dec(v_unused_1785_);
v___x_1777_ = v___x_1771_;
v_isShared_1778_ = v_isSharedCheck_1784_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_diag_1775_);
lean_inc(v_postponed_1774_);
lean_inc(v_zetaDeltaFVarIds_1773_);
lean_inc(v_cache_1772_);
lean_dec(v___x_1771_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1784_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1780_; 
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 0, v_snd_1770_);
v___x_1780_ = v___x_1777_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_snd_1770_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v_cache_1772_);
lean_ctor_set(v_reuseFailAlloc_1783_, 2, v_zetaDeltaFVarIds_1773_);
lean_ctor_set(v_reuseFailAlloc_1783_, 3, v_postponed_1774_);
lean_ctor_set(v_reuseFailAlloc_1783_, 4, v_diag_1775_);
v___x_1780_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = lean_st_ref_put(v___y_1762_, v___x_1780_);
v___x_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1782_, 0, v_fst_1769_);
return v___x_1782_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg___boxed(lean_object* v_e_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_e_1786_, v___y_1787_);
lean_dec(v___y_1787_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0(lean_object* v_e_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_e_1790_, v___y_1795_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___boxed(lean_object* v_e_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0(v_e_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
return v_res_1809_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1816_ = lean_box(0);
v___x_1817_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__3));
v___x_1818_ = l_Lean_mkConst(v___x_1817_, v___x_1816_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(lean_object* v_a_1819_, lean_object* v_numIndices_1820_, lean_object* v_as_1821_, lean_object* v_i_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v_zero_1828_; uint8_t v_isZero_1829_; 
v_zero_1828_ = lean_unsigned_to_nat(0u);
v_isZero_1829_ = lean_nat_dec_eq(v_i_1822_, v_zero_1828_);
if (v_isZero_1829_ == 1)
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
lean_dec(v_i_1822_);
lean_dec_ref(v_a_1819_);
v___x_1830_ = lean_box(0);
v___x_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
return v___x_1831_;
}
else
{
lean_object* v_one_1832_; lean_object* v_n_1833_; lean_object* v___x_1834_; 
v_one_1832_ = lean_unsigned_to_nat(1u);
v_n_1833_ = lean_nat_sub(v_i_1822_, v_one_1832_);
lean_dec(v_i_1822_);
v___x_1834_ = lean_array_fget(v_as_1821_, v_n_1833_);
if (lean_obj_tag(v___x_1834_) == 0)
{
v_i_1822_ = v_n_1833_;
goto _start;
}
else
{
lean_object* v_val_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1901_; 
v_val_1836_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1838_ = v___x_1834_;
v_isShared_1839_ = v_isSharedCheck_1901_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_val_1836_);
lean_dec(v___x_1834_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1901_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
uint8_t v___y_1841_; lean_object* v___x_1898_; uint8_t v___x_1899_; 
v___x_1898_ = l_Lean_LocalDecl_index(v_val_1836_);
v___x_1899_ = lean_nat_dec_le(v_numIndices_1820_, v___x_1898_);
lean_dec(v___x_1898_);
if (v___x_1899_ == 0)
{
uint8_t v___x_1900_; 
v___x_1900_ = l_Lean_LocalDecl_isAuxDecl(v_val_1836_);
v___y_1841_ = v___x_1900_;
goto v___jp_1840_;
}
else
{
v___y_1841_ = v___x_1899_;
goto v___jp_1840_;
}
v___jp_1840_:
{
if (v___y_1841_ == 0)
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = l_Lean_LocalDecl_type(v_val_1836_);
lean_inc_ref(v___x_1842_);
lean_inc_ref(v_a_1819_);
v___x_1843_ = l_Lean_Meta_isExprDefEq(v_a_1819_, v___x_1842_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1888_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1846_ = v___x_1843_;
v_isShared_1847_ = v_isSharedCheck_1888_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1843_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1888_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
uint8_t v___x_1848_; 
v___x_1848_ = lean_unbox(v_a_1844_);
lean_dec(v_a_1844_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; uint8_t v___x_1850_; 
lean_del_object(v___x_1846_);
v___x_1849_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__1));
v___x_1850_ = l_Lean_Expr_isAppOfArity(v_a_1819_, v___x_1849_, v_one_1832_);
if (v___x_1850_ == 0)
{
lean_dec_ref(v___x_1842_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
v_i_1822_ = v_n_1833_;
goto _start;
}
else
{
lean_object* v___x_1852_; uint8_t v___x_1853_; 
v___x_1852_ = l_Lean_Expr_appArg_x21(v_a_1819_);
v___x_1853_ = l_Lean_Expr_isAppOfArity(v___x_1852_, v___x_1849_, v_one_1832_);
if (v___x_1853_ == 0)
{
lean_dec_ref(v___x_1852_);
lean_dec_ref(v___x_1842_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
v_i_1822_ = v_n_1833_;
goto _start;
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = l_Lean_Expr_appArg_x21(v___x_1852_);
lean_dec_ref(v___x_1852_);
lean_inc_ref(v___x_1855_);
v___x_1856_ = l_Lean_Meta_isExprDefEq(v___x_1855_, v___x_1842_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1872_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1859_ = v___x_1856_;
v_isShared_1860_ = v_isSharedCheck_1872_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1856_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1872_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
uint8_t v___x_1861_; 
v___x_1861_ = lean_unbox(v_a_1857_);
lean_dec(v_a_1857_);
if (v___x_1861_ == 0)
{
lean_del_object(v___x_1859_);
lean_dec_ref(v___x_1855_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
v_i_1822_ = v_n_1833_;
goto _start;
}
else
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1867_; 
lean_dec(v_n_1833_);
lean_dec_ref(v_a_1819_);
v___x_1863_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4);
v___x_1864_ = l_Lean_LocalDecl_toExpr(v_val_1836_);
v___x_1865_ = l_Lean_mkAppB(v___x_1863_, v___x_1855_, v___x_1864_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v___x_1865_);
v___x_1867_ = v___x_1838_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
lean_object* v___x_1869_; 
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v___x_1867_);
v___x_1869_ = v___x_1859_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
lean_dec_ref(v___x_1855_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_dec(v_n_1833_);
lean_dec_ref(v_a_1819_);
v_a_1873_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1856_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1856_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
}
}
else
{
lean_object* v___x_1881_; lean_object* v___x_1883_; 
lean_dec_ref(v___x_1842_);
lean_dec(v_n_1833_);
lean_dec_ref(v_a_1819_);
v___x_1881_ = l_Lean_LocalDecl_toExpr(v_val_1836_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v___x_1881_);
v___x_1883_ = v___x_1838_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v___x_1881_);
v___x_1883_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1885_; 
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1883_);
v___x_1885_ = v___x_1846_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1883_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
}
else
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
lean_dec_ref(v___x_1842_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_dec(v_n_1833_);
lean_dec_ref(v_a_1819_);
v_a_1889_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1891_ = v___x_1843_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1843_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1889_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
else
{
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
v_i_1822_ = v_n_1833_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_a_1902_, lean_object* v_numIndices_1903_, lean_object* v_as_1904_, lean_object* v_i_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_a_1902_, v_numIndices_1903_, v_as_1904_, v_i_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec_ref(v_as_1904_);
lean_dec(v_numIndices_1903_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(lean_object* v_a_1912_, lean_object* v_numIndices_1913_, lean_object* v_as_1914_, lean_object* v_i_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_zero_1924_; uint8_t v_isZero_1925_; 
v_zero_1924_ = lean_unsigned_to_nat(0u);
v_isZero_1925_ = lean_nat_dec_eq(v_i_1915_, v_zero_1924_);
if (v_isZero_1925_ == 1)
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
lean_dec(v_i_1915_);
lean_dec_ref(v_a_1912_);
v___x_1926_ = lean_box(0);
v___x_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
return v___x_1927_;
}
else
{
lean_object* v_one_1928_; lean_object* v_n_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v_one_1928_ = lean_unsigned_to_nat(1u);
v_n_1929_ = lean_nat_sub(v_i_1915_, v_one_1928_);
lean_dec(v_i_1915_);
v___x_1930_ = lean_array_fget_borrowed(v_as_1914_, v_n_1929_);
lean_inc_ref(v_a_1912_);
v___x_1931_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_a_1912_, v_numIndices_1913_, v___x_1930_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
if (lean_obj_tag(v_a_1932_) == 0)
{
lean_dec_ref_known(v___x_1931_, 1);
v_i_1915_ = v_n_1929_;
goto _start;
}
else
{
lean_dec_ref_known(v_a_1932_, 1);
lean_dec(v_n_1929_);
lean_dec_ref(v_a_1912_);
return v___x_1931_;
}
}
else
{
lean_dec(v_n_1929_);
lean_dec_ref(v_a_1912_);
return v___x_1931_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(lean_object* v_a_1934_, lean_object* v_numIndices_1935_, lean_object* v_x_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
if (lean_obj_tag(v_x_1936_) == 0)
{
lean_object* v_cs_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v_cs_1945_ = lean_ctor_get(v_x_1936_, 0);
v___x_1946_ = lean_array_get_size(v_cs_1945_);
v___x_1947_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_a_1934_, v_numIndices_1935_, v_cs_1945_, v___x_1946_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
return v___x_1947_;
}
else
{
lean_object* v_vs_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v_vs_1948_ = lean_ctor_get(v_x_1936_, 0);
v___x_1949_ = lean_array_get_size(v_vs_1948_);
v___x_1950_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_a_1934_, v_numIndices_1935_, v_vs_1948_, v___x_1949_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
return v___x_1950_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3___boxed(lean_object* v_a_1951_, lean_object* v_numIndices_1952_, lean_object* v_x_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_a_1951_, v_numIndices_1952_, v_x_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v_x_1953_);
lean_dec(v_numIndices_1952_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_a_1963_, lean_object* v_numIndices_1964_, lean_object* v_as_1965_, lean_object* v_i_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_a_1963_, v_numIndices_1964_, v_as_1965_, v_i_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec_ref(v_as_1965_);
lean_dec(v_numIndices_1964_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(lean_object* v_a_1976_, lean_object* v_numIndices_1977_, lean_object* v_t_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v_root_1987_; lean_object* v_tail_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v_root_1987_ = lean_ctor_get(v_t_1978_, 0);
v_tail_1988_ = lean_ctor_get(v_t_1978_, 1);
v___x_1989_ = lean_array_get_size(v_tail_1988_);
lean_inc_ref(v_a_1976_);
v___x_1990_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_a_1976_, v_numIndices_1977_, v_tail_1988_, v___x_1989_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1991_);
if (lean_obj_tag(v_a_1991_) == 0)
{
lean_object* v___x_1992_; 
lean_dec_ref_known(v___x_1990_, 1);
v___x_1992_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_a_1976_, v_numIndices_1977_, v_root_1987_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
return v___x_1992_;
}
else
{
lean_dec_ref_known(v_a_1991_, 1);
lean_dec_ref(v_a_1976_);
return v___x_1990_;
}
}
else
{
lean_dec_ref(v_a_1976_);
return v___x_1990_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1___boxed(lean_object* v_a_1993_, lean_object* v_numIndices_1994_, lean_object* v_t_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(v_a_1993_, v_numIndices_1994_, v_t_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v_t_1995_);
lean_dec(v_numIndices_1994_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(lean_object* v_a_2005_, lean_object* v_numIndices_2006_, lean_object* v_lctx_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
lean_object* v_decls_2016_; lean_object* v___x_2017_; 
v_decls_2016_ = lean_ctor_get(v_lctx_2007_, 1);
v___x_2017_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(v_a_2005_, v_numIndices_2006_, v_decls_2016_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1___boxed(lean_object* v_a_2018_, lean_object* v_numIndices_2019_, lean_object* v_lctx_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(v_a_2018_, v_numIndices_2019_, v_lctx_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec_ref(v_lctx_2020_);
lean_dec(v_numIndices_2019_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(lean_object* v_cls_2030_, lean_object* v_msg_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v_ref_2037_; lean_object* v___x_2038_; lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2083_; 
v_ref_2037_ = lean_ctor_get(v___y_2034_, 5);
v___x_2038_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(v_msg_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2041_ = v___x_2038_;
v_isShared_2042_ = v_isSharedCheck_2083_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2038_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2083_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2043_; lean_object* v_traceState_2044_; lean_object* v_env_2045_; lean_object* v_nextMacroScope_2046_; lean_object* v_ngen_2047_; lean_object* v_auxDeclNGen_2048_; lean_object* v_cache_2049_; lean_object* v_messages_2050_; lean_object* v_infoState_2051_; lean_object* v_snapshotTasks_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2082_; 
v___x_2043_ = lean_st_ref_take(v___y_2035_);
v_traceState_2044_ = lean_ctor_get(v___x_2043_, 4);
v_env_2045_ = lean_ctor_get(v___x_2043_, 0);
v_nextMacroScope_2046_ = lean_ctor_get(v___x_2043_, 1);
v_ngen_2047_ = lean_ctor_get(v___x_2043_, 2);
v_auxDeclNGen_2048_ = lean_ctor_get(v___x_2043_, 3);
v_cache_2049_ = lean_ctor_get(v___x_2043_, 5);
v_messages_2050_ = lean_ctor_get(v___x_2043_, 6);
v_infoState_2051_ = lean_ctor_get(v___x_2043_, 7);
v_snapshotTasks_2052_ = lean_ctor_get(v___x_2043_, 8);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2054_ = v___x_2043_;
v_isShared_2055_ = v_isSharedCheck_2082_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_snapshotTasks_2052_);
lean_inc(v_infoState_2051_);
lean_inc(v_messages_2050_);
lean_inc(v_cache_2049_);
lean_inc(v_traceState_2044_);
lean_inc(v_auxDeclNGen_2048_);
lean_inc(v_ngen_2047_);
lean_inc(v_nextMacroScope_2046_);
lean_inc(v_env_2045_);
lean_dec(v___x_2043_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2082_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
uint64_t v_tid_2056_; lean_object* v_traces_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2081_; 
v_tid_2056_ = lean_ctor_get_uint64(v_traceState_2044_, sizeof(void*)*1);
v_traces_2057_ = lean_ctor_get(v_traceState_2044_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v_traceState_2044_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2059_ = v_traceState_2044_;
v_isShared_2060_ = v_isSharedCheck_2081_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_traces_2057_);
lean_dec(v_traceState_2044_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2081_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2061_; double v___x_2062_; uint8_t v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2071_; 
v___x_2061_ = lean_box(0);
v___x_2062_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0);
v___x_2063_ = 0;
v___x_2064_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__1));
v___x_2065_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2065_, 0, v_cls_2030_);
lean_ctor_set(v___x_2065_, 1, v___x_2061_);
lean_ctor_set(v___x_2065_, 2, v___x_2064_);
lean_ctor_set_float(v___x_2065_, sizeof(void*)*3, v___x_2062_);
lean_ctor_set_float(v___x_2065_, sizeof(void*)*3 + 8, v___x_2062_);
lean_ctor_set_uint8(v___x_2065_, sizeof(void*)*3 + 16, v___x_2063_);
v___x_2066_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__2));
v___x_2067_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2065_);
lean_ctor_set(v___x_2067_, 1, v_a_2039_);
lean_ctor_set(v___x_2067_, 2, v___x_2066_);
lean_inc(v_ref_2037_);
v___x_2068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2068_, 0, v_ref_2037_);
lean_ctor_set(v___x_2068_, 1, v___x_2067_);
v___x_2069_ = l_Lean_PersistentArray_push___redArg(v_traces_2057_, v___x_2068_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v___x_2069_);
v___x_2071_ = v___x_2059_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v___x_2069_);
lean_ctor_set_uint64(v_reuseFailAlloc_2080_, sizeof(void*)*1, v_tid_2056_);
v___x_2071_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
lean_object* v___x_2073_; 
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 4, v___x_2071_);
v___x_2073_ = v___x_2054_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_env_2045_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v_nextMacroScope_2046_);
lean_ctor_set(v_reuseFailAlloc_2079_, 2, v_ngen_2047_);
lean_ctor_set(v_reuseFailAlloc_2079_, 3, v_auxDeclNGen_2048_);
lean_ctor_set(v_reuseFailAlloc_2079_, 4, v___x_2071_);
lean_ctor_set(v_reuseFailAlloc_2079_, 5, v_cache_2049_);
lean_ctor_set(v_reuseFailAlloc_2079_, 6, v_messages_2050_);
lean_ctor_set(v_reuseFailAlloc_2079_, 7, v_infoState_2051_);
lean_ctor_set(v_reuseFailAlloc_2079_, 8, v_snapshotTasks_2052_);
v___x_2073_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2077_; 
v___x_2074_ = lean_st_ref_put(v___y_2035_, v___x_2073_);
v___x_2075_ = lean_box(0);
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 0, v___x_2075_);
v___x_2077_ = v___x_2041_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg___boxed(lean_object* v_cls_2084_, lean_object* v_msg_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v_cls_2084_, v_msg_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
return v_res_2091_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3(void){
_start:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2097_ = lean_box(0);
v___x_2098_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2));
v___x_2099_ = l_Lean_mkConst(v___x_2098_, v___x_2097_);
return v___x_2099_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6(void){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2103_ = lean_box(0);
v___x_2104_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__5));
v___x_2105_ = l_Lean_mkConst(v___x_2104_, v___x_2103_);
return v___x_2105_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10(void){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2112_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9));
v___x_2113_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4));
v___x_2114_ = l_Lean_Name_append(v___x_2113_, v___x_2112_);
return v___x_2114_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12(void){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11));
v___x_2117_ = l_Lean_stringToMessageData(v___x_2116_);
return v___x_2117_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14(void){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13));
v___x_2120_ = l_Lean_stringToMessageData(v___x_2119_);
return v___x_2120_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17(void){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__16));
v___x_2125_ = l_Lean_MessageData_ofFormat(v___x_2124_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(lean_object* v_numIndices_2126_, uint8_t v_useDecide_2127_, lean_object* v_prop_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_){
_start:
{
lean_object* v___x_2137_; lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2268_; 
v___x_2137_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_prop_2128_, v_a_2133_);
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2140_ = v___x_2137_;
v_isShared_2141_ = v_isSharedCheck_2268_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2137_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2268_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___y_2143_; lean_object* v___y_2144_; lean_object* v___y_2145_; lean_object* v___y_2146_; lean_object* v___y_2147_; lean_object* v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v_a_2162_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2193_; lean_object* v___y_2194_; lean_object* v___y_2195_; lean_object* v___y_2196_; lean_object* v_options_2236_; uint8_t v_hasTrace_2237_; 
v_options_2236_ = lean_ctor_get(v_a_2134_, 2);
v_hasTrace_2237_ = lean_ctor_get_uint8(v_options_2236_, sizeof(void*)*1);
if (v_hasTrace_2237_ == 0)
{
v___y_2190_ = v_a_2129_;
v___y_2191_ = v_a_2130_;
v___y_2192_ = v_a_2131_;
v___y_2193_ = v_a_2132_;
v___y_2194_ = v_a_2133_;
v___y_2195_ = v_a_2134_;
v___y_2196_ = v_a_2135_;
goto v___jp_2189_;
}
else
{
lean_object* v_inheritedTraceOptions_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; uint8_t v___x_2241_; 
v_inheritedTraceOptions_2238_ = lean_ctor_get(v_a_2134_, 13);
v___x_2239_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9));
v___x_2240_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10);
v___x_2241_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2238_, v_options_2236_, v___x_2240_);
if (v___x_2241_ == 0)
{
v___y_2190_ = v_a_2129_;
v___y_2191_ = v_a_2130_;
v___y_2192_ = v_a_2131_;
v___y_2193_ = v_a_2132_;
v___y_2194_ = v_a_2133_;
v___y_2195_ = v_a_2134_;
v___y_2196_ = v_a_2135_;
goto v___jp_2189_;
}
else
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___y_2248_; lean_object* v___x_2261_; lean_object* v___x_2262_; uint8_t v___x_2263_; 
v___x_2242_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12);
lean_inc(v_a_2138_);
v___x_2243_ = l_Lean_MessageData_ofExpr(v_a_2138_);
v___x_2244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2242_);
lean_ctor_set(v___x_2244_, 1, v___x_2243_);
v___x_2245_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14);
v___x_2246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2244_);
lean_ctor_set(v___x_2246_, 1, v___x_2245_);
v___x_2261_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__1));
v___x_2262_ = lean_unsigned_to_nat(1u);
v___x_2263_ = l_Lean_Expr_isAppOfArity(v_a_2138_, v___x_2261_, v___x_2262_);
if (v___x_2263_ == 0)
{
goto v___jp_2259_;
}
else
{
lean_object* v___x_2264_; uint8_t v___x_2265_; 
v___x_2264_ = l_Lean_Expr_appArg_x21(v_a_2138_);
v___x_2265_ = l_Lean_Expr_isAppOfArity(v___x_2264_, v___x_2261_, v___x_2262_);
if (v___x_2265_ == 0)
{
lean_dec_ref(v___x_2264_);
goto v___jp_2259_;
}
else
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = l_Lean_Expr_appArg_x21(v___x_2264_);
lean_dec_ref(v___x_2264_);
v___x_2267_ = l_Lean_MessageData_ofExpr(v___x_2266_);
v___y_2248_ = v___x_2267_;
goto v___jp_2247_;
}
}
v___jp_2247_:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2246_);
lean_ctor_set(v___x_2249_, 1, v___y_2248_);
v___x_2250_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v___x_2239_, v___x_2249_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_);
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_dec_ref_known(v___x_2250_, 1);
v___y_2190_ = v_a_2129_;
v___y_2191_ = v_a_2130_;
v___y_2192_ = v_a_2131_;
v___y_2193_ = v_a_2132_;
v___y_2194_ = v_a_2133_;
v___y_2195_ = v_a_2134_;
v___y_2196_ = v_a_2135_;
goto v___jp_2189_;
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
lean_del_object(v___x_2140_);
lean_dec(v_a_2138_);
v_a_2251_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2250_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2250_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
v___jp_2259_:
{
lean_object* v___x_2260_; 
v___x_2260_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17);
v___y_2248_ = v___x_2260_;
goto v___jp_2247_;
}
}
}
v___jp_2142_:
{
lean_object* v_lctx_2150_; lean_object* v___x_2151_; 
v_lctx_2150_ = lean_ctor_get(v___y_2146_, 2);
v___x_2151_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(v_a_2138_, v_numIndices_2126_, v_lctx_2150_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
return v___x_2151_;
}
v___jp_2152_:
{
lean_object* v___x_2163_; uint8_t v___x_2164_; 
v___x_2163_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2));
v___x_2164_ = l_Lean_Expr_isConstOf(v_a_2162_, v___x_2163_);
lean_dec_ref(v_a_2162_);
if (v___x_2164_ == 0)
{
lean_dec_ref(v___y_2161_);
lean_dec_ref(v___y_2157_);
lean_del_object(v___x_2140_);
v___y_2143_ = v___y_2153_;
v___y_2144_ = v___y_2158_;
v___y_2145_ = v___y_2160_;
v___y_2146_ = v___y_2154_;
v___y_2147_ = v___y_2155_;
v___y_2148_ = v___y_2156_;
v___y_2149_ = v___y_2159_;
goto v___jp_2142_;
}
else
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
lean_dec(v_a_2138_);
v___x_2165_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3);
v___x_2166_ = l_Lean_Meta_mkEqRefl(v___x_2165_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2159_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2180_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2169_ = v___x_2166_;
v_isShared_2170_ = v_isSharedCheck_2180_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2166_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2180_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2175_; 
v___x_2171_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6);
v___x_2172_ = l_Lean_Expr_appArg_x21(v___y_2157_);
lean_dec_ref(v___y_2157_);
v___x_2173_ = l_Lean_mkApp3(v___x_2171_, v___y_2161_, v___x_2172_, v_a_2167_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set_tag(v___x_2140_, 1);
lean_ctor_set(v___x_2140_, 0, v___x_2173_);
v___x_2175_ = v___x_2140_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2173_);
v___x_2175_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
lean_object* v___x_2177_; 
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 0, v___x_2175_);
v___x_2177_ = v___x_2169_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2175_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
else
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
lean_dec_ref(v___y_2161_);
lean_dec_ref(v___y_2157_);
lean_del_object(v___x_2140_);
v_a_2181_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2166_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2166_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
}
v___jp_2189_:
{
if (v_useDecide_2127_ == 0)
{
lean_del_object(v___x_2140_);
v___y_2143_ = v___y_2190_;
v___y_2144_ = v___y_2191_;
v___y_2145_ = v___y_2192_;
v___y_2146_ = v___y_2193_;
v___y_2147_ = v___y_2194_;
v___y_2148_ = v___y_2195_;
v___y_2149_ = v___y_2196_;
goto v___jp_2142_;
}
else
{
lean_object* v___x_2197_; lean_object* v_a_2198_; uint8_t v___x_2199_; 
lean_inc(v_a_2138_);
v___x_2197_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_a_2138_, v___y_2194_);
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_a_2198_);
lean_dec_ref(v___x_2197_);
v___x_2199_ = l_Lean_Expr_hasFVar(v_a_2198_);
if (v___x_2199_ == 0)
{
uint8_t v___x_2200_; 
v___x_2200_ = l_Lean_Expr_hasMVar(v_a_2198_);
if (v___x_2200_ == 0)
{
lean_object* v___x_2201_; 
lean_inc(v_a_2198_);
v___x_2201_ = l_Lean_Meta_mkDecide(v_a_2198_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v_keyedConfig_2203_; uint8_t v_trackZetaDelta_2204_; lean_object* v_zetaDeltaSet_2205_; lean_object* v_lctx_2206_; lean_object* v_localInstances_2207_; lean_object* v_defEqCtx_x3f_2208_; lean_object* v_synthPendingDepth_2209_; lean_object* v_customCanUnfoldPredicate_x3f_2210_; uint8_t v_univApprox_2211_; uint8_t v_inTypeClassResolution_2212_; uint8_t v_cacheInferType_2213_; uint8_t v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc_n(v_a_2202_, 2);
lean_dec_ref_known(v___x_2201_, 1);
v_keyedConfig_2203_ = lean_ctor_get(v___y_2193_, 0);
v_trackZetaDelta_2204_ = lean_ctor_get_uint8(v___y_2193_, sizeof(void*)*7);
v_zetaDeltaSet_2205_ = lean_ctor_get(v___y_2193_, 1);
v_lctx_2206_ = lean_ctor_get(v___y_2193_, 2);
v_localInstances_2207_ = lean_ctor_get(v___y_2193_, 3);
v_defEqCtx_x3f_2208_ = lean_ctor_get(v___y_2193_, 4);
v_synthPendingDepth_2209_ = lean_ctor_get(v___y_2193_, 5);
v_customCanUnfoldPredicate_x3f_2210_ = lean_ctor_get(v___y_2193_, 6);
v_univApprox_2211_ = lean_ctor_get_uint8(v___y_2193_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2212_ = lean_ctor_get_uint8(v___y_2193_, sizeof(void*)*7 + 2);
v_cacheInferType_2213_ = lean_ctor_get_uint8(v___y_2193_, sizeof(void*)*7 + 3);
v___x_2214_ = 1;
lean_inc_ref(v_keyedConfig_2203_);
v___x_2215_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2214_, v_keyedConfig_2203_);
lean_inc(v_customCanUnfoldPredicate_x3f_2210_);
lean_inc(v_synthPendingDepth_2209_);
lean_inc(v_defEqCtx_x3f_2208_);
lean_inc_ref(v_localInstances_2207_);
lean_inc_ref(v_lctx_2206_);
lean_inc(v_zetaDeltaSet_2205_);
v___x_2216_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
lean_ctor_set(v___x_2216_, 1, v_zetaDeltaSet_2205_);
lean_ctor_set(v___x_2216_, 2, v_lctx_2206_);
lean_ctor_set(v___x_2216_, 3, v_localInstances_2207_);
lean_ctor_set(v___x_2216_, 4, v_defEqCtx_x3f_2208_);
lean_ctor_set(v___x_2216_, 5, v_synthPendingDepth_2209_);
lean_ctor_set(v___x_2216_, 6, v_customCanUnfoldPredicate_x3f_2210_);
lean_ctor_set_uint8(v___x_2216_, sizeof(void*)*7, v_trackZetaDelta_2204_);
lean_ctor_set_uint8(v___x_2216_, sizeof(void*)*7 + 1, v_univApprox_2211_);
lean_ctor_set_uint8(v___x_2216_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2212_);
lean_ctor_set_uint8(v___x_2216_, sizeof(void*)*7 + 3, v_cacheInferType_2213_);
lean_inc(v___y_2196_);
lean_inc_ref(v___y_2195_);
lean_inc(v___y_2194_);
v___x_2217_ = lean_whnf(v_a_2202_, v___x_2216_, v___y_2194_, v___y_2195_, v___y_2196_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref_known(v___x_2217_, 1);
v___y_2153_ = v___y_2190_;
v___y_2154_ = v___y_2193_;
v___y_2155_ = v___y_2194_;
v___y_2156_ = v___y_2195_;
v___y_2157_ = v_a_2202_;
v___y_2158_ = v___y_2191_;
v___y_2159_ = v___y_2196_;
v___y_2160_ = v___y_2192_;
v___y_2161_ = v_a_2198_;
v_a_2162_ = v_a_2218_;
goto v___jp_2152_;
}
else
{
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2219_; 
v_a_2219_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2219_);
lean_dec_ref_known(v___x_2217_, 1);
v___y_2153_ = v___y_2190_;
v___y_2154_ = v___y_2193_;
v___y_2155_ = v___y_2194_;
v___y_2156_ = v___y_2195_;
v___y_2157_ = v_a_2202_;
v___y_2158_ = v___y_2191_;
v___y_2159_ = v___y_2196_;
v___y_2160_ = v___y_2192_;
v___y_2161_ = v_a_2198_;
v_a_2162_ = v_a_2219_;
goto v___jp_2152_;
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
lean_dec(v_a_2202_);
lean_dec(v_a_2198_);
lean_del_object(v___x_2140_);
lean_dec(v_a_2138_);
v_a_2220_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2217_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2217_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
lean_dec(v_a_2198_);
lean_del_object(v___x_2140_);
lean_dec(v_a_2138_);
v_a_2228_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2201_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2201_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
else
{
lean_dec(v_a_2198_);
lean_del_object(v___x_2140_);
v___y_2143_ = v___y_2190_;
v___y_2144_ = v___y_2191_;
v___y_2145_ = v___y_2192_;
v___y_2146_ = v___y_2193_;
v___y_2147_ = v___y_2194_;
v___y_2148_ = v___y_2195_;
v___y_2149_ = v___y_2196_;
goto v___jp_2142_;
}
}
else
{
lean_dec(v_a_2198_);
lean_del_object(v___x_2140_);
v___y_2143_ = v___y_2190_;
v___y_2144_ = v___y_2191_;
v___y_2145_ = v___y_2192_;
v___y_2146_ = v___y_2193_;
v___y_2147_ = v___y_2194_;
v___y_2148_ = v___y_2195_;
v___y_2149_ = v___y_2196_;
goto v___jp_2142_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___boxed(lean_object* v_numIndices_2269_, lean_object* v_useDecide_2270_, lean_object* v_prop_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_){
_start:
{
uint8_t v_useDecide_boxed_2280_; lean_object* v_res_2281_; 
v_useDecide_boxed_2280_ = lean_unbox(v_useDecide_2270_);
v_res_2281_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2269_, v_useDecide_boxed_2280_, v_prop_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
lean_dec(v_a_2278_);
lean_dec_ref(v_a_2277_);
lean_dec(v_a_2276_);
lean_dec_ref(v_a_2275_);
lean_dec(v_a_2274_);
lean_dec_ref(v_a_2273_);
lean_dec(v_a_2272_);
lean_dec(v_numIndices_2269_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2(lean_object* v_cls_2282_, lean_object* v_msg_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v_cls_2282_, v_msg_2283_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___boxed(lean_object* v_cls_2293_, lean_object* v_msg_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2(v_cls_2293_, v_msg_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2(lean_object* v_a_2304_, lean_object* v_numIndices_2305_, lean_object* v_as_2306_, lean_object* v_i_2307_, lean_object* v_a_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
lean_object* v___x_2317_; 
v___x_2317_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_a_2304_, v_numIndices_2305_, v_as_2306_, v_i_2307_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_a_2318_, lean_object* v_numIndices_2319_, lean_object* v_as_2320_, lean_object* v_i_2321_, lean_object* v_a_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2(v_a_2318_, v_numIndices_2319_, v_as_2320_, v_i_2321_, v_a_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v_as_2320_);
lean_dec(v_numIndices_2319_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5(lean_object* v_a_2332_, lean_object* v_numIndices_2333_, lean_object* v_as_2334_, lean_object* v_i_2335_, lean_object* v_a_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_a_2332_, v_numIndices_2333_, v_as_2334_, v_i_2335_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_a_2346_, lean_object* v_numIndices_2347_, lean_object* v_as_2348_, lean_object* v_i_2349_, lean_object* v_a_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5(v_a_2346_, v_numIndices_2347_, v_as_2348_, v_i_2349_, v_a_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec_ref(v_as_2348_);
lean_dec(v_numIndices_2347_);
return v_res_2359_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3(void){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2365_ = lean_box(0);
v___x_2366_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__2));
v___x_2367_ = l_Lean_mkConst(v___x_2366_, v___x_2365_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27(lean_object* v_numIndices_2371_, uint8_t v_useDecideBool_2372_, lean_object* v_e_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_){
_start:
{
lean_object* v___x_2382_; 
lean_inc_ref(v_e_2373_);
v___x_2382_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2373_, v_a_2378_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2563_; 
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2385_ = v___x_2382_;
v_isShared_2386_ = v_isSharedCheck_2563_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2382_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2563_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2392_; uint8_t v___x_2393_; 
v___x_2392_ = l_Lean_Expr_cleanupAnnotations(v_a_2383_);
v___x_2393_ = l_Lean_Expr_isApp(v___x_2392_);
if (v___x_2393_ == 0)
{
lean_dec_ref(v___x_2392_);
lean_dec_ref(v_e_2373_);
goto v___jp_2387_;
}
else
{
lean_object* v_arg_2394_; lean_object* v___x_2395_; uint8_t v___x_2396_; 
v_arg_2394_ = lean_ctor_get(v___x_2392_, 1);
lean_inc_ref(v_arg_2394_);
v___x_2395_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2392_);
v___x_2396_ = l_Lean_Expr_isApp(v___x_2395_);
if (v___x_2396_ == 0)
{
lean_dec_ref(v___x_2395_);
lean_dec_ref(v_arg_2394_);
lean_dec_ref(v_e_2373_);
goto v___jp_2387_;
}
else
{
lean_object* v_arg_2397_; lean_object* v___x_2398_; uint8_t v___x_2399_; 
v_arg_2397_ = lean_ctor_get(v___x_2395_, 1);
lean_inc_ref(v_arg_2397_);
v___x_2398_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2395_);
v___x_2399_ = l_Lean_Expr_isApp(v___x_2398_);
if (v___x_2399_ == 0)
{
lean_dec_ref(v___x_2398_);
lean_dec_ref(v_arg_2397_);
lean_dec_ref(v_arg_2394_);
lean_dec_ref(v_e_2373_);
goto v___jp_2387_;
}
else
{
lean_object* v_arg_2400_; lean_object* v___x_2401_; uint8_t v___x_2402_; 
v_arg_2400_ = lean_ctor_get(v___x_2398_, 1);
lean_inc_ref(v_arg_2400_);
v___x_2401_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2398_);
v___x_2402_ = l_Lean_Expr_isApp(v___x_2401_);
if (v___x_2402_ == 0)
{
lean_dec_ref(v___x_2401_);
lean_dec_ref(v_arg_2400_);
lean_dec_ref(v_arg_2397_);
lean_dec_ref(v_arg_2394_);
lean_dec_ref(v_e_2373_);
goto v___jp_2387_;
}
else
{
lean_object* v_arg_2403_; lean_object* v___x_2404_; uint8_t v___x_2405_; 
v_arg_2403_ = lean_ctor_get(v___x_2401_, 1);
lean_inc_ref(v_arg_2403_);
v___x_2404_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2401_);
v___x_2405_ = l_Lean_Expr_isApp(v___x_2404_);
if (v___x_2405_ == 0)
{
lean_dec_ref(v___x_2404_);
lean_dec_ref(v_arg_2403_);
lean_dec_ref(v_arg_2400_);
lean_dec_ref(v_arg_2397_);
lean_dec_ref(v_arg_2394_);
lean_dec_ref(v_e_2373_);
goto v___jp_2387_;
}
else
{
lean_object* v_arg_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; uint8_t v___x_2409_; 
v_arg_2406_ = lean_ctor_get(v___x_2404_, 1);
lean_inc_ref(v_arg_2406_);
v___x_2407_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2404_);
v___x_2408_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__2));
v___x_2409_ = l_Lean_Expr_isConstOf(v___x_2407_, v___x_2408_);
if (v___x_2409_ == 0)
{
lean_dec_ref(v___x_2407_);
lean_dec_ref(v_arg_2406_);
lean_dec_ref(v_arg_2403_);
lean_dec_ref(v_arg_2400_);
lean_dec_ref(v_arg_2397_);
lean_dec_ref(v_arg_2394_);
lean_dec_ref(v_e_2373_);
goto v___jp_2387_;
}
else
{
lean_object* v___x_2410_; 
lean_del_object(v___x_2385_);
lean_inc_ref(v_arg_2403_);
v___x_2410_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2371_, v_useDecideBool_2372_, v_arg_2403_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2554_; 
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2413_ = v___x_2410_;
v_isShared_2414_ = v_isSharedCheck_2554_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2410_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2554_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2415_; 
v___x_2415_ = l_Lean_Expr_constLevels_x21(v___x_2407_);
if (lean_obj_tag(v_a_2411_) == 1)
{
lean_object* v_val_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2431_; 
lean_dec_ref(v___x_2407_);
lean_dec_ref(v_e_2373_);
v_val_2416_ = lean_ctor_get(v_a_2411_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v_a_2411_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2418_ = v_a_2411_;
v_isShared_2419_ = v_isSharedCheck_2431_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_val_2416_);
lean_dec(v_a_2411_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2431_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2424_; 
v___x_2420_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__7));
v___x_2421_ = l_Lean_mkConst(v___x_2420_, v___x_2415_);
lean_inc_ref(v_arg_2397_);
v___x_2422_ = l_Lean_mkApp6(v___x_2421_, v_arg_2403_, v_arg_2400_, v_val_2416_, v_arg_2406_, v_arg_2397_, v_arg_2394_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___x_2422_);
v___x_2424_ = v___x_2418_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2422_);
v___x_2424_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2428_; 
v___x_2425_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2425_, 0, v_arg_2397_);
lean_ctor_set(v___x_2425_, 1, v___x_2424_);
lean_ctor_set_uint8(v___x_2425_, sizeof(void*)*2, v___x_2409_);
v___x_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2425_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 0, v___x_2426_);
v___x_2428_ = v___x_2413_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v___x_2426_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
}
else
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
lean_del_object(v___x_2413_);
lean_dec(v_a_2411_);
lean_inc_ref(v_arg_2403_);
v___x_2432_ = l_Lean_mkNot(v_arg_2403_);
v___x_2433_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2371_, v_useDecideBool_2372_, v___x_2432_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2545_; 
v_a_2434_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2436_ = v___x_2433_;
v_isShared_2437_ = v_isSharedCheck_2545_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2433_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2545_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
if (lean_obj_tag(v_a_2434_) == 1)
{
lean_object* v_val_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2453_; 
lean_dec_ref(v___x_2407_);
lean_dec_ref(v_e_2373_);
v_val_2438_ = lean_ctor_get(v_a_2434_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v_a_2434_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2440_ = v_a_2434_;
v_isShared_2441_ = v_isSharedCheck_2453_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_val_2438_);
lean_dec(v_a_2434_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2453_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2446_; 
v___x_2442_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__9));
v___x_2443_ = l_Lean_mkConst(v___x_2442_, v___x_2415_);
lean_inc_ref(v_arg_2394_);
v___x_2444_ = l_Lean_mkApp6(v___x_2443_, v_arg_2403_, v_arg_2400_, v_val_2438_, v_arg_2406_, v_arg_2397_, v_arg_2394_);
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 0, v___x_2444_);
v___x_2446_ = v___x_2440_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2444_);
v___x_2446_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2450_; 
v___x_2447_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2447_, 0, v_arg_2394_);
lean_ctor_set(v___x_2447_, 1, v___x_2446_);
lean_ctor_set_uint8(v___x_2447_, sizeof(void*)*2, v___x_2409_);
v___x_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 0, v___x_2448_);
v___x_2450_ = v___x_2436_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v___x_2448_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
}
else
{
lean_object* v___x_2454_; 
lean_del_object(v___x_2436_);
lean_dec(v_a_2434_);
lean_inc(v_a_2380_);
lean_inc_ref(v_a_2379_);
lean_inc(v_a_2378_);
lean_inc_ref(v_a_2377_);
lean_inc(v_a_2376_);
lean_inc_ref(v_a_2375_);
lean_inc(v_a_2374_);
lean_inc_ref(v_arg_2403_);
v___x_2454_ = lean_simp(v_arg_2403_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2536_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2457_ = v___x_2454_;
v_isShared_2458_ = v_isSharedCheck_2536_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2454_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2536_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v_expr_2459_; uint8_t v___x_2460_; 
v_expr_2459_ = lean_ctor_get(v_a_2455_, 0);
v___x_2460_ = lean_expr_eqv(v_expr_2459_, v_arg_2403_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
lean_del_object(v___x_2457_);
v___x_2461_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3);
lean_inc_ref(v_expr_2459_);
v___x_2462_ = l_Lean_Expr_app___override(v___x_2461_, v_expr_2459_);
v___x_2463_ = lean_box(0);
v___x_2464_ = l_Lean_Meta_trySynthInstance(v___x_2462_, v___x_2463_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2513_; 
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2467_ = v___x_2464_;
v_isShared_2468_ = v_isSharedCheck_2513_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2464_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2513_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
if (lean_obj_tag(v_a_2465_) == 1)
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2499_; 
lean_inc_ref(v_expr_2459_);
lean_del_object(v___x_2467_);
lean_dec_ref(v_e_2373_);
v_a_2469_ = lean_ctor_get(v_a_2465_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v_a_2465_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2471_ = v_a_2465_;
v_isShared_2472_ = v_isSharedCheck_2499_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v_a_2465_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2499_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2473_; 
v___x_2473_ = l_Lean_Meta_Simp_Result_getProof(v_a_2455_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2490_; 
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2476_ = v___x_2473_;
v_isShared_2477_ = v_isSharedCheck_2490_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2473_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2490_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2483_; 
v___x_2478_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__5));
v___x_2479_ = l_Lean_mkConst(v___x_2478_, v___x_2415_);
lean_inc_ref(v_arg_2394_);
lean_inc_ref(v_arg_2397_);
lean_inc(v_a_2469_);
lean_inc_ref(v_expr_2459_);
lean_inc_ref(v_arg_2406_);
v___x_2480_ = l_Lean_mkApp8(v___x_2479_, v_arg_2406_, v_arg_2403_, v_expr_2459_, v_arg_2400_, v_a_2469_, v_arg_2397_, v_arg_2394_, v_a_2474_);
v___x_2481_ = l_Lean_mkApp5(v___x_2407_, v_arg_2406_, v_expr_2459_, v_a_2469_, v_arg_2397_, v_arg_2394_);
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 0, v___x_2480_);
v___x_2483_ = v___x_2471_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2480_);
v___x_2483_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2487_; 
v___x_2484_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2484_, 0, v___x_2481_);
lean_ctor_set(v___x_2484_, 1, v___x_2483_);
lean_ctor_set_uint8(v___x_2484_, sizeof(void*)*2, v___x_2409_);
v___x_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2484_);
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 0, v___x_2485_);
v___x_2487_ = v___x_2476_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2485_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
lean_del_object(v___x_2471_);
lean_dec(v_a_2469_);
lean_dec_ref(v_expr_2459_);
lean_dec(v___x_2415_);
lean_dec_ref(v___x_2407_);
lean_dec_ref(v_arg_2406_);
lean_dec_ref(v_arg_2403_);
lean_dec_ref(v_arg_2400_);
lean_dec_ref(v_arg_2397_);
lean_dec_ref(v_arg_2394_);
v_a_2491_ = lean_ctor_get(v___x_2473_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2473_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2473_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
}
else
{
lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2510_; 
lean_dec(v_a_2465_);
lean_dec(v___x_2415_);
lean_dec_ref(v___x_2407_);
lean_dec_ref(v_arg_2406_);
lean_dec_ref(v_arg_2403_);
lean_dec_ref(v_arg_2400_);
lean_dec_ref(v_arg_2397_);
lean_dec_ref(v_arg_2394_);
v_isSharedCheck_2510_ = !lean_is_exclusive(v_a_2455_);
if (v_isSharedCheck_2510_ == 0)
{
lean_object* v_unused_2511_; lean_object* v_unused_2512_; 
v_unused_2511_ = lean_ctor_get(v_a_2455_, 1);
lean_dec(v_unused_2511_);
v_unused_2512_ = lean_ctor_get(v_a_2455_, 0);
lean_dec(v_unused_2512_);
v___x_2501_ = v_a_2455_;
v_isShared_2502_ = v_isSharedCheck_2510_;
goto v_resetjp_2500_;
}
else
{
lean_dec(v_a_2455_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2510_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 1, v___x_2463_);
lean_ctor_set(v___x_2501_, 0, v_e_2373_);
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_e_2373_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v___x_2463_);
v___x_2504_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
lean_object* v___x_2505_; lean_object* v___x_2507_; 
lean_ctor_set_uint8(v___x_2504_, sizeof(void*)*2, v___x_2409_);
v___x_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2504_);
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 0, v___x_2505_);
v___x_2507_ = v___x_2467_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___x_2505_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
return v___x_2507_;
}
}
}
}
}
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
lean_dec(v_a_2455_);
lean_dec(v___x_2415_);
lean_dec_ref(v___x_2407_);
lean_dec_ref(v_arg_2406_);
lean_dec_ref(v_arg_2403_);
lean_dec_ref(v_arg_2400_);
lean_dec_ref(v_arg_2397_);
lean_dec_ref(v_arg_2394_);
lean_dec_ref(v_e_2373_);
v_a_2514_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2464_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2464_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2514_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
else
{
lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2533_; 
lean_dec(v___x_2415_);
lean_dec_ref(v___x_2407_);
lean_dec_ref(v_arg_2406_);
lean_dec_ref(v_arg_2403_);
lean_dec_ref(v_arg_2400_);
lean_dec_ref(v_arg_2397_);
lean_dec_ref(v_arg_2394_);
v_isSharedCheck_2533_ = !lean_is_exclusive(v_a_2455_);
if (v_isSharedCheck_2533_ == 0)
{
lean_object* v_unused_2534_; lean_object* v_unused_2535_; 
v_unused_2534_ = lean_ctor_get(v_a_2455_, 1);
lean_dec(v_unused_2534_);
v_unused_2535_ = lean_ctor_get(v_a_2455_, 0);
lean_dec(v_unused_2535_);
v___x_2523_ = v_a_2455_;
v_isShared_2524_ = v_isSharedCheck_2533_;
goto v_resetjp_2522_;
}
else
{
lean_dec(v_a_2455_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2533_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2525_; lean_object* v___x_2527_; 
v___x_2525_ = lean_box(0);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 1, v___x_2525_);
lean_ctor_set(v___x_2523_, 0, v_e_2373_);
v___x_2527_ = v___x_2523_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_e_2373_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v___x_2525_);
v___x_2527_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
lean_object* v___x_2528_; lean_object* v___x_2530_; 
lean_ctor_set_uint8(v___x_2527_, sizeof(void*)*2, v___x_2409_);
v___x_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2527_);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v___x_2528_);
v___x_2530_ = v___x_2457_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2528_);
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
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
lean_dec(v___x_2415_);
lean_dec_ref(v___x_2407_);
lean_dec_ref(v_arg_2406_);
lean_dec_ref(v_arg_2403_);
lean_dec_ref(v_arg_2400_);
lean_dec_ref(v_arg_2397_);
lean_dec_ref(v_arg_2394_);
lean_dec_ref(v_e_2373_);
v_a_2537_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2454_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2454_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
}
}
else
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2553_; 
lean_dec(v___x_2415_);
lean_dec_ref(v___x_2407_);
lean_dec_ref(v_arg_2406_);
lean_dec_ref(v_arg_2403_);
lean_dec_ref(v_arg_2400_);
lean_dec_ref(v_arg_2397_);
lean_dec_ref(v_arg_2394_);
lean_dec_ref(v_e_2373_);
v_a_2546_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2548_ = v___x_2433_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2433_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
if (v_isShared_2549_ == 0)
{
v___x_2551_ = v___x_2548_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_a_2546_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
}
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_dec_ref(v___x_2407_);
lean_dec_ref(v_arg_2406_);
lean_dec_ref(v_arg_2403_);
lean_dec_ref(v_arg_2400_);
lean_dec_ref(v_arg_2397_);
lean_dec_ref(v_arg_2394_);
lean_dec_ref(v_e_2373_);
v_a_2555_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2410_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2410_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
}
}
}
}
}
v___jp_2387_:
{
lean_object* v___x_2388_; lean_object* v___x_2390_; 
v___x_2388_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__0));
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 0, v___x_2388_);
v___x_2390_ = v___x_2385_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2388_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
else
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
lean_dec_ref(v_e_2373_);
v_a_2564_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2566_ = v___x_2382_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2382_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2564_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___boxed(lean_object* v_numIndices_2572_, lean_object* v_useDecideBool_2573_, lean_object* v_e_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_){
_start:
{
uint8_t v_useDecideBool_boxed_2583_; lean_object* v_res_2584_; 
v_useDecideBool_boxed_2583_ = lean_unbox(v_useDecideBool_2573_);
v_res_2584_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27(v_numIndices_2572_, v_useDecideBool_boxed_2583_, v_e_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_);
lean_dec(v_a_2581_);
lean_dec_ref(v_a_2580_);
lean_dec(v_a_2579_);
lean_dec_ref(v_a_2578_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
lean_dec(v_a_2575_);
lean_dec(v_numIndices_2572_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(lean_object* v_e_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_){
_start:
{
if (lean_obj_tag(v_e_2588_) == 6)
{
lean_object* v_binderName_2592_; lean_object* v___x_2593_; 
v_binderName_2592_ = lean_ctor_get(v_e_2588_, 0);
lean_inc(v_binderName_2592_);
v___x_2593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2593_, 0, v_binderName_2592_);
return v___x_2593_;
}
else
{
lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2594_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__1));
v___x_2595_ = l_Lean_Core_mkFreshUserName(v___x_2594_, v_a_2589_, v_a_2590_);
return v___x_2595_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___boxed(lean_object* v_e_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_e_2596_, v_a_2597_, v_a_2598_);
lean_dec(v_a_2598_);
lean_dec_ref(v_a_2597_);
lean_dec_ref(v_e_2596_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName(lean_object* v_e_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_e_2601_, v_a_2604_, v_a_2605_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___boxed(lean_object* v_e_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName(v_e_2608_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_);
lean_dec(v_a_2612_);
lean_dec_ref(v_a_2611_);
lean_dec(v_a_2610_);
lean_dec_ref(v_a_2609_);
lean_dec_ref(v_e_2608_);
return v_res_2614_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3(void){
_start:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2620_ = lean_box(0);
v___x_2621_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__2));
v___x_2622_ = l_Lean_mkConst(v___x_2621_, v___x_2620_);
return v___x_2622_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4(void){
_start:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2623_ = lean_unsigned_to_nat(0u);
v___x_2624_ = l_Lean_mkBVar(v___x_2623_);
return v___x_2624_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7(void){
_start:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2629_ = lean_box(0);
v___x_2630_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__6));
v___x_2631_ = l_Lean_mkConst(v___x_2630_, v___x_2629_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27(lean_object* v_numIndices_2635_, uint8_t v_useDecideBool_2636_, lean_object* v_e_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_){
_start:
{
lean_object* v___x_2646_; 
lean_inc_ref(v_e_2637_);
v___x_2646_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2637_, v_a_2642_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2856_; 
v_a_2647_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2649_ = v___x_2646_;
v_isShared_2650_ = v_isSharedCheck_2856_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2646_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2856_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2656_; uint8_t v___x_2657_; 
v___x_2656_ = l_Lean_Expr_cleanupAnnotations(v_a_2647_);
v___x_2657_ = l_Lean_Expr_isApp(v___x_2656_);
if (v___x_2657_ == 0)
{
lean_dec_ref(v___x_2656_);
lean_dec_ref(v_e_2637_);
goto v___jp_2651_;
}
else
{
lean_object* v_arg_2658_; lean_object* v___x_2659_; uint8_t v___x_2660_; 
v_arg_2658_ = lean_ctor_get(v___x_2656_, 1);
lean_inc_ref(v_arg_2658_);
v___x_2659_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2656_);
v___x_2660_ = l_Lean_Expr_isApp(v___x_2659_);
if (v___x_2660_ == 0)
{
lean_dec_ref(v___x_2659_);
lean_dec_ref(v_arg_2658_);
lean_dec_ref(v_e_2637_);
goto v___jp_2651_;
}
else
{
lean_object* v_arg_2661_; lean_object* v___x_2662_; uint8_t v___x_2663_; 
v_arg_2661_ = lean_ctor_get(v___x_2659_, 1);
lean_inc_ref(v_arg_2661_);
v___x_2662_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2659_);
v___x_2663_ = l_Lean_Expr_isApp(v___x_2662_);
if (v___x_2663_ == 0)
{
lean_dec_ref(v___x_2662_);
lean_dec_ref(v_arg_2661_);
lean_dec_ref(v_arg_2658_);
lean_dec_ref(v_e_2637_);
goto v___jp_2651_;
}
else
{
lean_object* v_arg_2664_; lean_object* v___x_2665_; uint8_t v___x_2666_; 
v_arg_2664_ = lean_ctor_get(v___x_2662_, 1);
lean_inc_ref(v_arg_2664_);
v___x_2665_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2662_);
v___x_2666_ = l_Lean_Expr_isApp(v___x_2665_);
if (v___x_2666_ == 0)
{
lean_dec_ref(v___x_2665_);
lean_dec_ref(v_arg_2664_);
lean_dec_ref(v_arg_2661_);
lean_dec_ref(v_arg_2658_);
lean_dec_ref(v_e_2637_);
goto v___jp_2651_;
}
else
{
lean_object* v_arg_2667_; lean_object* v___x_2668_; uint8_t v___x_2669_; 
v_arg_2667_ = lean_ctor_get(v___x_2665_, 1);
lean_inc_ref(v_arg_2667_);
v___x_2668_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2665_);
v___x_2669_ = l_Lean_Expr_isApp(v___x_2668_);
if (v___x_2669_ == 0)
{
lean_dec_ref(v___x_2668_);
lean_dec_ref(v_arg_2667_);
lean_dec_ref(v_arg_2664_);
lean_dec_ref(v_arg_2661_);
lean_dec_ref(v_arg_2658_);
lean_dec_ref(v_e_2637_);
goto v___jp_2651_;
}
else
{
lean_object* v_arg_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; uint8_t v___x_2673_; 
v_arg_2670_ = lean_ctor_get(v___x_2668_, 1);
lean_inc_ref(v_arg_2670_);
v___x_2671_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2668_);
v___x_2672_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__4));
v___x_2673_ = l_Lean_Expr_isConstOf(v___x_2671_, v___x_2672_);
if (v___x_2673_ == 0)
{
lean_dec_ref(v___x_2671_);
lean_dec_ref(v_arg_2670_);
lean_dec_ref(v_arg_2667_);
lean_dec_ref(v_arg_2664_);
lean_dec_ref(v_arg_2661_);
lean_dec_ref(v_arg_2658_);
lean_dec_ref(v_e_2637_);
goto v___jp_2651_;
}
else
{
lean_object* v___x_2674_; 
lean_del_object(v___x_2649_);
lean_inc_ref(v_arg_2667_);
v___x_2674_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2635_, v_useDecideBool_2636_, v_arg_2667_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2847_; 
v_a_2675_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2677_ = v___x_2674_;
v_isShared_2678_ = v_isSharedCheck_2847_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2674_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2847_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2679_; 
v___x_2679_ = l_Lean_Expr_constLevels_x21(v___x_2671_);
if (lean_obj_tag(v_a_2675_) == 1)
{
lean_object* v_val_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2697_; 
lean_dec_ref(v___x_2671_);
lean_dec_ref(v_e_2637_);
v_val_2680_ = lean_ctor_get(v_a_2675_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v_a_2675_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2682_ = v_a_2675_;
v_isShared_2683_ = v_isSharedCheck_2697_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_val_2680_);
lean_dec(v_a_2675_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2697_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2690_; 
lean_inc(v_val_2680_);
lean_inc_ref(v_arg_2661_);
v___x_2684_ = l_Lean_Expr_app___override(v_arg_2661_, v_val_2680_);
v___x_2685_ = l_Lean_Expr_headBeta(v___x_2684_);
v___x_2686_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__11));
v___x_2687_ = l_Lean_mkConst(v___x_2686_, v___x_2679_);
v___x_2688_ = l_Lean_mkApp6(v___x_2687_, v_arg_2667_, v_arg_2664_, v_val_2680_, v_arg_2670_, v_arg_2661_, v_arg_2658_);
if (v_isShared_2683_ == 0)
{
lean_ctor_set(v___x_2682_, 0, v___x_2688_);
v___x_2690_ = v___x_2682_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2688_);
v___x_2690_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2694_; 
v___x_2691_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2691_, 0, v___x_2685_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
lean_ctor_set_uint8(v___x_2691_, sizeof(void*)*2, v___x_2673_);
v___x_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2691_);
if (v_isShared_2678_ == 0)
{
lean_ctor_set(v___x_2677_, 0, v___x_2692_);
v___x_2694_ = v___x_2677_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2692_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
else
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
lean_del_object(v___x_2677_);
lean_dec(v_a_2675_);
lean_inc_ref(v_arg_2667_);
v___x_2698_ = l_Lean_mkNot(v_arg_2667_);
v___x_2699_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2635_, v_useDecideBool_2636_, v___x_2698_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2838_; 
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2702_ = v___x_2699_;
v_isShared_2703_ = v_isSharedCheck_2838_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2699_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2838_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
if (lean_obj_tag(v_a_2700_) == 1)
{
lean_object* v_val_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2721_; 
lean_dec_ref(v___x_2671_);
lean_dec_ref(v_e_2637_);
v_val_2704_ = lean_ctor_get(v_a_2700_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v_a_2700_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2706_ = v_a_2700_;
v_isShared_2707_ = v_isSharedCheck_2721_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_val_2704_);
lean_dec(v_a_2700_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2721_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2714_; 
lean_inc(v_val_2704_);
lean_inc_ref(v_arg_2658_);
v___x_2708_ = l_Lean_Expr_app___override(v_arg_2658_, v_val_2704_);
v___x_2709_ = l_Lean_Expr_headBeta(v___x_2708_);
v___x_2710_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__13));
v___x_2711_ = l_Lean_mkConst(v___x_2710_, v___x_2679_);
v___x_2712_ = l_Lean_mkApp6(v___x_2711_, v_arg_2667_, v_arg_2664_, v_val_2704_, v_arg_2670_, v_arg_2661_, v_arg_2658_);
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 0, v___x_2712_);
v___x_2714_ = v___x_2706_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v___x_2712_);
v___x_2714_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2718_; 
v___x_2715_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2715_, 0, v___x_2709_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
lean_ctor_set_uint8(v___x_2715_, sizeof(void*)*2, v___x_2673_);
v___x_2716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2715_);
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 0, v___x_2716_);
v___x_2718_ = v___x_2702_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2716_);
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
else
{
lean_object* v___x_2722_; 
lean_del_object(v___x_2702_);
lean_dec(v_a_2700_);
lean_inc(v_a_2644_);
lean_inc_ref(v_a_2643_);
lean_inc(v_a_2642_);
lean_inc_ref(v_a_2641_);
lean_inc(v_a_2640_);
lean_inc_ref(v_a_2639_);
lean_inc(v_a_2638_);
lean_inc_ref(v_arg_2667_);
v___x_2722_ = lean_simp(v_arg_2667_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2829_; 
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2725_ = v___x_2722_;
v_isShared_2726_ = v_isSharedCheck_2829_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2722_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2829_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v_expr_2727_; uint8_t v___x_2728_; 
v_expr_2727_ = lean_ctor_get(v_a_2723_, 0);
v___x_2728_ = lean_expr_eqv(v_expr_2727_, v_arg_2667_);
if (v___x_2728_ == 0)
{
lean_object* v___x_2729_; 
lean_inc_ref(v_expr_2727_);
lean_del_object(v___x_2725_);
v___x_2729_ = l_Lean_Meta_Simp_Result_getProof(v_a_2723_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v_a_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_a_2730_);
lean_dec_ref_known(v___x_2729_, 1);
v___x_2731_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3);
lean_inc_ref(v_expr_2727_);
v___x_2732_ = l_Lean_Expr_app___override(v___x_2731_, v_expr_2727_);
v___x_2733_ = lean_box(0);
v___x_2734_ = l_Lean_Meta_trySynthInstance(v___x_2732_, v___x_2733_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2798_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2737_ = v___x_2734_;
v_isShared_2738_ = v_isSharedCheck_2798_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2734_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2798_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
if (lean_obj_tag(v_a_2735_) == 1)
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2792_; 
lean_del_object(v___x_2737_);
lean_dec_ref(v_e_2637_);
v_a_2739_ = lean_ctor_get(v_a_2735_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v_a_2735_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2741_ = v_a_2735_;
v_isShared_2742_ = v_isSharedCheck_2792_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v_a_2735_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2792_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2743_; 
v___x_2743_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_arg_2661_, v_a_2643_, v_a_2644_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v_a_2744_; lean_object* v___x_2745_; 
v_a_2744_ = lean_ctor_get(v___x_2743_, 0);
lean_inc(v_a_2744_);
lean_dec_ref_known(v___x_2743_, 1);
v___x_2745_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_arg_2658_, v_a_2643_, v_a_2644_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2775_; 
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2748_ = v___x_2745_;
v_isShared_2749_ = v_isSharedCheck_2775_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2745_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2775_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; uint8_t v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2768_; 
v___x_2750_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3);
v___x_2751_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4);
lean_inc_n(v_a_2730_, 2);
lean_inc_ref_n(v_expr_2727_, 5);
lean_inc_ref_n(v_arg_2667_, 2);
v___x_2752_ = l_Lean_mkApp4(v___x_2750_, v_arg_2667_, v_expr_2727_, v_a_2730_, v___x_2751_);
lean_inc_ref(v_arg_2661_);
v___x_2753_ = l_Lean_Expr_app___override(v_arg_2661_, v___x_2752_);
v___x_2754_ = l_Lean_Expr_headBeta(v___x_2753_);
v___x_2755_ = 0;
v___x_2756_ = l_Lean_mkLambda(v_a_2744_, v___x_2755_, v_expr_2727_, v___x_2754_);
v___x_2757_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7);
v___x_2758_ = l_Lean_mkApp4(v___x_2757_, v_arg_2667_, v_expr_2727_, v_a_2730_, v___x_2751_);
lean_inc_ref(v_arg_2658_);
v___x_2759_ = l_Lean_Expr_app___override(v_arg_2658_, v___x_2758_);
v___x_2760_ = l_Lean_Expr_headBeta(v___x_2759_);
v___x_2761_ = l_Lean_mkNot(v_expr_2727_);
v___x_2762_ = l_Lean_mkLambda(v_a_2746_, v___x_2755_, v___x_2761_, v___x_2760_);
lean_inc(v_a_2739_);
lean_inc_ref(v_arg_2670_);
v___x_2763_ = l_Lean_mkApp5(v___x_2671_, v_arg_2670_, v_expr_2727_, v_a_2739_, v___x_2756_, v___x_2762_);
v___x_2764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__9));
v___x_2765_ = l_Lean_mkConst(v___x_2764_, v___x_2679_);
v___x_2766_ = l_Lean_mkApp8(v___x_2765_, v_arg_2670_, v_arg_2667_, v_expr_2727_, v_arg_2664_, v_a_2739_, v_arg_2661_, v_arg_2658_, v_a_2730_);
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 0, v___x_2766_);
v___x_2768_ = v___x_2741_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2766_);
v___x_2768_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2772_; 
v___x_2769_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2769_, 0, v___x_2763_);
lean_ctor_set(v___x_2769_, 1, v___x_2768_);
lean_ctor_set_uint8(v___x_2769_, sizeof(void*)*2, v___x_2673_);
v___x_2770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2769_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 0, v___x_2770_);
v___x_2772_ = v___x_2748_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2770_);
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
else
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2783_; 
lean_dec(v_a_2744_);
lean_del_object(v___x_2741_);
lean_dec(v_a_2739_);
lean_dec(v_a_2730_);
lean_dec_ref(v_expr_2727_);
lean_dec(v___x_2679_);
lean_dec_ref(v___x_2671_);
lean_dec_ref(v_arg_2670_);
lean_dec_ref(v_arg_2667_);
lean_dec_ref(v_arg_2664_);
lean_dec_ref(v_arg_2661_);
lean_dec_ref(v_arg_2658_);
v_a_2776_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2778_ = v___x_2745_;
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2745_);
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
else
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
lean_del_object(v___x_2741_);
lean_dec(v_a_2739_);
lean_dec(v_a_2730_);
lean_dec_ref(v_expr_2727_);
lean_dec(v___x_2679_);
lean_dec_ref(v___x_2671_);
lean_dec_ref(v_arg_2670_);
lean_dec_ref(v_arg_2667_);
lean_dec_ref(v_arg_2664_);
lean_dec_ref(v_arg_2661_);
lean_dec_ref(v_arg_2658_);
v_a_2784_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2743_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2743_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
}
else
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2796_; 
lean_dec(v_a_2735_);
lean_dec(v_a_2730_);
lean_dec_ref(v_expr_2727_);
lean_dec(v___x_2679_);
lean_dec_ref(v___x_2671_);
lean_dec_ref(v_arg_2670_);
lean_dec_ref(v_arg_2667_);
lean_dec_ref(v_arg_2664_);
lean_dec_ref(v_arg_2661_);
lean_dec_ref(v_arg_2658_);
v___x_2793_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2793_, 0, v_e_2637_);
lean_ctor_set(v___x_2793_, 1, v___x_2733_);
lean_ctor_set_uint8(v___x_2793_, sizeof(void*)*2, v___x_2673_);
v___x_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2793_);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 0, v___x_2794_);
v___x_2796_ = v___x_2737_;
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
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
lean_dec(v_a_2730_);
lean_dec_ref(v_expr_2727_);
lean_dec(v___x_2679_);
lean_dec_ref(v___x_2671_);
lean_dec_ref(v_arg_2670_);
lean_dec_ref(v_arg_2667_);
lean_dec_ref(v_arg_2664_);
lean_dec_ref(v_arg_2661_);
lean_dec_ref(v_arg_2658_);
lean_dec_ref(v_e_2637_);
v_a_2799_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2801_ = v___x_2734_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2734_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
else
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2814_; 
lean_dec_ref(v_expr_2727_);
lean_dec(v___x_2679_);
lean_dec_ref(v___x_2671_);
lean_dec_ref(v_arg_2670_);
lean_dec_ref(v_arg_2667_);
lean_dec_ref(v_arg_2664_);
lean_dec_ref(v_arg_2661_);
lean_dec_ref(v_arg_2658_);
lean_dec_ref(v_e_2637_);
v_a_2807_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2809_ = v___x_2729_;
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2729_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2812_; 
if (v_isShared_2810_ == 0)
{
v___x_2812_ = v___x_2809_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
}
else
{
lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2826_; 
lean_dec(v___x_2679_);
lean_dec_ref(v___x_2671_);
lean_dec_ref(v_arg_2670_);
lean_dec_ref(v_arg_2667_);
lean_dec_ref(v_arg_2664_);
lean_dec_ref(v_arg_2661_);
lean_dec_ref(v_arg_2658_);
v_isSharedCheck_2826_ = !lean_is_exclusive(v_a_2723_);
if (v_isSharedCheck_2826_ == 0)
{
lean_object* v_unused_2827_; lean_object* v_unused_2828_; 
v_unused_2827_ = lean_ctor_get(v_a_2723_, 1);
lean_dec(v_unused_2827_);
v_unused_2828_ = lean_ctor_get(v_a_2723_, 0);
lean_dec(v_unused_2828_);
v___x_2816_ = v_a_2723_;
v_isShared_2817_ = v_isSharedCheck_2826_;
goto v_resetjp_2815_;
}
else
{
lean_dec(v_a_2723_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2826_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2818_; lean_object* v___x_2820_; 
v___x_2818_ = lean_box(0);
if (v_isShared_2817_ == 0)
{
lean_ctor_set(v___x_2816_, 1, v___x_2818_);
lean_ctor_set(v___x_2816_, 0, v_e_2637_);
v___x_2820_ = v___x_2816_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_e_2637_);
lean_ctor_set(v_reuseFailAlloc_2825_, 1, v___x_2818_);
v___x_2820_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
lean_object* v___x_2821_; lean_object* v___x_2823_; 
lean_ctor_set_uint8(v___x_2820_, sizeof(void*)*2, v___x_2673_);
v___x_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2820_);
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 0, v___x_2821_);
v___x_2823_ = v___x_2725_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v___x_2821_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
}
}
else
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2837_; 
lean_dec(v___x_2679_);
lean_dec_ref(v___x_2671_);
lean_dec_ref(v_arg_2670_);
lean_dec_ref(v_arg_2667_);
lean_dec_ref(v_arg_2664_);
lean_dec_ref(v_arg_2661_);
lean_dec_ref(v_arg_2658_);
lean_dec_ref(v_e_2637_);
v_a_2830_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2832_ = v___x_2722_;
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2722_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2835_; 
if (v_isShared_2833_ == 0)
{
v___x_2835_ = v___x_2832_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_a_2830_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
}
}
else
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
lean_dec(v___x_2679_);
lean_dec_ref(v___x_2671_);
lean_dec_ref(v_arg_2670_);
lean_dec_ref(v_arg_2667_);
lean_dec_ref(v_arg_2664_);
lean_dec_ref(v_arg_2661_);
lean_dec_ref(v_arg_2658_);
lean_dec_ref(v_e_2637_);
v_a_2839_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2841_ = v___x_2699_;
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2699_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2844_; 
if (v_isShared_2842_ == 0)
{
v___x_2844_ = v___x_2841_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
}
}
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
lean_dec_ref(v___x_2671_);
lean_dec_ref(v_arg_2670_);
lean_dec_ref(v_arg_2667_);
lean_dec_ref(v_arg_2664_);
lean_dec_ref(v_arg_2661_);
lean_dec_ref(v_arg_2658_);
lean_dec_ref(v_e_2637_);
v_a_2848_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2674_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2674_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
}
}
}
}
}
v___jp_2651_:
{
lean_object* v___x_2652_; lean_object* v___x_2654_; 
v___x_2652_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__0));
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 0, v___x_2652_);
v___x_2654_ = v___x_2649_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2652_);
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
else
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
lean_dec_ref(v_e_2637_);
v_a_2857_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2646_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2646_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2857_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___boxed(lean_object* v_numIndices_2865_, lean_object* v_useDecideBool_2866_, lean_object* v_e_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_){
_start:
{
uint8_t v_useDecideBool_boxed_2876_; lean_object* v_res_2877_; 
v_useDecideBool_boxed_2876_ = lean_unbox(v_useDecideBool_2866_);
v_res_2877_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27(v_numIndices_2865_, v_useDecideBool_boxed_2876_, v_e_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
lean_dec(v_a_2874_);
lean_dec_ref(v_a_2873_);
lean_dec(v_a_2872_);
lean_dec_ref(v_a_2871_);
lean_dec(v_a_2870_);
lean_dec_ref(v_a_2869_);
lean_dec(v_a_2868_);
lean_dec(v_numIndices_2865_);
return v_res_2877_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0(void){
_start:
{
lean_object* v___x_2878_; 
v___x_2878_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_2878_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1(void){
_start:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v_s_2881_; 
v___x_2879_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__2, &l_Lean_Meta_SplitIf_getSimpContext___closed__2_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__2);
v___x_2880_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0);
v_s_2881_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_s_2881_, 0, v___x_2880_);
lean_ctor_set(v_s_2881_, 1, v___x_2880_);
lean_ctor_set(v_s_2881_, 2, v___x_2879_);
lean_ctor_set(v_s_2881_, 3, v___x_2879_);
return v_s_2881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(lean_object* v_numIndices_2945_, uint8_t v_useDecide_2946_){
_start:
{
lean_object* v_s_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; uint8_t v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v_s_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v_s_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v_s_2948_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1);
v___x_2949_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__3));
v___x_2950_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__16));
v___x_2951_ = 0;
v___x_2952_ = lean_box(v_useDecide_2946_);
lean_inc(v_numIndices_2945_);
v___x_2953_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___boxed), 11, 2);
lean_closure_set(v___x_2953_, 0, v_numIndices_2945_);
lean_closure_set(v___x_2953_, 1, v___x_2952_);
v___x_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
v_s_2955_ = l_Lean_Meta_Simp_Simprocs_addCore(v_s_2948_, v___x_2949_, v___x_2950_, v___x_2951_, v___x_2954_);
v___x_2956_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__18));
v___x_2957_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__20));
v___x_2958_ = lean_box(v_useDecide_2946_);
v___x_2959_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___boxed), 11, 2);
lean_closure_set(v___x_2959_, 0, v_numIndices_2945_);
lean_closure_set(v___x_2959_, 1, v___x_2958_);
v___x_2960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
v_s_2961_ = l_Lean_Meta_Simp_Simprocs_addCore(v_s_2955_, v___x_2956_, v___x_2957_, v___x_2951_, v___x_2960_);
v___x_2962_ = lean_unsigned_to_nat(1u);
v___x_2963_ = lean_mk_empty_array_with_capacity(v___x_2962_);
v___x_2964_ = lean_array_push(v___x_2963_, v_s_2961_);
v___x_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___boxed(lean_object* v_numIndices_2966_, lean_object* v_useDecide_2967_, lean_object* v_a_2968_){
_start:
{
uint8_t v_useDecide_boxed_2969_; lean_object* v_res_2970_; 
v_useDecide_boxed_2969_ = lean_unbox(v_useDecide_2967_);
v_res_2970_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_numIndices_2966_, v_useDecide_boxed_2969_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs(lean_object* v_numIndices_2971_, uint8_t v_useDecide_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_){
_start:
{
lean_object* v___x_2978_; 
v___x_2978_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_numIndices_2971_, v_useDecide_2972_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___boxed(lean_object* v_numIndices_2979_, lean_object* v_useDecide_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_){
_start:
{
uint8_t v_useDecide_boxed_2986_; lean_object* v_res_2987_; 
v_useDecide_boxed_2986_ = lean_unbox(v_useDecide_2980_);
v_res_2987_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs(v_numIndices_2979_, v_useDecide_boxed_2986_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_);
lean_dec(v_a_2984_);
lean_dec_ref(v_a_2983_);
lean_dec(v_a_2982_);
lean_dec_ref(v_a_2981_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(uint8_t v_useDecide_2988_, lean_object* v_a_2989_){
_start:
{
lean_object* v_lctx_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v_lctx_2991_ = lean_ctor_get(v_a_2989_, 2);
lean_inc_ref(v_lctx_2991_);
v___x_2992_ = lean_local_ctx_num_indices(v_lctx_2991_);
v___x_2993_ = lean_box(v_useDecide_2988_);
v___x_2994_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___boxed), 11, 2);
lean_closure_set(v___x_2994_, 0, v___x_2992_);
lean_closure_set(v___x_2994_, 1, v___x_2993_);
v___x_2995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2994_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg___boxed(lean_object* v_useDecide_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_){
_start:
{
uint8_t v_useDecide_boxed_2999_; lean_object* v_res_3000_; 
v_useDecide_boxed_2999_ = lean_unbox(v_useDecide_2996_);
v_res_3000_ = l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(v_useDecide_boxed_2999_, v_a_2997_);
lean_dec_ref(v_a_2997_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f(uint8_t v_useDecide_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_){
_start:
{
lean_object* v___x_3007_; 
v___x_3007_ = l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(v_useDecide_3001_, v_a_3002_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed(lean_object* v_useDecide_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_){
_start:
{
uint8_t v_useDecide_boxed_3014_; lean_object* v_res_3015_; 
v_useDecide_boxed_3014_ = lean_unbox(v_useDecide_3008_);
v_res_3015_ = l_Lean_Meta_SplitIf_mkDischarge_x3f(v_useDecide_boxed_3014_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_);
lean_dec(v_a_3012_);
lean_dec_ref(v_a_3011_);
lean_dec(v_a_3010_);
lean_dec_ref(v_a_3009_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(lean_object* v_mvarId_3016_, lean_object* v_x_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
lean_object* v___x_3023_; 
v___x_3023_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3016_, v_x_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3031_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3026_ = v___x_3023_;
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3023_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3029_; 
if (v_isShared_3027_ == 0)
{
v___x_3029_ = v___x_3026_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3024_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
v_a_3032_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_3023_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_3023_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_3040_, lean_object* v_x_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_){
_start:
{
lean_object* v_res_3047_; 
v_res_3047_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_3040_, v_x_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
return v_res_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0(lean_object* v_00_u03b1_3048_, lean_object* v_mvarId_3049_, lean_object* v_x_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_){
_start:
{
lean_object* v___x_3056_; 
v___x_3056_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_3049_, v_x_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___boxed(lean_object* v_00_u03b1_3057_, lean_object* v_mvarId_3058_, lean_object* v_x_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0(v_00_u03b1_3057_, v_mvarId_3058_, v_x_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
return v_res_3065_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3067_ = ((lean_object*)(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__0));
v___x_3068_ = l_Lean_stringToMessageData(v___x_3067_);
return v___x_3068_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3070_ = ((lean_object*)(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__2));
v___x_3071_ = l_Lean_stringToMessageData(v___x_3070_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0(lean_object* v_e_3072_, lean_object* v_mvarId_3073_, lean_object* v_hName_x3f_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
lean_object* v___x_3083_; lean_object* v_a_3084_; lean_object* v___x_3085_; 
v___x_3083_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_3072_, v___y_3076_);
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
lean_inc_n(v_a_3084_, 2);
lean_dec_ref(v___x_3083_);
v___x_3085_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(v_a_3084_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v_a_3086_; 
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
lean_inc(v_a_3086_);
lean_dec_ref_known(v___x_3085_, 1);
if (lean_obj_tag(v_a_3086_) == 1)
{
lean_object* v_val_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3161_; 
lean_dec(v_a_3084_);
v_val_3087_ = lean_ctor_get(v_a_3086_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v_a_3086_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3089_ = v_a_3086_;
v_isShared_3090_ = v_isSharedCheck_3161_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_val_3087_);
lean_dec(v_a_3086_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3161_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v_fst_3091_; lean_object* v_snd_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3160_; 
v_fst_3091_ = lean_ctor_get(v_val_3087_, 0);
v_snd_3092_ = lean_ctor_get(v_val_3087_, 1);
v_isSharedCheck_3160_ = !lean_is_exclusive(v_val_3087_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3094_ = v_val_3087_;
v_isShared_3095_ = v_isSharedCheck_3160_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_snd_3092_);
lean_inc(v_fst_3091_);
lean_dec(v_val_3087_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3160_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v_hName_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; 
if (lean_obj_tag(v_hName_x3f_3074_) == 0)
{
lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3148_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__1));
v___x_3149_ = l_Lean_Core_mkFreshUserName(v___x_3148_, v___y_3077_, v___y_3078_);
if (lean_obj_tag(v___x_3149_) == 0)
{
lean_object* v_a_3150_; 
v_a_3150_ = lean_ctor_get(v___x_3149_, 0);
lean_inc(v_a_3150_);
lean_dec_ref_known(v___x_3149_, 1);
v_hName_3123_ = v_a_3150_;
v___y_3124_ = v___y_3075_;
v___y_3125_ = v___y_3076_;
v___y_3126_ = v___y_3077_;
v___y_3127_ = v___y_3078_;
goto v___jp_3122_;
}
else
{
lean_object* v_a_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3158_; 
lean_del_object(v___x_3094_);
lean_dec(v_snd_3092_);
lean_dec(v_fst_3091_);
lean_del_object(v___x_3089_);
lean_dec(v_mvarId_3073_);
v_a_3151_ = lean_ctor_get(v___x_3149_, 0);
v_isSharedCheck_3158_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3153_ = v___x_3149_;
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_a_3151_);
lean_dec(v___x_3149_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3156_; 
if (v_isShared_3154_ == 0)
{
v___x_3156_ = v___x_3153_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v_a_3151_);
v___x_3156_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
return v___x_3156_;
}
}
}
}
else
{
lean_object* v_val_3159_; 
v_val_3159_ = lean_ctor_get(v_hName_x3f_3074_, 0);
lean_inc(v_val_3159_);
lean_dec_ref_known(v_hName_x3f_3074_, 1);
v_hName_3123_ = v_val_3159_;
v___y_3124_ = v___y_3075_;
v___y_3125_ = v___y_3076_;
v___y_3126_ = v___y_3077_;
v___y_3127_ = v___y_3078_;
goto v___jp_3122_;
}
v___jp_3096_:
{
lean_object* v___x_3102_; 
v___x_3102_ = l_Lean_MVarId_byCasesDec(v_mvarId_3073_, v_fst_3091_, v_snd_3092_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3113_; 
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3105_ = v___x_3102_;
v_isShared_3106_ = v_isSharedCheck_3113_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3102_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3113_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 0, v_a_3103_);
v___x_3108_ = v___x_3089_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3103_);
v___x_3108_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
lean_object* v___x_3110_; 
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 0, v___x_3108_);
v___x_3110_ = v___x_3105_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3108_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
else
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3121_; 
lean_del_object(v___x_3089_);
v_a_3114_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3116_ = v___x_3102_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3102_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3119_; 
if (v_isShared_3117_ == 0)
{
v___x_3119_ = v___x_3116_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3114_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
}
v___jp_3122_:
{
lean_object* v_options_3128_; uint8_t v_hasTrace_3129_; 
v_options_3128_ = lean_ctor_get(v___y_3126_, 2);
v_hasTrace_3129_ = lean_ctor_get_uint8(v_options_3128_, sizeof(void*)*1);
if (v_hasTrace_3129_ == 0)
{
lean_del_object(v___x_3094_);
v___y_3097_ = v_hName_3123_;
v___y_3098_ = v___y_3124_;
v___y_3099_ = v___y_3125_;
v___y_3100_ = v___y_3126_;
v___y_3101_ = v___y_3127_;
goto v___jp_3096_;
}
else
{
lean_object* v_inheritedTraceOptions_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; uint8_t v___x_3133_; 
v_inheritedTraceOptions_3130_ = lean_ctor_get(v___y_3126_, 13);
v___x_3131_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9));
v___x_3132_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10);
v___x_3133_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3130_, v_options_3128_, v___x_3132_);
if (v___x_3133_ == 0)
{
lean_del_object(v___x_3094_);
v___y_3097_ = v_hName_3123_;
v___y_3098_ = v___y_3124_;
v___y_3099_ = v___y_3125_;
v___y_3100_ = v___y_3126_;
v___y_3101_ = v___y_3127_;
goto v___jp_3096_;
}
else
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3137_; 
v___x_3134_ = lean_obj_once(&l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1, &l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1_once, _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1);
lean_inc(v_snd_3092_);
v___x_3135_ = l_Lean_MessageData_ofExpr(v_snd_3092_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set_tag(v___x_3094_, 7);
lean_ctor_set(v___x_3094_, 1, v___x_3135_);
lean_ctor_set(v___x_3094_, 0, v___x_3134_);
v___x_3137_ = v___x_3094_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v___x_3134_);
lean_ctor_set(v_reuseFailAlloc_3147_, 1, v___x_3135_);
v___x_3137_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
lean_object* v___x_3138_; 
v___x_3138_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_3131_, v___x_3137_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_dec_ref_known(v___x_3138_, 1);
v___y_3097_ = v_hName_3123_;
v___y_3098_ = v___y_3124_;
v___y_3099_ = v___y_3125_;
v___y_3100_ = v___y_3126_;
v___y_3101_ = v___y_3127_;
goto v___jp_3096_;
}
else
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3146_; 
lean_dec(v_hName_3123_);
lean_dec(v_snd_3092_);
lean_dec(v_fst_3091_);
lean_del_object(v___x_3089_);
lean_dec(v_mvarId_3073_);
v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3141_ = v___x_3138_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3138_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3144_; 
if (v_isShared_3142_ == 0)
{
v___x_3144_ = v___x_3141_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3139_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
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
lean_object* v_options_3162_; uint8_t v_hasTrace_3163_; 
lean_dec(v_a_3086_);
lean_dec(v_hName_x3f_3074_);
lean_dec(v_mvarId_3073_);
v_options_3162_ = lean_ctor_get(v___y_3077_, 2);
v_hasTrace_3163_ = lean_ctor_get_uint8(v_options_3162_, sizeof(void*)*1);
if (v_hasTrace_3163_ == 0)
{
lean_dec(v_a_3084_);
goto v___jp_3080_;
}
else
{
lean_object* v_inheritedTraceOptions_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; uint8_t v___x_3167_; 
v_inheritedTraceOptions_3164_ = lean_ctor_get(v___y_3077_, 13);
v___x_3165_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9));
v___x_3166_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10);
v___x_3167_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3164_, v_options_3162_, v___x_3166_);
if (v___x_3167_ == 0)
{
lean_dec(v_a_3084_);
goto v___jp_3080_;
}
else
{
lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3168_ = lean_obj_once(&l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3, &l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3_once, _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3);
v___x_3169_ = l_Lean_indentExpr(v_a_3084_);
v___x_3170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3168_);
lean_ctor_set(v___x_3170_, 1, v___x_3169_);
v___x_3171_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_3165_, v___x_3170_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_dec_ref_known(v___x_3171_, 1);
goto v___jp_3080_;
}
else
{
lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3179_; 
v_a_3172_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3174_ = v___x_3171_;
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_3171_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3177_; 
if (v_isShared_3175_ == 0)
{
v___x_3177_ = v___x_3174_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_a_3172_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3187_; 
lean_dec(v_a_3084_);
lean_dec(v_hName_x3f_3074_);
lean_dec(v_mvarId_3073_);
v_a_3180_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3182_ = v___x_3085_;
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_a_3180_);
lean_dec(v___x_3085_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3185_; 
if (v_isShared_3183_ == 0)
{
v___x_3185_ = v___x_3182_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_a_3180_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
}
v___jp_3080_:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3081_ = lean_box(0);
v___x_3082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
return v___x_3082_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___boxed(lean_object* v_e_3188_, lean_object* v_mvarId_3189_, lean_object* v_hName_x3f_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0(v_e_3188_, v_mvarId_3189_, v_hName_x3f_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f(lean_object* v_mvarId_3197_, lean_object* v_e_3198_, lean_object* v_hName_x3f_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_){
_start:
{
lean_object* v___f_3205_; lean_object* v___x_3206_; 
lean_inc(v_mvarId_3197_);
v___f_3205_ = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3205_, 0, v_e_3198_);
lean_closure_set(v___f_3205_, 1, v_mvarId_3197_);
lean_closure_set(v___f_3205_, 2, v_hName_x3f_3199_);
v___x_3206_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_3197_, v___f_3205_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_);
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___boxed(lean_object* v_mvarId_3207_, lean_object* v_e_3208_, lean_object* v_hName_x3f_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_){
_start:
{
lean_object* v_res_3215_; 
v_res_3215_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(v_mvarId_3207_, v_e_3208_, v_hName_x3f_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_);
lean_dec(v_a_3213_);
lean_dec_ref(v_a_3212_);
lean_dec(v_a_3211_);
lean_dec_ref(v_a_3210_);
return v_res_3215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0(lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
lean_object* v_lctx_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v_lctx_3221_ = lean_ctor_get(v___y_3216_, 2);
lean_inc_ref(v_lctx_3221_);
lean_dec_ref(v___y_3216_);
v___x_3222_ = lean_local_ctx_num_indices(v_lctx_3221_);
v___x_3223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0___boxed(lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0(v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec(v___y_3225_);
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(lean_object* v_mvarId_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_){
_start:
{
lean_object* v___f_3237_; lean_object* v___x_3238_; 
v___f_3237_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___closed__0));
v___x_3238_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_3231_, v___f_3237_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_);
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___boxed(lean_object* v_mvarId_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(v_mvarId_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_);
lean_dec(v_a_3243_);
lean_dec_ref(v_a_3242_);
lean_dec(v_a_3241_);
lean_dec_ref(v_a_3240_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_simpIfTarget_spec__0(lean_object* v_msg_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_){
_start:
{
lean_object* v___f_3253_; lean_object* v___x_1955__overap_3254_; lean_object* v___x_3255_; 
v___f_3253_ = ((lean_object*)(l_panic___at___00Lean_Meta_simpIfTarget_spec__0___closed__0));
v___x_1955__overap_3254_ = lean_panic_fn_borrowed(v___f_3253_, v_msg_3247_);
lean_inc(v___y_3251_);
lean_inc_ref(v___y_3250_);
lean_inc(v___y_3249_);
lean_inc_ref(v___y_3248_);
v___x_3255_ = lean_apply_5(v___x_1955__overap_3254_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, lean_box(0));
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_simpIfTarget_spec__0___boxed(lean_object* v_msg_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v_msg_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
return v_res_3262_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(lean_object* v_opts_3263_, lean_object* v_opt_3264_){
_start:
{
lean_object* v_name_3265_; lean_object* v_defValue_3266_; lean_object* v_map_3267_; lean_object* v___x_3268_; 
v_name_3265_ = lean_ctor_get(v_opt_3264_, 0);
v_defValue_3266_ = lean_ctor_get(v_opt_3264_, 1);
v_map_3267_ = lean_ctor_get(v_opts_3263_, 0);
v___x_3268_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3267_, v_name_3265_);
if (lean_obj_tag(v___x_3268_) == 0)
{
uint8_t v___x_3269_; 
v___x_3269_ = lean_unbox(v_defValue_3266_);
return v___x_3269_;
}
else
{
lean_object* v_val_3270_; 
v_val_3270_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_val_3270_);
lean_dec_ref_known(v___x_3268_, 1);
if (lean_obj_tag(v_val_3270_) == 1)
{
uint8_t v_v_3271_; 
v_v_3271_ = lean_ctor_get_uint8(v_val_3270_, 0);
lean_dec_ref_known(v_val_3270_, 0);
return v_v_3271_;
}
else
{
uint8_t v___x_3272_; 
lean_dec(v_val_3270_);
v___x_3272_ = lean_unbox(v_defValue_3266_);
return v___x_3272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1___boxed(lean_object* v_opts_3273_, lean_object* v_opt_3274_){
_start:
{
uint8_t v_res_3275_; lean_object* v_r_3276_; 
v_res_3275_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v_opts_3273_, v_opt_3274_);
lean_dec_ref(v_opt_3274_);
lean_dec_ref(v_opts_3273_);
v_r_3276_ = lean_box(v_res_3275_);
return v_r_3276_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__0(void){
_start:
{
lean_object* v___x_3277_; 
v___x_3277_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3277_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__1(void){
_start:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; 
v___x_3278_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__0, &l_Lean_Meta_simpIfTarget___closed__0_once, _init_l_Lean_Meta_simpIfTarget___closed__0);
v___x_3279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3278_);
return v___x_3279_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__2(void){
_start:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3280_ = lean_unsigned_to_nat(0u);
v___x_3281_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__1, &l_Lean_Meta_simpIfTarget___closed__1_once, _init_l_Lean_Meta_simpIfTarget___closed__1);
v___x_3282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3281_);
lean_ctor_set(v___x_3282_, 1, v___x_3280_);
return v___x_3282_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__3(void){
_start:
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3283_ = lean_unsigned_to_nat(32u);
v___x_3284_ = lean_mk_empty_array_with_capacity(v___x_3283_);
v___x_3285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3284_);
return v___x_3285_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__4(void){
_start:
{
size_t v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3286_ = ((size_t)5ULL);
v___x_3287_ = lean_unsigned_to_nat(0u);
v___x_3288_ = lean_unsigned_to_nat(32u);
v___x_3289_ = lean_mk_empty_array_with_capacity(v___x_3288_);
v___x_3290_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__3, &l_Lean_Meta_simpIfTarget___closed__3_once, _init_l_Lean_Meta_simpIfTarget___closed__3);
v___x_3291_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3291_, 0, v___x_3290_);
lean_ctor_set(v___x_3291_, 1, v___x_3289_);
lean_ctor_set(v___x_3291_, 2, v___x_3287_);
lean_ctor_set(v___x_3291_, 3, v___x_3287_);
lean_ctor_set_usize(v___x_3291_, 4, v___x_3286_);
return v___x_3291_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__5(void){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3292_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__4, &l_Lean_Meta_simpIfTarget___closed__4_once, _init_l_Lean_Meta_simpIfTarget___closed__4);
v___x_3293_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__1, &l_Lean_Meta_simpIfTarget___closed__1_once, _init_l_Lean_Meta_simpIfTarget___closed__1);
v___x_3294_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3293_);
lean_ctor_set(v___x_3294_, 1, v___x_3293_);
lean_ctor_set(v___x_3294_, 2, v___x_3293_);
lean_ctor_set(v___x_3294_, 3, v___x_3292_);
return v___x_3294_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__6(void){
_start:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3295_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__5, &l_Lean_Meta_simpIfTarget___closed__5_once, _init_l_Lean_Meta_simpIfTarget___closed__5);
v___x_3296_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__2, &l_Lean_Meta_simpIfTarget___closed__2_once, _init_l_Lean_Meta_simpIfTarget___closed__2);
v___x_3297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3296_);
lean_ctor_set(v___x_3297_, 1, v___x_3295_);
return v___x_3297_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__10(void){
_start:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3301_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__9));
v___x_3302_ = lean_unsigned_to_nat(78u);
v___x_3303_ = lean_unsigned_to_nat(289u);
v___x_3304_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__8));
v___x_3305_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_3306_ = l_mkPanicMessageWithDecl(v___x_3305_, v___x_3304_, v___x_3303_, v___x_3302_, v___x_3301_);
return v___x_3306_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__12(void){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3309_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__9));
v___x_3310_ = lean_unsigned_to_nat(128u);
v___x_3311_ = lean_unsigned_to_nat(293u);
v___x_3312_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__8));
v___x_3313_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_3314_ = l_mkPanicMessageWithDecl(v___x_3313_, v___x_3312_, v___x_3311_, v___x_3310_, v___x_3309_);
return v___x_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfTarget(lean_object* v_mvarId_3315_, uint8_t v_useDecide_3316_, uint8_t v_useNewSemantics_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_){
_start:
{
if (v_useNewSemantics_3317_ == 0)
{
lean_object* v_options_3370_; lean_object* v___x_3371_; uint8_t v___x_3372_; 
v_options_3370_ = lean_ctor_get(v_a_3320_, 2);
v___x_3371_ = l_Lean_Meta_backward_split;
v___x_3372_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v_options_3370_, v___x_3371_);
if (v___x_3372_ == 0)
{
goto v___jp_3323_;
}
else
{
lean_object* v___x_3373_; 
v___x_3373_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v_a_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
lean_inc(v_a_3374_);
lean_dec_ref_known(v___x_3373_, 1);
v___x_3375_ = lean_box(v_useDecide_3316_);
v___x_3376_ = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed), 6, 1);
lean_closure_set(v___x_3376_, 0, v___x_3375_);
lean_inc(v_mvarId_3315_);
v___x_3377_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_3315_, v___x_3376_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v_a_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
lean_inc(v_a_3378_);
lean_dec_ref_known(v___x_3377_, 1);
v___x_3379_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__11));
v___x_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3380_, 0, v_a_3378_);
v___x_3381_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__6, &l_Lean_Meta_simpIfTarget___closed__6_once, _init_l_Lean_Meta_simpIfTarget___closed__6);
v___x_3382_ = l_Lean_Meta_simpTarget(v_mvarId_3315_, v_a_3374_, v___x_3379_, v___x_3380_, v_useNewSemantics_3317_, v___x_3381_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3394_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3385_ = v___x_3382_;
v_isShared_3386_ = v_isSharedCheck_3394_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3382_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3394_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v_fst_3387_; 
v_fst_3387_ = lean_ctor_get(v_a_3383_, 0);
lean_inc(v_fst_3387_);
lean_dec(v_a_3383_);
if (lean_obj_tag(v_fst_3387_) == 1)
{
lean_object* v_val_3388_; lean_object* v___x_3390_; 
v_val_3388_ = lean_ctor_get(v_fst_3387_, 0);
lean_inc(v_val_3388_);
lean_dec_ref_known(v_fst_3387_, 1);
if (v_isShared_3386_ == 0)
{
lean_ctor_set(v___x_3385_, 0, v_val_3388_);
v___x_3390_ = v___x_3385_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_val_3388_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
else
{
lean_object* v___x_3392_; lean_object* v___x_3393_; 
lean_dec(v_fst_3387_);
lean_del_object(v___x_3385_);
v___x_3392_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__12, &l_Lean_Meta_simpIfTarget___closed__12_once, _init_l_Lean_Meta_simpIfTarget___closed__12);
v___x_3393_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3392_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
return v___x_3393_;
}
}
}
else
{
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3402_; 
v_a_3395_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3397_ = v___x_3382_;
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v___x_3382_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3400_; 
if (v_isShared_3398_ == 0)
{
v___x_3400_ = v___x_3397_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_a_3395_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
}
else
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
lean_dec(v_a_3374_);
lean_dec(v_mvarId_3315_);
v_a_3403_ = lean_ctor_get(v___x_3377_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3377_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3377_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_a_3403_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
else
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_dec(v_mvarId_3315_);
v_a_3411_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3373_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3373_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
}
else
{
goto v___jp_3323_;
}
v___jp_3323_:
{
lean_object* v___x_3324_; 
v___x_3324_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_3318_, v_a_3320_, v_a_3321_);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v_a_3325_; lean_object* v___x_3326_; 
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
lean_inc(v_a_3325_);
lean_dec_ref_known(v___x_3324_, 1);
lean_inc(v_mvarId_3315_);
v___x_3326_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(v_mvarId_3315_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; lean_object* v___x_3328_; lean_object* v_a_3329_; lean_object* v___x_3330_; uint8_t v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3327_);
lean_dec_ref_known(v___x_3326_, 1);
v___x_3328_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_a_3327_, v_useDecide_3316_);
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
lean_inc(v_a_3329_);
lean_dec_ref(v___x_3328_);
v___x_3330_ = lean_box(0);
v___x_3331_ = 0;
v___x_3332_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__6, &l_Lean_Meta_simpIfTarget___closed__6_once, _init_l_Lean_Meta_simpIfTarget___closed__6);
v___x_3333_ = l_Lean_Meta_simpTarget(v_mvarId_3315_, v_a_3325_, v_a_3329_, v___x_3330_, v___x_3331_, v___x_3332_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3345_; 
v_a_3334_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3336_ = v___x_3333_;
v_isShared_3337_ = v_isSharedCheck_3345_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3333_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3345_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v_fst_3338_; 
v_fst_3338_ = lean_ctor_get(v_a_3334_, 0);
lean_inc(v_fst_3338_);
lean_dec(v_a_3334_);
if (lean_obj_tag(v_fst_3338_) == 1)
{
lean_object* v_val_3339_; lean_object* v___x_3341_; 
v_val_3339_ = lean_ctor_get(v_fst_3338_, 0);
lean_inc(v_val_3339_);
lean_dec_ref_known(v_fst_3338_, 1);
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 0, v_val_3339_);
v___x_3341_ = v___x_3336_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v_val_3339_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
else
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
lean_dec(v_fst_3338_);
lean_del_object(v___x_3336_);
v___x_3343_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__10, &l_Lean_Meta_simpIfTarget___closed__10_once, _init_l_Lean_Meta_simpIfTarget___closed__10);
v___x_3344_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3343_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
return v___x_3344_;
}
}
}
else
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3353_; 
v_a_3346_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3348_ = v___x_3333_;
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3333_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3351_; 
if (v_isShared_3349_ == 0)
{
v___x_3351_ = v___x_3348_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_a_3346_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
}
else
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3361_; 
lean_dec(v_a_3325_);
lean_dec(v_mvarId_3315_);
v_a_3354_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3356_ = v___x_3326_;
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3326_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3359_; 
if (v_isShared_3357_ == 0)
{
v___x_3359_ = v___x_3356_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_a_3354_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
}
else
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3369_; 
lean_dec(v_mvarId_3315_);
v_a_3362_ = lean_ctor_get(v___x_3324_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3364_ = v___x_3324_;
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3324_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3367_; 
if (v_isShared_3365_ == 0)
{
v___x_3367_ = v___x_3364_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_a_3362_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfTarget___boxed(lean_object* v_mvarId_3419_, lean_object* v_useDecide_3420_, lean_object* v_useNewSemantics_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_){
_start:
{
uint8_t v_useDecide_boxed_3427_; uint8_t v_useNewSemantics_boxed_3428_; lean_object* v_res_3429_; 
v_useDecide_boxed_3427_ = lean_unbox(v_useDecide_3420_);
v_useNewSemantics_boxed_3428_ = lean_unbox(v_useNewSemantics_3421_);
v_res_3429_ = l_Lean_Meta_simpIfTarget(v_mvarId_3419_, v_useDecide_boxed_3427_, v_useNewSemantics_boxed_3428_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_);
lean_dec(v_a_3425_);
lean_dec_ref(v_a_3424_);
lean_dec(v_a_3423_);
lean_dec_ref(v_a_3422_);
return v_res_3429_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfLocalDecl___closed__1(void){
_start:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3431_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__9));
v___x_3432_ = lean_unsigned_to_nat(93u);
v___x_3433_ = lean_unsigned_to_nat(305u);
v___x_3434_ = ((lean_object*)(l_Lean_Meta_simpIfLocalDecl___closed__0));
v___x_3435_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_3436_ = l_mkPanicMessageWithDecl(v___x_3435_, v___x_3434_, v___x_3433_, v___x_3432_, v___x_3431_);
return v___x_3436_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfLocalDecl___closed__2(void){
_start:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3437_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__9));
v___x_3438_ = lean_unsigned_to_nat(133u);
v___x_3439_ = lean_unsigned_to_nat(309u);
v___x_3440_ = ((lean_object*)(l_Lean_Meta_simpIfLocalDecl___closed__0));
v___x_3441_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_3442_ = l_mkPanicMessageWithDecl(v___x_3441_, v___x_3440_, v___x_3439_, v___x_3438_, v___x_3437_);
return v___x_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfLocalDecl(lean_object* v_mvarId_3443_, lean_object* v_fvarId_3444_, uint8_t v_useNewSemantics_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_){
_start:
{
if (v_useNewSemantics_3445_ == 0)
{
lean_object* v_options_3499_; lean_object* v___x_3500_; uint8_t v___x_3501_; 
v_options_3499_ = lean_ctor_get(v_a_3448_, 2);
v___x_3500_ = l_Lean_Meta_backward_split;
v___x_3501_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v_options_3499_, v___x_3500_);
if (v___x_3501_ == 0)
{
goto v___jp_3451_;
}
else
{
lean_object* v___x_3502_; 
v___x_3502_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_a_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
lean_inc(v_a_3503_);
lean_dec_ref_known(v___x_3502_, 1);
v___x_3504_ = lean_box(v_useNewSemantics_3445_);
v___x_3505_ = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed), 6, 1);
lean_closure_set(v___x_3505_, 0, v___x_3504_);
lean_inc(v_mvarId_3443_);
v___x_3506_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_3443_, v___x_3505_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v_a_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v_a_3507_ = lean_ctor_get(v___x_3506_, 0);
lean_inc(v_a_3507_);
lean_dec_ref_known(v___x_3506_, 1);
v___x_3508_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__11));
v___x_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3509_, 0, v_a_3507_);
v___x_3510_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__6, &l_Lean_Meta_simpIfTarget___closed__6_once, _init_l_Lean_Meta_simpIfTarget___closed__6);
v___x_3511_ = l_Lean_Meta_simpLocalDecl(v_mvarId_3443_, v_fvarId_3444_, v_a_3503_, v___x_3508_, v___x_3509_, v_useNewSemantics_3445_, v___x_3510_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3524_; 
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3514_ = v___x_3511_;
v_isShared_3515_ = v_isSharedCheck_3524_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3511_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3524_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v_fst_3516_; 
v_fst_3516_ = lean_ctor_get(v_a_3512_, 0);
lean_inc(v_fst_3516_);
lean_dec(v_a_3512_);
if (lean_obj_tag(v_fst_3516_) == 1)
{
lean_object* v_val_3517_; lean_object* v_snd_3518_; lean_object* v___x_3520_; 
v_val_3517_ = lean_ctor_get(v_fst_3516_, 0);
lean_inc(v_val_3517_);
lean_dec_ref_known(v_fst_3516_, 1);
v_snd_3518_ = lean_ctor_get(v_val_3517_, 1);
lean_inc(v_snd_3518_);
lean_dec(v_val_3517_);
if (v_isShared_3515_ == 0)
{
lean_ctor_set(v___x_3514_, 0, v_snd_3518_);
v___x_3520_ = v___x_3514_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_snd_3518_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
else
{
lean_object* v___x_3522_; lean_object* v___x_3523_; 
lean_dec(v_fst_3516_);
lean_del_object(v___x_3514_);
v___x_3522_ = lean_obj_once(&l_Lean_Meta_simpIfLocalDecl___closed__2, &l_Lean_Meta_simpIfLocalDecl___closed__2_once, _init_l_Lean_Meta_simpIfLocalDecl___closed__2);
v___x_3523_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3522_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
return v___x_3523_;
}
}
}
else
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3532_; 
v_a_3525_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3527_ = v___x_3511_;
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___x_3511_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3530_; 
if (v_isShared_3528_ == 0)
{
v___x_3530_ = v___x_3527_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3525_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
lean_dec(v_a_3503_);
lean_dec(v_fvarId_3444_);
lean_dec(v_mvarId_3443_);
v_a_3533_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3506_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3506_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3538_; 
if (v_isShared_3536_ == 0)
{
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3533_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
else
{
lean_object* v_a_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3548_; 
lean_dec(v_fvarId_3444_);
lean_dec(v_mvarId_3443_);
v_a_3541_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3543_ = v___x_3502_;
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_a_3541_);
lean_dec(v___x_3502_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3546_; 
if (v_isShared_3544_ == 0)
{
v___x_3546_ = v___x_3543_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3541_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
}
else
{
goto v___jp_3451_;
}
v___jp_3451_:
{
lean_object* v___x_3452_; 
v___x_3452_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_3446_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v_a_3453_; lean_object* v___x_3454_; 
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_a_3453_);
lean_dec_ref_known(v___x_3452_, 1);
lean_inc(v_mvarId_3443_);
v___x_3454_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(v_mvarId_3443_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3455_; uint8_t v___x_3456_; lean_object* v___x_3457_; lean_object* v_a_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; 
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
lean_inc(v_a_3455_);
lean_dec_ref_known(v___x_3454_, 1);
v___x_3456_ = 0;
v___x_3457_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_a_3455_, v___x_3456_);
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_a_3458_);
lean_dec_ref(v___x_3457_);
v___x_3459_ = lean_box(0);
v___x_3460_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__6, &l_Lean_Meta_simpIfTarget___closed__6_once, _init_l_Lean_Meta_simpIfTarget___closed__6);
v___x_3461_ = l_Lean_Meta_simpLocalDecl(v_mvarId_3443_, v_fvarId_3444_, v_a_3453_, v_a_3458_, v___x_3459_, v___x_3456_, v___x_3460_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3474_; 
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3464_ = v___x_3461_;
v_isShared_3465_ = v_isSharedCheck_3474_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3461_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3474_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v_fst_3466_; 
v_fst_3466_ = lean_ctor_get(v_a_3462_, 0);
lean_inc(v_fst_3466_);
lean_dec(v_a_3462_);
if (lean_obj_tag(v_fst_3466_) == 1)
{
lean_object* v_val_3467_; lean_object* v_snd_3468_; lean_object* v___x_3470_; 
v_val_3467_ = lean_ctor_get(v_fst_3466_, 0);
lean_inc(v_val_3467_);
lean_dec_ref_known(v_fst_3466_, 1);
v_snd_3468_ = lean_ctor_get(v_val_3467_, 1);
lean_inc(v_snd_3468_);
lean_dec(v_val_3467_);
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 0, v_snd_3468_);
v___x_3470_ = v___x_3464_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_snd_3468_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
else
{
lean_object* v___x_3472_; lean_object* v___x_3473_; 
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
v___x_3472_ = lean_obj_once(&l_Lean_Meta_simpIfLocalDecl___closed__1, &l_Lean_Meta_simpIfLocalDecl___closed__1_once, _init_l_Lean_Meta_simpIfLocalDecl___closed__1);
v___x_3473_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3472_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
return v___x_3473_;
}
}
}
else
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3482_; 
v_a_3475_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3477_ = v___x_3461_;
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3461_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3480_; 
if (v_isShared_3478_ == 0)
{
v___x_3480_ = v___x_3477_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_a_3475_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
else
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
lean_dec(v_a_3453_);
lean_dec(v_fvarId_3444_);
lean_dec(v_mvarId_3443_);
v_a_3483_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3485_ = v___x_3454_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3454_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3483_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
else
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3498_; 
lean_dec(v_fvarId_3444_);
lean_dec(v_mvarId_3443_);
v_a_3491_ = lean_ctor_get(v___x_3452_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3493_ = v___x_3452_;
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3452_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3496_; 
if (v_isShared_3494_ == 0)
{
v___x_3496_ = v___x_3493_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_a_3491_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfLocalDecl___boxed(lean_object* v_mvarId_3549_, lean_object* v_fvarId_3550_, lean_object* v_useNewSemantics_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_){
_start:
{
uint8_t v_useNewSemantics_boxed_3557_; lean_object* v_res_3558_; 
v_useNewSemantics_boxed_3557_ = lean_unbox(v_useNewSemantics_3551_);
v_res_3558_ = l_Lean_Meta_simpIfLocalDecl(v_mvarId_3549_, v_fvarId_3550_, v_useNewSemantics_boxed_3557_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_);
lean_dec(v_a_3555_);
lean_dec_ref(v_a_3554_);
lean_dec(v_a_3553_);
lean_dec_ref(v_a_3552_);
return v_res_3558_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(lean_object* v_x_x3f_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_){
_start:
{
lean_object* v___x_3565_; 
v___x_3565_ = l_Lean_Meta_saveState___redArg(v___y_3561_, v___y_3563_);
if (lean_obj_tag(v___x_3565_) == 0)
{
lean_object* v_a_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3610_; 
v_a_3566_ = lean_ctor_get(v___x_3565_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3565_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3568_ = v___x_3565_;
v_isShared_3569_ = v_isSharedCheck_3610_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_a_3566_);
lean_dec(v___x_3565_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3610_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v___y_3571_; uint8_t v___y_3572_; lean_object* v_a_3594_; lean_object* v___x_3597_; 
lean_inc(v___y_3563_);
lean_inc_ref(v___y_3562_);
lean_inc(v___y_3561_);
lean_inc_ref(v___y_3560_);
v___x_3597_ = lean_apply_5(v_x_x3f_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, lean_box(0));
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3598_; 
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_a_3598_);
if (lean_obj_tag(v_a_3598_) == 0)
{
lean_object* v___x_3599_; 
lean_dec_ref_known(v___x_3597_, 1);
v___x_3599_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3566_, v___y_3561_, v___y_3563_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3606_; 
lean_del_object(v___x_3568_);
lean_dec(v_a_3566_);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3606_ == 0)
{
lean_object* v_unused_3607_; 
v_unused_3607_ = lean_ctor_get(v___x_3599_, 0);
lean_dec(v_unused_3607_);
v___x_3601_ = v___x_3599_;
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
else
{
lean_dec(v___x_3599_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3604_; 
if (v_isShared_3602_ == 0)
{
lean_ctor_set(v___x_3601_, 0, v_a_3598_);
v___x_3604_ = v___x_3601_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3598_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
else
{
lean_object* v_a_3608_; 
v_a_3608_ = lean_ctor_get(v___x_3599_, 0);
lean_inc(v_a_3608_);
lean_dec_ref_known(v___x_3599_, 1);
v_a_3594_ = v_a_3608_;
goto v___jp_3593_;
}
}
else
{
lean_dec_ref_known(v_a_3598_, 1);
lean_del_object(v___x_3568_);
lean_dec(v_a_3566_);
return v___x_3597_;
}
}
else
{
lean_object* v_a_3609_; 
v_a_3609_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_a_3609_);
lean_dec_ref_known(v___x_3597_, 1);
v_a_3594_ = v_a_3609_;
goto v___jp_3593_;
}
v___jp_3570_:
{
if (v___y_3572_ == 0)
{
lean_object* v___x_3573_; 
lean_del_object(v___x_3568_);
v___x_3573_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3566_, v___y_3561_, v___y_3563_);
lean_dec(v_a_3566_);
if (lean_obj_tag(v___x_3573_) == 0)
{
lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3580_; 
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3580_ == 0)
{
lean_object* v_unused_3581_; 
v_unused_3581_ = lean_ctor_get(v___x_3573_, 0);
lean_dec(v_unused_3581_);
v___x_3575_ = v___x_3573_;
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
else
{
lean_dec(v___x_3573_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3578_; 
if (v_isShared_3576_ == 0)
{
lean_ctor_set_tag(v___x_3575_, 1);
lean_ctor_set(v___x_3575_, 0, v___y_3571_);
v___x_3578_ = v___x_3575_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___y_3571_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
else
{
lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3589_; 
lean_dec_ref(v___y_3571_);
v_a_3582_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3584_ = v___x_3573_;
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3573_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3587_; 
if (v_isShared_3585_ == 0)
{
v___x_3587_ = v___x_3584_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_a_3582_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
}
}
else
{
lean_object* v___x_3591_; 
lean_dec(v_a_3566_);
if (v_isShared_3569_ == 0)
{
lean_ctor_set_tag(v___x_3568_, 1);
lean_ctor_set(v___x_3568_, 0, v___y_3571_);
v___x_3591_ = v___x_3568_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v___y_3571_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
v___jp_3593_:
{
uint8_t v___x_3595_; 
v___x_3595_ = l_Lean_Exception_isInterrupt(v_a_3594_);
if (v___x_3595_ == 0)
{
uint8_t v___x_3596_; 
lean_inc_ref(v_a_3594_);
v___x_3596_ = l_Lean_Exception_isRuntime(v_a_3594_);
v___y_3571_ = v_a_3594_;
v___y_3572_ = v___x_3596_;
goto v___jp_3570_;
}
else
{
v___y_3571_ = v_a_3594_;
v___y_3572_ = v___x_3595_;
goto v___jp_3570_;
}
}
}
}
else
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_dec_ref(v_x_x3f_3559_);
v_a_3611_ = lean_ctor_get(v___x_3565_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3565_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3565_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3565_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg___boxed(lean_object* v_x_x3f_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
lean_object* v_res_3625_; 
v_res_3625_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v_x_x3f_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_);
lean_dec(v___y_3623_);
lean_dec_ref(v___y_3622_);
lean_dec(v___y_3621_);
lean_dec_ref(v___y_3620_);
return v_res_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0(lean_object* v_00_u03b1_3626_, lean_object* v_x_x3f_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
lean_object* v___x_3633_; 
v___x_3633_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v_x_x3f_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_);
return v___x_3633_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___boxed(lean_object* v_00_u03b1_3634_, lean_object* v_x_x3f_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v_res_3641_; 
v_res_3641_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0(v_00_u03b1_3634_, v_x_x3f_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_);
lean_dec(v___y_3639_);
lean_dec_ref(v___y_3638_);
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
return v_res_3641_;
}
}
static lean_object* _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; 
v___x_3646_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1));
v___x_3647_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4));
v___x_3648_ = l_Lean_Name_append(v___x_3647_, v___x_3646_);
return v___x_3648_;
}
}
static lean_object* _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3650_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__3));
v___x_3651_ = l_Lean_stringToMessageData(v___x_3650_);
return v___x_3651_;
}
}
static lean_object* _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3653_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__5));
v___x_3654_ = l_Lean_stringToMessageData(v___x_3653_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0(lean_object* v_mvarId_3655_, lean_object* v_hName_x3f_3656_, uint8_t v_useNewSemantics_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_){
_start:
{
lean_object* v___x_3666_; 
lean_inc(v_mvarId_3655_);
v___x_3666_ = l_Lean_MVarId_getType(v_mvarId_3655_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3668_; 
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
lean_inc(v_a_3667_);
lean_dec_ref_known(v___x_3666_, 1);
v___x_3668_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(v_mvarId_3655_, v_a_3667_, v_hName_x3f_3656_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
if (lean_obj_tag(v___x_3668_) == 0)
{
lean_object* v_a_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3765_; 
v_a_3669_ = lean_ctor_get(v___x_3668_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3671_ = v___x_3668_;
v_isShared_3672_ = v_isSharedCheck_3765_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_a_3669_);
lean_dec(v___x_3668_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3765_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
if (lean_obj_tag(v_a_3669_) == 1)
{
lean_object* v_val_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3760_; 
lean_del_object(v___x_3671_);
v_val_3673_ = lean_ctor_get(v_a_3669_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v_a_3669_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3675_ = v_a_3669_;
v_isShared_3676_ = v_isSharedCheck_3760_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_val_3673_);
lean_dec(v_a_3669_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3760_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v_fst_3677_; lean_object* v_snd_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3759_; 
v_fst_3677_ = lean_ctor_get(v_val_3673_, 0);
v_snd_3678_ = lean_ctor_get(v_val_3673_, 1);
v_isSharedCheck_3759_ = !lean_is_exclusive(v_val_3673_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3680_ = v_val_3673_;
v_isShared_3681_ = v_isSharedCheck_3759_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_snd_3678_);
lean_inc(v_fst_3677_);
lean_dec(v_val_3673_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3759_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v_mvarId_3682_; lean_object* v_fvarId_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3758_; 
v_mvarId_3682_ = lean_ctor_get(v_fst_3677_, 0);
v_fvarId_3683_ = lean_ctor_get(v_fst_3677_, 1);
v_isSharedCheck_3758_ = !lean_is_exclusive(v_fst_3677_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3685_ = v_fst_3677_;
v_isShared_3686_ = v_isSharedCheck_3758_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_fvarId_3683_);
lean_inc(v_mvarId_3682_);
lean_dec(v_fst_3677_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3758_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
uint8_t v___x_3687_; lean_object* v___x_3688_; 
v___x_3687_ = 0;
lean_inc(v_mvarId_3682_);
v___x_3688_ = l_Lean_Meta_simpIfTarget(v_mvarId_3682_, v___x_3687_, v_useNewSemantics_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
if (lean_obj_tag(v___x_3688_) == 0)
{
lean_object* v_a_3689_; lean_object* v_mvarId_3690_; lean_object* v_fvarId_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3749_; 
v_a_3689_ = lean_ctor_get(v___x_3688_, 0);
lean_inc(v_a_3689_);
lean_dec_ref_known(v___x_3688_, 1);
v_mvarId_3690_ = lean_ctor_get(v_snd_3678_, 0);
v_fvarId_3691_ = lean_ctor_get(v_snd_3678_, 1);
v_isSharedCheck_3749_ = !lean_is_exclusive(v_snd_3678_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3693_ = v_snd_3678_;
v_isShared_3694_ = v_isSharedCheck_3749_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_fvarId_3691_);
lean_inc(v_mvarId_3690_);
lean_dec(v_snd_3678_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3749_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3695_; 
lean_inc(v_mvarId_3690_);
v___x_3695_ = l_Lean_Meta_simpIfTarget(v_mvarId_3690_, v___x_3687_, v_useNewSemantics_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3740_; 
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3698_ = v___x_3695_;
v_isShared_3699_ = v_isSharedCheck_3740_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3695_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3740_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
uint8_t v___x_3716_; 
v___x_3716_ = l_Lean_instBEqMVarId_beq(v_mvarId_3682_, v_a_3689_);
lean_dec(v_mvarId_3682_);
if (v___x_3716_ == 0)
{
lean_dec(v_mvarId_3690_);
goto v___jp_3700_;
}
else
{
uint8_t v___x_3717_; 
v___x_3717_ = l_Lean_instBEqMVarId_beq(v_mvarId_3690_, v_a_3696_);
lean_dec(v_mvarId_3690_);
if (v___x_3717_ == 0)
{
goto v___jp_3700_;
}
else
{
lean_object* v_options_3718_; uint8_t v_hasTrace_3719_; 
lean_del_object(v___x_3698_);
lean_del_object(v___x_3693_);
lean_dec(v_fvarId_3691_);
lean_del_object(v___x_3685_);
lean_dec(v_fvarId_3683_);
lean_del_object(v___x_3680_);
lean_del_object(v___x_3675_);
v_options_3718_ = lean_ctor_get(v___y_3660_, 2);
v_hasTrace_3719_ = lean_ctor_get_uint8(v_options_3718_, sizeof(void*)*1);
if (v_hasTrace_3719_ == 0)
{
lean_dec(v_a_3696_);
lean_dec(v_a_3689_);
goto v___jp_3663_;
}
else
{
lean_object* v_inheritedTraceOptions_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; uint8_t v___x_3723_; 
v_inheritedTraceOptions_3720_ = lean_ctor_get(v___y_3660_, 13);
v___x_3721_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1));
v___x_3722_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2);
v___x_3723_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3720_, v_options_3718_, v___x_3722_);
if (v___x_3723_ == 0)
{
lean_dec(v_a_3696_);
lean_dec(v_a_3689_);
goto v___jp_3663_;
}
else
{
lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3724_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4);
v___x_3725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3725_, 0, v_a_3689_);
v___x_3726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3724_);
lean_ctor_set(v___x_3726_, 1, v___x_3725_);
v___x_3727_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6);
v___x_3728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3726_);
lean_ctor_set(v___x_3728_, 1, v___x_3727_);
v___x_3729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3729_, 0, v_a_3696_);
v___x_3730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3728_);
lean_ctor_set(v___x_3730_, 1, v___x_3729_);
v___x_3731_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_3721_, v___x_3730_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_dec_ref_known(v___x_3731_, 1);
goto v___jp_3663_;
}
else
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
v_a_3732_ = lean_ctor_get(v___x_3731_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3731_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3731_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3731_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3732_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
}
}
}
}
v___jp_3700_:
{
lean_object* v___x_3702_; 
if (v_isShared_3694_ == 0)
{
lean_ctor_set(v___x_3693_, 1, v_fvarId_3683_);
lean_ctor_set(v___x_3693_, 0, v_a_3689_);
v___x_3702_ = v___x_3693_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3689_);
lean_ctor_set(v_reuseFailAlloc_3715_, 1, v_fvarId_3683_);
v___x_3702_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
lean_object* v___x_3704_; 
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 1, v_fvarId_3691_);
lean_ctor_set(v___x_3685_, 0, v_a_3696_);
v___x_3704_ = v___x_3685_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_a_3696_);
lean_ctor_set(v_reuseFailAlloc_3714_, 1, v_fvarId_3691_);
v___x_3704_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
lean_object* v___x_3706_; 
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 1, v___x_3704_);
lean_ctor_set(v___x_3680_, 0, v___x_3702_);
v___x_3706_ = v___x_3680_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v___x_3702_);
lean_ctor_set(v_reuseFailAlloc_3713_, 1, v___x_3704_);
v___x_3706_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
lean_object* v___x_3708_; 
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 0, v___x_3706_);
v___x_3708_ = v___x_3675_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v___x_3706_);
v___x_3708_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
lean_object* v___x_3710_; 
if (v_isShared_3699_ == 0)
{
lean_ctor_set(v___x_3698_, 0, v___x_3708_);
v___x_3710_ = v___x_3698_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v___x_3708_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
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
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
lean_del_object(v___x_3693_);
lean_dec(v_fvarId_3691_);
lean_dec(v_mvarId_3690_);
lean_dec(v_a_3689_);
lean_del_object(v___x_3685_);
lean_dec(v_fvarId_3683_);
lean_dec(v_mvarId_3682_);
lean_del_object(v___x_3680_);
lean_del_object(v___x_3675_);
v_a_3741_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3743_ = v___x_3695_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3695_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3741_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
}
else
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3757_; 
lean_del_object(v___x_3685_);
lean_dec(v_fvarId_3683_);
lean_dec(v_mvarId_3682_);
lean_del_object(v___x_3680_);
lean_dec(v_snd_3678_);
lean_del_object(v___x_3675_);
v_a_3750_ = lean_ctor_get(v___x_3688_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3752_ = v___x_3688_;
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3688_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3755_; 
if (v_isShared_3753_ == 0)
{
v___x_3755_ = v___x_3752_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_a_3750_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3761_; lean_object* v___x_3763_; 
lean_dec(v_a_3669_);
v___x_3761_ = lean_box(0);
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 0, v___x_3761_);
v___x_3763_ = v___x_3671_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v___x_3761_);
v___x_3763_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
return v___x_3763_;
}
}
}
}
else
{
return v___x_3668_;
}
}
else
{
lean_object* v_a_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3773_; 
lean_dec(v_hName_x3f_3656_);
lean_dec(v_mvarId_3655_);
v_a_3766_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3768_ = v___x_3666_;
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_a_3766_);
lean_dec(v___x_3666_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3771_; 
if (v_isShared_3769_ == 0)
{
v___x_3771_ = v___x_3768_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_a_3766_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
v___jp_3663_:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3664_ = lean_box(0);
v___x_3665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3665_, 0, v___x_3664_);
return v___x_3665_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0___boxed(lean_object* v_mvarId_3774_, lean_object* v_hName_x3f_3775_, lean_object* v_useNewSemantics_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_){
_start:
{
uint8_t v_useNewSemantics_boxed_3782_; lean_object* v_res_3783_; 
v_useNewSemantics_boxed_3782_ = lean_unbox(v_useNewSemantics_3776_);
v_res_3783_ = l_Lean_Meta_splitIfTarget_x3f___lam__0(v_mvarId_3774_, v_hName_x3f_3775_, v_useNewSemantics_boxed_3782_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
lean_dec(v___y_3778_);
lean_dec_ref(v___y_3777_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f(lean_object* v_mvarId_3784_, lean_object* v_hName_x3f_3785_, uint8_t v_useNewSemantics_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_){
_start:
{
lean_object* v___x_3792_; lean_object* v___f_3793_; lean_object* v___x_3794_; 
v___x_3792_ = lean_box(v_useNewSemantics_3786_);
v___f_3793_ = lean_alloc_closure((void*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3793_, 0, v_mvarId_3784_);
lean_closure_set(v___f_3793_, 1, v_hName_x3f_3785_);
lean_closure_set(v___f_3793_, 2, v___x_3792_);
v___x_3794_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v___f_3793_, v_a_3787_, v_a_3788_, v_a_3789_, v_a_3790_);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___boxed(lean_object* v_mvarId_3795_, lean_object* v_hName_x3f_3796_, lean_object* v_useNewSemantics_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_){
_start:
{
uint8_t v_useNewSemantics_boxed_3803_; lean_object* v_res_3804_; 
v_useNewSemantics_boxed_3803_ = lean_unbox(v_useNewSemantics_3797_);
v_res_3804_ = l_Lean_Meta_splitIfTarget_x3f(v_mvarId_3795_, v_hName_x3f_3796_, v_useNewSemantics_boxed_3803_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_);
lean_dec(v_a_3801_);
lean_dec_ref(v_a_3800_);
lean_dec(v_a_3799_);
lean_dec_ref(v_a_3798_);
return v_res_3804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___lam__0(lean_object* v___x_3805_, lean_object* v_mvarId_3806_, lean_object* v_hName_x3f_3807_, lean_object* v_fvarId_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
lean_object* v___x_3817_; 
lean_inc(v___y_3812_);
lean_inc_ref(v___y_3811_);
lean_inc(v___y_3810_);
lean_inc_ref(v___y_3809_);
v___x_3817_ = lean_infer_type(v___x_3805_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_object* v_a_3818_; lean_object* v___x_3819_; 
v_a_3818_ = lean_ctor_get(v___x_3817_, 0);
lean_inc(v_a_3818_);
lean_dec_ref_known(v___x_3817_, 1);
v___x_3819_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(v_mvarId_3806_, v_a_3818_, v_hName_x3f_3807_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3914_; 
v_a_3820_ = lean_ctor_get(v___x_3819_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3822_ = v___x_3819_;
v_isShared_3823_ = v_isSharedCheck_3914_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3819_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3914_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
if (lean_obj_tag(v_a_3820_) == 1)
{
lean_object* v_val_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3909_; 
lean_del_object(v___x_3822_);
v_val_3824_ = lean_ctor_get(v_a_3820_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v_a_3820_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3826_ = v_a_3820_;
v_isShared_3827_ = v_isSharedCheck_3909_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_val_3824_);
lean_dec(v_a_3820_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3909_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v_fst_3828_; lean_object* v_snd_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3908_; 
v_fst_3828_ = lean_ctor_get(v_val_3824_, 0);
v_snd_3829_ = lean_ctor_get(v_val_3824_, 1);
v_isSharedCheck_3908_ = !lean_is_exclusive(v_val_3824_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3831_ = v_val_3824_;
v_isShared_3832_ = v_isSharedCheck_3908_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_snd_3829_);
lean_inc(v_fst_3828_);
lean_dec(v_val_3824_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3908_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v_mvarId_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3906_; 
v_mvarId_3833_ = lean_ctor_get(v_fst_3828_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v_fst_3828_);
if (v_isSharedCheck_3906_ == 0)
{
lean_object* v_unused_3907_; 
v_unused_3907_ = lean_ctor_get(v_fst_3828_, 1);
lean_dec(v_unused_3907_);
v___x_3835_ = v_fst_3828_;
v_isShared_3836_ = v_isSharedCheck_3906_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_mvarId_3833_);
lean_dec(v_fst_3828_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3906_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
uint8_t v___x_3837_; lean_object* v___x_3838_; 
v___x_3837_ = 0;
lean_inc(v_fvarId_3808_);
lean_inc(v_mvarId_3833_);
v___x_3838_ = l_Lean_Meta_simpIfLocalDecl(v_mvarId_3833_, v_fvarId_3808_, v___x_3837_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
if (lean_obj_tag(v___x_3838_) == 0)
{
lean_object* v_a_3839_; lean_object* v_mvarId_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3896_; 
v_a_3839_ = lean_ctor_get(v___x_3838_, 0);
lean_inc(v_a_3839_);
lean_dec_ref_known(v___x_3838_, 1);
v_mvarId_3840_ = lean_ctor_get(v_snd_3829_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v_snd_3829_);
if (v_isSharedCheck_3896_ == 0)
{
lean_object* v_unused_3897_; 
v_unused_3897_ = lean_ctor_get(v_snd_3829_, 1);
lean_dec(v_unused_3897_);
v___x_3842_ = v_snd_3829_;
v_isShared_3843_ = v_isSharedCheck_3896_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_mvarId_3840_);
lean_dec(v_snd_3829_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3896_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3844_; 
lean_inc(v_mvarId_3840_);
v___x_3844_ = l_Lean_Meta_simpIfLocalDecl(v_mvarId_3840_, v_fvarId_3808_, v___x_3837_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
if (lean_obj_tag(v___x_3844_) == 0)
{
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3887_; 
v_a_3845_ = lean_ctor_get(v___x_3844_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3844_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3847_ = v___x_3844_;
v_isShared_3848_ = v_isSharedCheck_3887_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___x_3844_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3887_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
uint8_t v___x_3859_; 
v___x_3859_ = l_Lean_instBEqMVarId_beq(v_mvarId_3833_, v_a_3839_);
lean_dec(v_mvarId_3833_);
if (v___x_3859_ == 0)
{
lean_del_object(v___x_3842_);
lean_dec(v_mvarId_3840_);
lean_del_object(v___x_3835_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
goto v___jp_3849_;
}
else
{
uint8_t v___x_3860_; 
v___x_3860_ = l_Lean_instBEqMVarId_beq(v_mvarId_3840_, v_a_3845_);
lean_dec(v_mvarId_3840_);
if (v___x_3860_ == 0)
{
lean_del_object(v___x_3842_);
lean_del_object(v___x_3835_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
goto v___jp_3849_;
}
else
{
lean_object* v_options_3861_; uint8_t v_hasTrace_3862_; 
lean_del_object(v___x_3847_);
lean_del_object(v___x_3831_);
lean_del_object(v___x_3826_);
v_options_3861_ = lean_ctor_get(v___y_3811_, 2);
v_hasTrace_3862_ = lean_ctor_get_uint8(v_options_3861_, sizeof(void*)*1);
if (v_hasTrace_3862_ == 0)
{
lean_dec(v_a_3845_);
lean_del_object(v___x_3842_);
lean_dec(v_a_3839_);
lean_del_object(v___x_3835_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
goto v___jp_3814_;
}
else
{
lean_object* v_inheritedTraceOptions_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; uint8_t v___x_3866_; 
v_inheritedTraceOptions_3863_ = lean_ctor_get(v___y_3811_, 13);
v___x_3864_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1));
v___x_3865_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2);
v___x_3866_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3863_, v_options_3861_, v___x_3865_);
if (v___x_3866_ == 0)
{
lean_dec(v_a_3845_);
lean_del_object(v___x_3842_);
lean_dec(v_a_3839_);
lean_del_object(v___x_3835_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
goto v___jp_3814_;
}
else
{
lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3870_; 
v___x_3867_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4);
v___x_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3868_, 0, v_a_3839_);
if (v_isShared_3843_ == 0)
{
lean_ctor_set_tag(v___x_3842_, 7);
lean_ctor_set(v___x_3842_, 1, v___x_3868_);
lean_ctor_set(v___x_3842_, 0, v___x_3867_);
v___x_3870_ = v___x_3842_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v___x_3867_);
lean_ctor_set(v_reuseFailAlloc_3886_, 1, v___x_3868_);
v___x_3870_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
lean_object* v___x_3871_; lean_object* v___x_3873_; 
v___x_3871_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6);
if (v_isShared_3836_ == 0)
{
lean_ctor_set_tag(v___x_3835_, 7);
lean_ctor_set(v___x_3835_, 1, v___x_3871_);
lean_ctor_set(v___x_3835_, 0, v___x_3870_);
v___x_3873_ = v___x_3835_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v___x_3870_);
lean_ctor_set(v_reuseFailAlloc_3885_, 1, v___x_3871_);
v___x_3873_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3874_, 0, v_a_3845_);
v___x_3875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3875_, 0, v___x_3873_);
lean_ctor_set(v___x_3875_, 1, v___x_3874_);
v___x_3876_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_3864_, v___x_3875_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_dec_ref_known(v___x_3876_, 1);
goto v___jp_3814_;
}
else
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3884_; 
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3879_ = v___x_3876_;
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3876_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
if (v_isShared_3880_ == 0)
{
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_a_3877_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
}
}
}
}
}
}
v___jp_3849_:
{
lean_object* v___x_3851_; 
if (v_isShared_3832_ == 0)
{
lean_ctor_set(v___x_3831_, 1, v_a_3845_);
lean_ctor_set(v___x_3831_, 0, v_a_3839_);
v___x_3851_ = v___x_3831_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_a_3839_);
lean_ctor_set(v_reuseFailAlloc_3858_, 1, v_a_3845_);
v___x_3851_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
lean_object* v___x_3853_; 
if (v_isShared_3827_ == 0)
{
lean_ctor_set(v___x_3826_, 0, v___x_3851_);
v___x_3853_ = v___x_3826_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v___x_3851_);
v___x_3853_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
lean_object* v___x_3855_; 
if (v_isShared_3848_ == 0)
{
lean_ctor_set(v___x_3847_, 0, v___x_3853_);
v___x_3855_ = v___x_3847_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v___x_3853_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
}
}
else
{
lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3895_; 
lean_del_object(v___x_3842_);
lean_dec(v_mvarId_3840_);
lean_dec(v_a_3839_);
lean_del_object(v___x_3835_);
lean_dec(v_mvarId_3833_);
lean_del_object(v___x_3831_);
lean_del_object(v___x_3826_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
v_a_3888_ = lean_ctor_get(v___x_3844_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3844_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3890_ = v___x_3844_;
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v___x_3844_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
if (v_isShared_3891_ == 0)
{
v___x_3893_ = v___x_3890_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3888_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
}
}
}
}
}
else
{
lean_object* v_a_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3905_; 
lean_del_object(v___x_3835_);
lean_dec(v_mvarId_3833_);
lean_del_object(v___x_3831_);
lean_dec(v_snd_3829_);
lean_del_object(v___x_3826_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
lean_dec(v_fvarId_3808_);
v_a_3898_ = lean_ctor_get(v___x_3838_, 0);
v_isSharedCheck_3905_ = !lean_is_exclusive(v___x_3838_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3900_ = v___x_3838_;
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_a_3898_);
lean_dec(v___x_3838_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3903_; 
if (v_isShared_3901_ == 0)
{
v___x_3903_ = v___x_3900_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_a_3898_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
return v___x_3903_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3910_; lean_object* v___x_3912_; 
lean_dec(v_a_3820_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
lean_dec(v_fvarId_3808_);
v___x_3910_ = lean_box(0);
if (v_isShared_3823_ == 0)
{
lean_ctor_set(v___x_3822_, 0, v___x_3910_);
v___x_3912_ = v___x_3822_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v___x_3910_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
}
}
else
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3922_; 
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
lean_dec(v_fvarId_3808_);
v_a_3915_ = lean_ctor_get(v___x_3819_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3917_ = v___x_3819_;
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3819_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3920_; 
if (v_isShared_3918_ == 0)
{
v___x_3920_ = v___x_3917_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
lean_dec(v_fvarId_3808_);
lean_dec(v_hName_x3f_3807_);
lean_dec(v_mvarId_3806_);
v_a_3923_ = lean_ctor_get(v___x_3817_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3817_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3817_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3817_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3923_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
v___jp_3814_:
{
lean_object* v___x_3815_; lean_object* v___x_3816_; 
v___x_3815_ = lean_box(0);
v___x_3816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3815_);
return v___x_3816_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___lam__0___boxed(lean_object* v___x_3931_, lean_object* v_mvarId_3932_, lean_object* v_hName_x3f_3933_, lean_object* v_fvarId_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_){
_start:
{
lean_object* v_res_3940_; 
v_res_3940_ = l_Lean_Meta_splitIfLocalDecl_x3f___lam__0(v___x_3931_, v_mvarId_3932_, v_hName_x3f_3933_, v_fvarId_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
return v_res_3940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f(lean_object* v_mvarId_3941_, lean_object* v_fvarId_3942_, lean_object* v_hName_x3f_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_){
_start:
{
lean_object* v___x_3949_; lean_object* v___f_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; 
lean_inc(v_fvarId_3942_);
v___x_3949_ = l_Lean_mkFVar(v_fvarId_3942_);
lean_inc(v_mvarId_3941_);
v___f_3950_ = lean_alloc_closure((void*)(l_Lean_Meta_splitIfLocalDecl_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3950_, 0, v___x_3949_);
lean_closure_set(v___f_3950_, 1, v_mvarId_3941_);
lean_closure_set(v___f_3950_, 2, v_hName_x3f_3943_);
lean_closure_set(v___f_3950_, 3, v_fvarId_3942_);
v___x_3951_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3951_, 0, lean_box(0));
lean_closure_set(v___x_3951_, 1, v_mvarId_3941_);
lean_closure_set(v___x_3951_, 2, v___f_3950_);
v___x_3952_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v___x_3951_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_);
return v___x_3952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___boxed(lean_object* v_mvarId_3953_, lean_object* v_fvarId_3954_, lean_object* v_hName_x3f_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l_Lean_Meta_splitIfLocalDecl_x3f(v_mvarId_3953_, v_fvarId_3954_, v_hName_x3f_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_);
lean_dec(v_a_3959_);
lean_dec_ref(v_a_3958_);
lean_dec(v_a_3957_);
lean_dec_ref(v_a_3956_);
return v_res_3961_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
v___x_3982_ = lean_unsigned_to_nat(3526097586u);
v___x_3983_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_));
v___x_3984_ = l_Lean_Name_num___override(v___x_3983_, v___x_3982_);
return v___x_3984_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; 
v___x_3986_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_));
v___x_3987_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3988_ = l_Lean_Name_str___override(v___x_3987_, v___x_3986_);
return v___x_3988_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; 
v___x_3990_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_));
v___x_3991_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3992_ = l_Lean_Name_str___override(v___x_3991_, v___x_3990_);
return v___x_3992_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3993_ = lean_unsigned_to_nat(2u);
v___x_3994_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3995_ = l_Lean_Name_num___override(v___x_3994_, v___x_3993_);
return v___x_3995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3997_; uint8_t v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3997_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9));
v___x_3998_ = 0;
v___x_3999_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_4000_ = l_Lean_registerTraceClass(v___x_3997_, v___x_3998_, v___x_3999_);
return v___x_4000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2____boxed(lean_object* v_a_4001_){
_start:
{
lean_object* v_res_4002_; 
v_res_4002_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_();
return v_res_4002_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_SplitIf(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
