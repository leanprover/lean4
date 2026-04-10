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
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
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
lean_object* v_exceptionSet_153_; uint8_t v_kind_154_; lean_object* v_e_156_; lean_object* v___y_184_; lean_object* v___y_185_; uint8_t v___y_186_; uint8_t v___x_196_; 
v_exceptionSet_153_ = lean_ctor_get(v_ctx_151_, 0);
v_kind_154_ = lean_ctor_get_uint8(v_ctx_151_, sizeof(void*)*1);
v___x_196_ = l_Lean_Meta_SplitKind_considerIte(v_kind_154_);
if (v___x_196_ == 0)
{
goto v___jp_160_;
}
else
{
lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_197_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__2));
v___x_198_ = l_Lean_Expr_isAppOf(v_e_152_, v___x_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__4));
v___x_200_ = l_Lean_Expr_isAppOf(v_e_152_, v___x_199_);
if (v___x_200_ == 0)
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
lean_dec_ref(v___x_163_);
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
lean_dec_ref(v_fst_176_);
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
lean_dec(v___y_184_);
goto v___jp_160_;
}
else
{
lean_object* v___x_187_; lean_object* v___x_188_; 
lean_dec_ref(v_env_150_);
v___x_187_ = lean_nat_sub(v___y_184_, v___y_185_);
lean_dec(v___y_184_);
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
v___y_184_ = v_numArgs_190_;
v___y_185_ = v___x_191_;
v___y_186_ = v___x_192_;
goto v___jp_183_;
}
else
{
lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_193_ = lean_unsigned_to_nat(3u);
v___x_194_ = l_Lean_Expr_getRevArg_x21(v_e_152_, v___x_193_);
v___x_195_ = l_Lean_Expr_hasLooseBVars(v___x_194_);
lean_dec_ref(v___x_194_);
if (v___x_195_ == 0)
{
v___y_184_ = v_numArgs_190_;
v___y_185_ = v___x_191_;
v___y_186_ = v___x_192_;
goto v___jp_183_;
}
else
{
lean_dec(v_numArgs_190_);
goto v___jp_160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___boxed(lean_object* v_env_201_, lean_object* v_ctx_202_, lean_object* v_e_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f(v_env_201_, v_ctx_202_, v_e_203_);
lean_dec_ref(v_ctx_202_);
return v_res_204_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0(lean_object* v_00_u03b2_205_, lean_object* v_m_206_, lean_object* v_a_207_){
_start:
{
uint8_t v___x_208_; 
v___x_208_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(v_m_206_, v_a_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___boxed(lean_object* v_00_u03b2_209_, lean_object* v_m_210_, lean_object* v_a_211_){
_start:
{
uint8_t v_res_212_; lean_object* v_r_213_; 
v_res_212_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0(v_00_u03b2_209_, v_m_210_, v_a_211_);
lean_dec_ref(v_a_211_);
lean_dec_ref(v_m_210_);
v_r_213_ = lean_box(v_res_212_);
return v_r_213_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1(lean_object* v_upperBound_214_, lean_object* v_args_215_, lean_object* v_inst_216_, lean_object* v_R_217_, lean_object* v_a_218_, lean_object* v_b_219_, lean_object* v_c_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg(v_upperBound_214_, v_args_215_, v_a_218_, v_b_219_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___boxed(lean_object* v_upperBound_222_, lean_object* v_args_223_, lean_object* v_inst_224_, lean_object* v_R_225_, lean_object* v_a_226_, lean_object* v_b_227_, lean_object* v_c_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1(v_upperBound_222_, v_args_223_, v_inst_224_, v_R_225_, v_a_226_, v_b_227_, v_c_228_);
lean_dec_ref(v_b_227_);
lean_dec_ref(v_args_223_);
lean_dec(v_upperBound_222_);
return v_res_229_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0(lean_object* v_00_u03b2_230_, lean_object* v_a_231_, lean_object* v_x_232_){
_start:
{
uint8_t v___x_233_; 
v___x_233_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg(v_a_231_, v_x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_234_, lean_object* v_a_235_, lean_object* v_x_236_){
_start:
{
uint8_t v_res_237_; lean_object* v_r_238_; 
v_res_237_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0(v_00_u03b2_234_, v_a_235_, v_x_236_);
lean_dec(v_x_236_);
lean_dec_ref(v_a_235_);
v_r_238_ = lean_box(v_res_237_);
return v_r_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___redArg(lean_object* v_e_243_, lean_object* v_a_244_){
_start:
{
lean_object* v___f_246_; lean_object* v___f_247_; uint8_t v___x_248_; 
v___f_246_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__0));
v___f_247_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__1));
lean_inc_ref(v_e_243_);
v___x_248_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_246_, v___f_247_, v_a_244_, v_e_243_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_249_ = lean_box(0);
v___x_250_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_246_, v___f_247_, v_a_244_, v_e_243_, v___x_249_);
v___x_251_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__2));
v___x_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v___x_250_);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
return v___x_253_;
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
lean_dec_ref(v_e_243_);
v___x_254_ = lean_box(0);
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v_a_244_);
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
return v___x_256_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___redArg___boxed(lean_object* v_e_257_, lean_object* v_a_258_, lean_object* v_a_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_Meta_FindSplitImpl_checkVisited___redArg(v_e_257_, v_a_258_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited(lean_object* v_e_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_){
_start:
{
lean_object* v___f_269_; lean_object* v___f_270_; uint8_t v___x_271_; 
v___f_269_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__0));
v___f_270_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__1));
lean_inc_ref(v_e_261_);
v___x_271_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_269_, v___f_270_, v_a_263_, v_e_261_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_272_ = lean_box(0);
v___x_273_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_269_, v___f_270_, v_a_263_, v_e_261_, v___x_272_);
v___x_274_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__2));
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
lean_ctor_set(v___x_275_, 1, v___x_273_);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
return v___x_276_;
}
else
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
lean_dec_ref(v_e_261_);
v___x_277_ = lean_box(0);
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v_a_263_);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___boxed(lean_object* v_e_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_Meta_FindSplitImpl_checkVisited(v_e_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
lean_dec_ref(v_a_281_);
return v_res_288_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(lean_object* v_a_289_, lean_object* v_x_290_){
_start:
{
if (lean_obj_tag(v_x_290_) == 0)
{
uint8_t v___x_291_; 
v___x_291_ = 0;
return v___x_291_;
}
else
{
lean_object* v_key_292_; lean_object* v_tail_293_; size_t v___x_294_; size_t v___x_295_; uint8_t v___x_296_; 
v_key_292_ = lean_ctor_get(v_x_290_, 0);
v_tail_293_ = lean_ctor_get(v_x_290_, 2);
v___x_294_ = lean_ptr_addr(v_key_292_);
v___x_295_ = lean_ptr_addr(v_a_289_);
v___x_296_ = lean_usize_dec_eq(v___x_294_, v___x_295_);
if (v___x_296_ == 0)
{
v_x_290_ = v_tail_293_;
goto _start;
}
else
{
return v___x_296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg___boxed(lean_object* v_a_298_, lean_object* v_x_299_){
_start:
{
uint8_t v_res_300_; lean_object* v_r_301_; 
v_res_300_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(v_a_298_, v_x_299_);
lean_dec(v_x_299_);
lean_dec_ref(v_a_298_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6_spec__7___redArg(lean_object* v_x_302_, lean_object* v_x_303_){
_start:
{
if (lean_obj_tag(v_x_303_) == 0)
{
return v_x_302_;
}
else
{
lean_object* v_key_304_; lean_object* v_value_305_; lean_object* v_tail_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_332_; 
v_key_304_ = lean_ctor_get(v_x_303_, 0);
v_value_305_ = lean_ctor_get(v_x_303_, 1);
v_tail_306_ = lean_ctor_get(v_x_303_, 2);
v_isSharedCheck_332_ = !lean_is_exclusive(v_x_303_);
if (v_isSharedCheck_332_ == 0)
{
v___x_308_ = v_x_303_;
v_isShared_309_ = v_isSharedCheck_332_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_tail_306_);
lean_inc(v_value_305_);
lean_inc(v_key_304_);
lean_dec(v_x_303_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_332_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; size_t v___x_311_; uint64_t v___x_312_; uint64_t v___x_313_; uint64_t v___x_314_; uint64_t v___x_315_; uint64_t v___x_316_; uint64_t v_fold_317_; uint64_t v___x_318_; uint64_t v___x_319_; uint64_t v___x_320_; size_t v___x_321_; size_t v___x_322_; size_t v___x_323_; size_t v___x_324_; size_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_310_ = lean_array_get_size(v_x_302_);
v___x_311_ = lean_ptr_addr(v_key_304_);
v___x_312_ = lean_usize_to_uint64(v___x_311_);
v___x_313_ = 11ULL;
v___x_314_ = lean_uint64_mix_hash(v___x_312_, v___x_313_);
v___x_315_ = 32ULL;
v___x_316_ = lean_uint64_shift_right(v___x_314_, v___x_315_);
v_fold_317_ = lean_uint64_xor(v___x_314_, v___x_316_);
v___x_318_ = 16ULL;
v___x_319_ = lean_uint64_shift_right(v_fold_317_, v___x_318_);
v___x_320_ = lean_uint64_xor(v_fold_317_, v___x_319_);
v___x_321_ = lean_uint64_to_usize(v___x_320_);
v___x_322_ = lean_usize_of_nat(v___x_310_);
v___x_323_ = ((size_t)1ULL);
v___x_324_ = lean_usize_sub(v___x_322_, v___x_323_);
v___x_325_ = lean_usize_land(v___x_321_, v___x_324_);
v___x_326_ = lean_array_uget_borrowed(v_x_302_, v___x_325_);
lean_inc(v___x_326_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 2, v___x_326_);
v___x_328_ = v___x_308_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_key_304_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_value_305_);
lean_ctor_set(v_reuseFailAlloc_331_, 2, v___x_326_);
v___x_328_ = v_reuseFailAlloc_331_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_329_; 
v___x_329_ = lean_array_uset(v_x_302_, v___x_325_, v___x_328_);
v_x_302_ = v___x_329_;
v_x_303_ = v_tail_306_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6___redArg(lean_object* v_i_333_, lean_object* v_source_334_, lean_object* v_target_335_){
_start:
{
lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_336_ = lean_array_get_size(v_source_334_);
v___x_337_ = lean_nat_dec_lt(v_i_333_, v___x_336_);
if (v___x_337_ == 0)
{
lean_dec_ref(v_source_334_);
lean_dec(v_i_333_);
return v_target_335_;
}
else
{
lean_object* v_es_338_; lean_object* v___x_339_; lean_object* v_source_340_; lean_object* v_target_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v_es_338_ = lean_array_fget(v_source_334_, v_i_333_);
v___x_339_ = lean_box(0);
v_source_340_ = lean_array_fset(v_source_334_, v_i_333_, v___x_339_);
v_target_341_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6_spec__7___redArg(v_target_335_, v_es_338_);
v___x_342_ = lean_unsigned_to_nat(1u);
v___x_343_ = lean_nat_add(v_i_333_, v___x_342_);
lean_dec(v_i_333_);
v_i_333_ = v___x_343_;
v_source_334_ = v_source_340_;
v_target_335_ = v_target_341_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5___redArg(lean_object* v_data_345_){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v_nbuckets_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_346_ = lean_array_get_size(v_data_345_);
v___x_347_ = lean_unsigned_to_nat(2u);
v_nbuckets_348_ = lean_nat_mul(v___x_346_, v___x_347_);
v___x_349_ = lean_unsigned_to_nat(0u);
v___x_350_ = lean_box(0);
v___x_351_ = lean_mk_array(v_nbuckets_348_, v___x_350_);
v___x_352_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6___redArg(v___x_349_, v_data_345_, v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4___redArg(lean_object* v_m_353_, lean_object* v_a_354_, lean_object* v_b_355_){
_start:
{
lean_object* v_size_356_; lean_object* v_buckets_357_; lean_object* v___x_358_; size_t v___x_359_; uint64_t v___x_360_; uint64_t v___x_361_; uint64_t v___x_362_; uint64_t v___x_363_; uint64_t v___x_364_; uint64_t v_fold_365_; uint64_t v___x_366_; uint64_t v___x_367_; uint64_t v___x_368_; size_t v___x_369_; size_t v___x_370_; size_t v___x_371_; size_t v___x_372_; size_t v___x_373_; lean_object* v_bkt_374_; uint8_t v___x_375_; 
v_size_356_ = lean_ctor_get(v_m_353_, 0);
v_buckets_357_ = lean_ctor_get(v_m_353_, 1);
v___x_358_ = lean_array_get_size(v_buckets_357_);
v___x_359_ = lean_ptr_addr(v_a_354_);
v___x_360_ = lean_usize_to_uint64(v___x_359_);
v___x_361_ = 11ULL;
v___x_362_ = lean_uint64_mix_hash(v___x_360_, v___x_361_);
v___x_363_ = 32ULL;
v___x_364_ = lean_uint64_shift_right(v___x_362_, v___x_363_);
v_fold_365_ = lean_uint64_xor(v___x_362_, v___x_364_);
v___x_366_ = 16ULL;
v___x_367_ = lean_uint64_shift_right(v_fold_365_, v___x_366_);
v___x_368_ = lean_uint64_xor(v_fold_365_, v___x_367_);
v___x_369_ = lean_uint64_to_usize(v___x_368_);
v___x_370_ = lean_usize_of_nat(v___x_358_);
v___x_371_ = ((size_t)1ULL);
v___x_372_ = lean_usize_sub(v___x_370_, v___x_371_);
v___x_373_ = lean_usize_land(v___x_369_, v___x_372_);
v_bkt_374_ = lean_array_uget_borrowed(v_buckets_357_, v___x_373_);
v___x_375_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(v_a_354_, v_bkt_374_);
if (v___x_375_ == 0)
{
lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_396_; 
lean_inc_ref(v_buckets_357_);
lean_inc(v_size_356_);
v_isSharedCheck_396_ = !lean_is_exclusive(v_m_353_);
if (v_isSharedCheck_396_ == 0)
{
lean_object* v_unused_397_; lean_object* v_unused_398_; 
v_unused_397_ = lean_ctor_get(v_m_353_, 1);
lean_dec(v_unused_397_);
v_unused_398_ = lean_ctor_get(v_m_353_, 0);
lean_dec(v_unused_398_);
v___x_377_ = v_m_353_;
v_isShared_378_ = v_isSharedCheck_396_;
goto v_resetjp_376_;
}
else
{
lean_dec(v_m_353_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_396_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; lean_object* v_size_x27_380_; lean_object* v___x_381_; lean_object* v_buckets_x27_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_379_ = lean_unsigned_to_nat(1u);
v_size_x27_380_ = lean_nat_add(v_size_356_, v___x_379_);
lean_dec(v_size_356_);
lean_inc(v_bkt_374_);
v___x_381_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_381_, 0, v_a_354_);
lean_ctor_set(v___x_381_, 1, v_b_355_);
lean_ctor_set(v___x_381_, 2, v_bkt_374_);
v_buckets_x27_382_ = lean_array_uset(v_buckets_357_, v___x_373_, v___x_381_);
v___x_383_ = lean_unsigned_to_nat(4u);
v___x_384_ = lean_nat_mul(v_size_x27_380_, v___x_383_);
v___x_385_ = lean_unsigned_to_nat(3u);
v___x_386_ = lean_nat_div(v___x_384_, v___x_385_);
lean_dec(v___x_384_);
v___x_387_ = lean_array_get_size(v_buckets_x27_382_);
v___x_388_ = lean_nat_dec_le(v___x_386_, v___x_387_);
lean_dec(v___x_386_);
if (v___x_388_ == 0)
{
lean_object* v_val_389_; lean_object* v___x_391_; 
v_val_389_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5___redArg(v_buckets_x27_382_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 1, v_val_389_);
lean_ctor_set(v___x_377_, 0, v_size_x27_380_);
v___x_391_ = v___x_377_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_size_x27_380_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_val_389_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
else
{
lean_object* v___x_394_; 
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 1, v_buckets_x27_382_);
lean_ctor_set(v___x_377_, 0, v_size_x27_380_);
v___x_394_ = v___x_377_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_size_x27_380_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_buckets_x27_382_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
else
{
lean_dec(v_b_355_);
lean_dec_ref(v_a_354_);
return v_m_353_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg(lean_object* v_m_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_buckets_401_; lean_object* v___x_402_; size_t v___x_403_; uint64_t v___x_404_; uint64_t v___x_405_; uint64_t v___x_406_; uint64_t v___x_407_; uint64_t v___x_408_; uint64_t v_fold_409_; uint64_t v___x_410_; uint64_t v___x_411_; uint64_t v___x_412_; size_t v___x_413_; size_t v___x_414_; size_t v___x_415_; size_t v___x_416_; size_t v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v_buckets_401_ = lean_ctor_get(v_m_399_, 1);
v___x_402_ = lean_array_get_size(v_buckets_401_);
v___x_403_ = lean_ptr_addr(v_a_400_);
v___x_404_ = lean_usize_to_uint64(v___x_403_);
v___x_405_ = 11ULL;
v___x_406_ = lean_uint64_mix_hash(v___x_404_, v___x_405_);
v___x_407_ = 32ULL;
v___x_408_ = lean_uint64_shift_right(v___x_406_, v___x_407_);
v_fold_409_ = lean_uint64_xor(v___x_406_, v___x_408_);
v___x_410_ = 16ULL;
v___x_411_ = lean_uint64_shift_right(v_fold_409_, v___x_410_);
v___x_412_ = lean_uint64_xor(v_fold_409_, v___x_411_);
v___x_413_ = lean_uint64_to_usize(v___x_412_);
v___x_414_ = lean_usize_of_nat(v___x_402_);
v___x_415_ = ((size_t)1ULL);
v___x_416_ = lean_usize_sub(v___x_414_, v___x_415_);
v___x_417_ = lean_usize_land(v___x_413_, v___x_416_);
v___x_418_ = lean_array_uget_borrowed(v_buckets_401_, v___x_417_);
v___x_419_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(v_a_400_, v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg___boxed(lean_object* v_m_420_, lean_object* v_a_421_){
_start:
{
uint8_t v_res_422_; lean_object* v_r_423_; 
v_res_422_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg(v_m_420_, v_a_421_);
lean_dec_ref(v_a_421_);
lean_dec_ref(v_m_420_);
v_r_423_ = lean_box(v_res_422_);
return v_r_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_visit(lean_object* v_e_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; uint8_t v___x_463_; 
v___x_463_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg(v_a_426_, v_e_424_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; lean_object* v_env_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_464_ = lean_st_ref_get(v_a_430_);
v_env_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc_ref(v_env_465_);
lean_dec(v___x_464_);
v___x_466_ = lean_box(0);
lean_inc_ref_n(v_e_424_, 2);
v___x_467_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4___redArg(v_a_426_, v_e_424_, v___x_466_);
v___x_468_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f(v_env_465_, v_a_425_, v_e_424_);
if (lean_obj_tag(v___x_468_) == 1)
{
lean_object* v___x_469_; lean_object* v___x_470_; 
lean_dec_ref(v_e_424_);
v___x_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
lean_ctor_set(v___x_469_, 1, v___x_467_);
v___x_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
return v___x_470_;
}
else
{
uint8_t v___x_471_; 
lean_dec(v___x_468_);
v___x_471_ = l_Lean_Expr_hasLooseBVars(v_e_424_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; 
lean_inc_ref(v_e_424_);
v___x_472_ = l_Lean_Meta_isProof(v_e_424_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_483_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_483_ == 0)
{
v___x_475_ = v___x_472_;
v_isShared_476_ = v_isSharedCheck_483_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_472_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_483_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
uint8_t v___x_477_; 
v___x_477_ = lean_unbox(v_a_473_);
lean_dec(v_a_473_);
if (v___x_477_ == 0)
{
lean_del_object(v___x_475_);
v___y_433_ = v_a_425_;
v___y_434_ = v___x_467_;
v___y_435_ = v_a_427_;
v___y_436_ = v_a_428_;
v___y_437_ = v_a_429_;
v___y_438_ = v_a_430_;
goto v___jp_432_;
}
else
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
lean_dec_ref(v_e_424_);
v___x_478_ = lean_box(0);
v___x_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
lean_ctor_set(v___x_479_, 1, v___x_467_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v___x_479_);
v___x_481_ = v___x_475_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
else
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
lean_dec_ref(v___x_467_);
lean_dec_ref(v_e_424_);
v_a_484_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_472_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_472_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
else
{
v___y_433_ = v_a_425_;
v___y_434_ = v___x_467_;
v___y_435_ = v_a_427_;
v___y_436_ = v_a_428_;
v___y_437_ = v_a_429_;
v___y_438_ = v_a_430_;
goto v___jp_432_;
}
}
}
else
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
lean_dec_ref(v_e_424_);
v___x_492_ = lean_box(0);
v___x_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
lean_ctor_set(v___x_493_, 1, v_a_426_);
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
return v___x_494_;
}
v___jp_432_:
{
switch(lean_obj_tag(v_e_424_))
{
case 6:
{
lean_object* v_body_439_; 
v_body_439_ = lean_ctor_get(v_e_424_, 2);
lean_inc_ref(v_body_439_);
lean_dec_ref(v_e_424_);
v_e_424_ = v_body_439_;
v_a_425_ = v___y_433_;
v_a_426_ = v___y_434_;
v_a_427_ = v___y_435_;
v_a_428_ = v___y_436_;
v_a_429_ = v___y_437_;
v_a_430_ = v___y_438_;
goto _start;
}
case 11:
{
lean_object* v_struct_441_; 
v_struct_441_ = lean_ctor_get(v_e_424_, 2);
lean_inc_ref(v_struct_441_);
lean_dec_ref(v_e_424_);
v_e_424_ = v_struct_441_;
v_a_425_ = v___y_433_;
v_a_426_ = v___y_434_;
v_a_427_ = v___y_435_;
v_a_428_ = v___y_436_;
v_a_429_ = v___y_437_;
v_a_430_ = v___y_438_;
goto _start;
}
case 10:
{
lean_object* v_expr_443_; 
v_expr_443_ = lean_ctor_get(v_e_424_, 1);
lean_inc_ref(v_expr_443_);
lean_dec_ref(v_e_424_);
v_e_424_ = v_expr_443_;
v_a_425_ = v___y_433_;
v_a_426_ = v___y_434_;
v_a_427_ = v___y_435_;
v_a_428_ = v___y_436_;
v_a_429_ = v___y_437_;
v_a_430_ = v___y_438_;
goto _start;
}
case 7:
{
lean_object* v_binderType_445_; lean_object* v_body_446_; lean_object* v___x_447_; 
v_binderType_445_ = lean_ctor_get(v_e_424_, 1);
lean_inc_ref(v_binderType_445_);
v_body_446_ = lean_ctor_get(v_e_424_, 2);
lean_inc_ref(v_body_446_);
lean_dec_ref(v_e_424_);
v___x_447_ = l_Lean_Meta_FindSplitImpl_visit(v_binderType_445_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v_fst_449_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_a_448_);
v_fst_449_ = lean_ctor_get(v_a_448_, 0);
if (lean_obj_tag(v_fst_449_) == 0)
{
lean_object* v_snd_450_; 
lean_dec_ref(v___x_447_);
v_snd_450_ = lean_ctor_get(v_a_448_, 1);
lean_inc(v_snd_450_);
lean_dec(v_a_448_);
v_e_424_ = v_body_446_;
v_a_425_ = v___y_433_;
v_a_426_ = v_snd_450_;
v_a_427_ = v___y_435_;
v_a_428_ = v___y_436_;
v_a_429_ = v___y_437_;
v_a_430_ = v___y_438_;
goto _start;
}
else
{
lean_dec(v_a_448_);
lean_dec_ref(v_body_446_);
return v___x_447_;
}
}
else
{
lean_dec_ref(v_body_446_);
return v___x_447_;
}
}
case 8:
{
lean_object* v_value_452_; lean_object* v_body_453_; lean_object* v___x_454_; 
v_value_452_ = lean_ctor_get(v_e_424_, 2);
lean_inc_ref(v_value_452_);
v_body_453_ = lean_ctor_get(v_e_424_, 3);
lean_inc_ref(v_body_453_);
lean_dec_ref(v_e_424_);
v___x_454_ = l_Lean_Meta_FindSplitImpl_visit(v_value_452_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v_a_455_; lean_object* v_fst_456_; 
v_a_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc(v_a_455_);
v_fst_456_ = lean_ctor_get(v_a_455_, 0);
if (lean_obj_tag(v_fst_456_) == 0)
{
lean_object* v_snd_457_; 
lean_dec_ref(v___x_454_);
v_snd_457_ = lean_ctor_get(v_a_455_, 1);
lean_inc(v_snd_457_);
lean_dec(v_a_455_);
v_e_424_ = v_body_453_;
v_a_425_ = v___y_433_;
v_a_426_ = v_snd_457_;
v_a_427_ = v___y_435_;
v_a_428_ = v___y_436_;
v_a_429_ = v___y_437_;
v_a_430_ = v___y_438_;
goto _start;
}
else
{
lean_dec(v_a_455_);
lean_dec_ref(v_body_453_);
return v___x_454_;
}
}
else
{
lean_dec_ref(v_body_453_);
return v___x_454_;
}
}
case 5:
{
lean_object* v___x_459_; 
v___x_459_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f(v_e_424_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
return v___x_459_;
}
default: 
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
lean_dec_ref(v_e_424_);
v___x_460_ = lean_box(0);
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
lean_ctor_set(v___x_461_, 1, v___y_434_);
v___x_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
return v___x_462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(lean_object* v_upperBound_495_, lean_object* v_args_496_, lean_object* v_info_497_, lean_object* v_a_498_, lean_object* v_b_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v_a_508_; lean_object* v_snd_509_; lean_object* v_a_513_; lean_object* v_snd_514_; uint8_t v___x_518_; 
v___x_518_ = lean_nat_dec_lt(v_a_498_, v_upperBound_495_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; 
lean_dec(v_a_498_);
v___x_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_519_, 0, v_b_499_);
lean_ctor_set(v___x_519_, 1, v___y_501_);
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
return v___x_520_;
}
else
{
lean_object* v_paramInfo_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
lean_dec_ref(v_b_499_);
v_paramInfo_521_ = lean_ctor_get(v_info_497_, 0);
v___x_522_ = lean_box(0);
v___x_523_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0));
v___x_524_ = lean_array_fget_borrowed(v_args_496_, v_a_498_);
v___x_525_ = lean_array_get_size(v_paramInfo_521_);
v___x_526_ = lean_nat_dec_lt(v_a_498_, v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; 
lean_inc(v___x_524_);
v___x_527_ = l_Lean_Meta_FindSplitImpl_visit(v___x_524_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v_fst_529_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_a_528_);
lean_dec_ref(v___x_527_);
v_fst_529_ = lean_ctor_get(v_a_528_, 0);
if (lean_obj_tag(v_fst_529_) == 1)
{
lean_object* v_snd_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_538_; 
lean_inc_ref(v_fst_529_);
lean_dec(v_a_498_);
v_snd_530_ = lean_ctor_get(v_a_528_, 1);
v_isSharedCheck_538_ = !lean_is_exclusive(v_a_528_);
if (v_isSharedCheck_538_ == 0)
{
lean_object* v_unused_539_; 
v_unused_539_ = lean_ctor_get(v_a_528_, 0);
lean_dec(v_unused_539_);
v___x_532_ = v_a_528_;
v_isShared_533_ = v_isSharedCheck_538_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_snd_530_);
lean_dec(v_a_528_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_538_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_534_, 0, v_fst_529_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 1, v___x_522_);
lean_ctor_set(v___x_532_, 0, v___x_534_);
v___x_536_ = v___x_532_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v___x_522_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
v_a_508_ = v___x_536_;
v_snd_509_ = v_snd_530_;
goto v___jp_507_;
}
}
}
else
{
lean_object* v_snd_540_; 
v_snd_540_ = lean_ctor_get(v_a_528_, 1);
lean_inc(v_snd_540_);
lean_dec(v_a_528_);
v_a_513_ = v___x_523_;
v_snd_514_ = v_snd_540_;
goto v___jp_512_;
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec(v_a_498_);
v_a_541_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_527_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_527_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
else
{
lean_object* v___x_549_; uint8_t v_isProp_550_; 
v___x_549_ = lean_array_fget_borrowed(v_paramInfo_521_, v_a_498_);
v_isProp_550_ = lean_ctor_get_uint8(v___x_549_, sizeof(void*)*1 + 2);
if (v_isProp_550_ == 0)
{
uint8_t v___x_551_; 
v___x_551_ = l_Lean_Meta_ParamInfo_isExplicit(v___x_549_);
if (v___x_551_ == 0)
{
v_a_513_ = v___x_523_;
v_snd_514_ = v___y_501_;
goto v___jp_512_;
}
else
{
lean_object* v___x_552_; 
lean_inc(v___x_524_);
v___x_552_ = l_Lean_Meta_FindSplitImpl_visit(v___x_524_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v_fst_554_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_553_);
lean_dec_ref(v___x_552_);
v_fst_554_ = lean_ctor_get(v_a_553_, 0);
if (lean_obj_tag(v_fst_554_) == 1)
{
lean_object* v_snd_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_563_; 
lean_inc_ref(v_fst_554_);
lean_dec(v_a_498_);
v_snd_555_ = lean_ctor_get(v_a_553_, 1);
v_isSharedCheck_563_ = !lean_is_exclusive(v_a_553_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; 
v_unused_564_ = lean_ctor_get(v_a_553_, 0);
lean_dec(v_unused_564_);
v___x_557_ = v_a_553_;
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_snd_555_);
lean_dec(v_a_553_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_559_, 0, v_fst_554_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 1, v___x_522_);
lean_ctor_set(v___x_557_, 0, v___x_559_);
v___x_561_ = v___x_557_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v___x_522_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
v_a_508_ = v___x_561_;
v_snd_509_ = v_snd_555_;
goto v___jp_507_;
}
}
}
else
{
lean_object* v_snd_565_; 
v_snd_565_ = lean_ctor_get(v_a_553_, 1);
lean_inc(v_snd_565_);
lean_dec(v_a_553_);
v_a_513_ = v___x_523_;
v_snd_514_ = v_snd_565_;
goto v___jp_512_;
}
}
else
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
lean_dec(v_a_498_);
v_a_566_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_573_ == 0)
{
v___x_568_ = v___x_552_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_552_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_566_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
}
else
{
v_a_513_ = v___x_523_;
v_snd_514_ = v___y_501_;
goto v___jp_512_;
}
}
}
v___jp_507_:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v_a_508_);
lean_ctor_set(v___x_510_, 1, v_snd_509_);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
v___jp_512_:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_unsigned_to_nat(1u);
v___x_516_ = lean_nat_add(v_a_498_, v___x_515_);
lean_dec(v_a_498_);
lean_inc_ref(v_a_513_);
v_a_498_ = v___x_516_;
v_b_499_ = v_a_513_;
v___y_501_ = v_snd_514_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1(lean_object* v_x_578_, lean_object* v_x_579_, lean_object* v_x_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v_info_589_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; 
if (lean_obj_tag(v_x_578_) == 5)
{
lean_object* v_fn_630_; lean_object* v_arg_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v_fn_630_ = lean_ctor_get(v_x_578_, 0);
lean_inc_ref(v_fn_630_);
v_arg_631_ = lean_ctor_get(v_x_578_, 1);
lean_inc_ref(v_arg_631_);
lean_dec_ref(v_x_578_);
v___x_632_ = lean_array_set(v_x_579_, v_x_580_, v_arg_631_);
v___x_633_ = lean_unsigned_to_nat(1u);
v___x_634_ = lean_nat_sub(v_x_580_, v___x_633_);
lean_dec(v_x_580_);
v_x_578_ = v_fn_630_;
v_x_579_ = v___x_632_;
v_x_580_ = v___x_634_;
goto _start;
}
else
{
uint8_t v___x_636_; 
lean_dec(v_x_580_);
v___x_636_ = l_Lean_Expr_hasLooseBVars(v_x_578_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = lean_box(0);
lean_inc_ref(v_x_578_);
v___x_638_ = l_Lean_Meta_getFunInfo(v_x_578_, v___x_637_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
lean_dec_ref(v___x_638_);
v_info_589_ = v_a_639_;
v___y_590_ = v___y_581_;
v___y_591_ = v___y_582_;
v___y_592_ = v___y_583_;
v___y_593_ = v___y_584_;
v___y_594_ = v___y_585_;
v___y_595_ = v___y_586_;
goto v___jp_588_;
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec_ref(v___y_582_);
lean_dec_ref(v_x_579_);
lean_dec_ref(v_x_578_);
v_a_640_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_638_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_638_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
else
{
lean_object* v___x_648_; 
v___x_648_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___closed__1));
v_info_589_ = v___x_648_;
v___y_590_ = v___y_581_;
v___y_591_ = v___y_582_;
v___y_592_ = v___y_583_;
v___y_593_ = v___y_584_;
v___y_594_ = v___y_585_;
v___y_595_ = v___y_586_;
goto v___jp_588_;
}
}
v___jp_588_:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_596_ = lean_array_get_size(v_x_579_);
v___x_597_ = lean_unsigned_to_nat(0u);
v___x_598_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0));
v___x_599_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(v___x_596_, v_x_579_, v_info_589_, v___x_597_, v___x_598_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
lean_dec_ref(v_info_589_);
lean_dec_ref(v_x_579_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_621_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_621_ == 0)
{
v___x_602_ = v___x_599_;
v_isShared_603_ = v_isSharedCheck_621_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_599_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_621_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v_fst_604_; lean_object* v_fst_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_619_; 
v_fst_604_ = lean_ctor_get(v_a_600_, 0);
lean_inc(v_fst_604_);
v_fst_605_ = lean_ctor_get(v_fst_604_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v_fst_604_);
if (v_isSharedCheck_619_ == 0)
{
lean_object* v_unused_620_; 
v_unused_620_ = lean_ctor_get(v_fst_604_, 1);
lean_dec(v_unused_620_);
v___x_607_ = v_fst_604_;
v_isShared_608_ = v_isSharedCheck_619_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_fst_605_);
lean_dec(v_fst_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_619_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
if (lean_obj_tag(v_fst_605_) == 0)
{
lean_object* v_snd_609_; lean_object* v___x_610_; 
lean_del_object(v___x_607_);
lean_del_object(v___x_602_);
v_snd_609_ = lean_ctor_get(v_a_600_, 1);
lean_inc(v_snd_609_);
lean_dec(v_a_600_);
v___x_610_ = l_Lean_Meta_FindSplitImpl_visit(v_x_578_, v___y_590_, v_snd_609_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
return v___x_610_;
}
else
{
lean_object* v_snd_611_; lean_object* v_val_612_; lean_object* v___x_614_; 
lean_dec_ref(v_x_578_);
v_snd_611_ = lean_ctor_get(v_a_600_, 1);
lean_inc(v_snd_611_);
lean_dec(v_a_600_);
v_val_612_ = lean_ctor_get(v_fst_605_, 0);
lean_inc(v_val_612_);
lean_dec_ref(v_fst_605_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 1, v_snd_611_);
lean_ctor_set(v___x_607_, 0, v_val_612_);
v___x_614_ = v___x_607_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_val_612_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_snd_611_);
v___x_614_ = v_reuseFailAlloc_618_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_616_; 
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v___x_614_);
v___x_616_ = v___x_602_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
}
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_dec_ref(v_x_578_);
v_a_622_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_599_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_599_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f(lean_object* v_e_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
lean_object* v_dummy_657_; lean_object* v_nargs_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v_dummy_657_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0);
v_nargs_658_ = l_Lean_Expr_getAppNumArgs(v_e_649_);
lean_inc(v_nargs_658_);
v___x_659_ = lean_mk_array(v_nargs_658_, v_dummy_657_);
v___x_660_ = lean_unsigned_to_nat(1u);
v___x_661_ = lean_nat_sub(v_nargs_658_, v___x_660_);
lean_dec(v_nargs_658_);
v___x_662_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1(v_e_649_, v___x_659_, v___x_661_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f___boxed(lean_object* v_e_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f(v_e_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec_ref(v_a_664_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___boxed(lean_object* v_x_672_, lean_object* v_x_673_, lean_object* v_x_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1(v_x_672_, v_x_673_, v_x_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec_ref(v___y_675_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg___boxed(lean_object* v_upperBound_683_, lean_object* v_args_684_, lean_object* v_info_685_, lean_object* v_a_686_, lean_object* v_b_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(v_upperBound_683_, v_args_684_, v_info_685_, v_a_686_, v_b_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec_ref(v___y_688_);
lean_dec_ref(v_info_685_);
lean_dec_ref(v_args_684_);
lean_dec(v_upperBound_683_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_visit___boxed(lean_object* v_e_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_Meta_FindSplitImpl_visit(v_e_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_);
lean_dec(v_a_702_);
lean_dec_ref(v_a_701_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec_ref(v_a_697_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0(lean_object* v_upperBound_705_, lean_object* v_args_706_, lean_object* v_info_707_, lean_object* v_inst_708_, lean_object* v_R_709_, lean_object* v_a_710_, lean_object* v_b_711_, lean_object* v_c_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(v_upperBound_705_, v_args_706_, v_info_707_, v_a_710_, v_b_711_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___boxed(lean_object* v_upperBound_721_, lean_object* v_args_722_, lean_object* v_info_723_, lean_object* v_inst_724_, lean_object* v_R_725_, lean_object* v_a_726_, lean_object* v_b_727_, lean_object* v_c_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0(v_upperBound_721_, v_args_722_, v_info_723_, v_inst_724_, v_R_725_, v_a_726_, v_b_727_, v_c_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec_ref(v___y_729_);
lean_dec_ref(v_info_723_);
lean_dec_ref(v_args_722_);
lean_dec(v_upperBound_721_);
return v_res_736_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3(lean_object* v_00_u03b2_737_, lean_object* v_m_738_, lean_object* v_a_739_){
_start:
{
uint8_t v___x_740_; 
v___x_740_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg(v_m_738_, v_a_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___boxed(lean_object* v_00_u03b2_741_, lean_object* v_m_742_, lean_object* v_a_743_){
_start:
{
uint8_t v_res_744_; lean_object* v_r_745_; 
v_res_744_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3(v_00_u03b2_741_, v_m_742_, v_a_743_);
lean_dec_ref(v_a_743_);
lean_dec_ref(v_m_742_);
v_r_745_ = lean_box(v_res_744_);
return v_r_745_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4(lean_object* v_00_u03b2_746_, lean_object* v_m_747_, lean_object* v_a_748_, lean_object* v_b_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4___redArg(v_m_747_, v_a_748_, v_b_749_);
return v___x_750_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3(lean_object* v_00_u03b2_751_, lean_object* v_a_752_, lean_object* v_x_753_){
_start:
{
uint8_t v___x_754_; 
v___x_754_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(v_a_752_, v_x_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___boxed(lean_object* v_00_u03b2_755_, lean_object* v_a_756_, lean_object* v_x_757_){
_start:
{
uint8_t v_res_758_; lean_object* v_r_759_; 
v_res_758_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3(v_00_u03b2_755_, v_a_756_, v_x_757_);
lean_dec(v_x_757_);
lean_dec_ref(v_a_756_);
v_r_759_ = lean_box(v_res_758_);
return v_r_759_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5(lean_object* v_00_u03b2_760_, lean_object* v_data_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5___redArg(v_data_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_763_, lean_object* v_i_764_, lean_object* v_source_765_, lean_object* v_target_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6___redArg(v_i_764_, v_source_765_, v_target_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_768_, lean_object* v_x_769_, lean_object* v_x_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6_spec__7___redArg(v_x_769_, v_x_770_);
return v___x_771_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = lean_unsigned_to_nat(64u);
v___x_773_ = l_Lean_mkPtrSet___redArg(v___x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1(uint8_t v_kind_774_, lean_object* v_exceptionSet_775_, lean_object* v_e_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_782_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_782_, 0, v_exceptionSet_775_);
lean_ctor_set_uint8(v___x_782_, sizeof(void*)*1, v_kind_774_);
v___x_783_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0);
v___x_784_ = l_Lean_Meta_FindSplitImpl_visit(v_e_776_, v___x_782_, v___x_783_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
lean_dec_ref(v___x_782_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_793_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_793_ == 0)
{
v___x_787_ = v___x_784_;
v_isShared_788_ = v_isSharedCheck_793_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_793_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v_fst_789_; lean_object* v___x_791_; 
v_fst_789_ = lean_ctor_get(v_a_785_, 0);
lean_inc(v_fst_789_);
lean_dec(v_a_785_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v_fst_789_);
v___x_791_ = v___x_787_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_fst_789_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
v_a_794_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_784_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_784_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___boxed(lean_object* v_kind_802_, lean_object* v_exceptionSet_803_, lean_object* v_e_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
uint8_t v_kind_boxed_810_; lean_object* v_res_811_; 
v_kind_boxed_810_ = lean_unbox(v_kind_802_);
v_res_811_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1(v_kind_boxed_810_, v_exceptionSet_803_, v_e_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(lean_object* v_msgData_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v___x_818_; lean_object* v_env_819_; lean_object* v___x_820_; lean_object* v_mctx_821_; lean_object* v_lctx_822_; lean_object* v_options_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_818_ = lean_st_ref_get(v___y_816_);
v_env_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc_ref(v_env_819_);
lean_dec(v___x_818_);
v___x_820_ = lean_st_ref_get(v___y_814_);
v_mctx_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc_ref(v_mctx_821_);
lean_dec(v___x_820_);
v_lctx_822_ = lean_ctor_get(v___y_813_, 2);
v_options_823_ = lean_ctor_get(v___y_815_, 2);
lean_inc_ref(v_options_823_);
lean_inc_ref(v_lctx_822_);
v___x_824_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_824_, 0, v_env_819_);
lean_ctor_set(v___x_824_, 1, v_mctx_821_);
lean_ctor_set(v___x_824_, 2, v_lctx_822_);
lean_ctor_set(v___x_824_, 3, v_options_823_);
v___x_825_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
lean_ctor_set(v___x_825_, 1, v_msgData_812_);
v___x_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0___boxed(lean_object* v_msgData_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(v_msgData_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
return v_res_833_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_834_; double v___x_835_; 
v___x_834_ = lean_unsigned_to_nat(0u);
v___x_835_ = lean_float_of_nat(v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(lean_object* v_cls_839_, lean_object* v_msg_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_ref_846_; lean_object* v___x_847_; lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_892_; 
v_ref_846_ = lean_ctor_get(v___y_843_, 5);
v___x_847_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(v_msg_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
v_a_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_892_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_892_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_892_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_852_; lean_object* v_traceState_853_; lean_object* v_env_854_; lean_object* v_nextMacroScope_855_; lean_object* v_ngen_856_; lean_object* v_auxDeclNGen_857_; lean_object* v_cache_858_; lean_object* v_messages_859_; lean_object* v_infoState_860_; lean_object* v_snapshotTasks_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_891_; 
v___x_852_ = lean_st_ref_take(v___y_844_);
v_traceState_853_ = lean_ctor_get(v___x_852_, 4);
v_env_854_ = lean_ctor_get(v___x_852_, 0);
v_nextMacroScope_855_ = lean_ctor_get(v___x_852_, 1);
v_ngen_856_ = lean_ctor_get(v___x_852_, 2);
v_auxDeclNGen_857_ = lean_ctor_get(v___x_852_, 3);
v_cache_858_ = lean_ctor_get(v___x_852_, 5);
v_messages_859_ = lean_ctor_get(v___x_852_, 6);
v_infoState_860_ = lean_ctor_get(v___x_852_, 7);
v_snapshotTasks_861_ = lean_ctor_get(v___x_852_, 8);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_891_ == 0)
{
v___x_863_ = v___x_852_;
v_isShared_864_ = v_isSharedCheck_891_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_snapshotTasks_861_);
lean_inc(v_infoState_860_);
lean_inc(v_messages_859_);
lean_inc(v_cache_858_);
lean_inc(v_traceState_853_);
lean_inc(v_auxDeclNGen_857_);
lean_inc(v_ngen_856_);
lean_inc(v_nextMacroScope_855_);
lean_inc(v_env_854_);
lean_dec(v___x_852_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_891_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
uint64_t v_tid_865_; lean_object* v_traces_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_890_; 
v_tid_865_ = lean_ctor_get_uint64(v_traceState_853_, sizeof(void*)*1);
v_traces_866_ = lean_ctor_get(v_traceState_853_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v_traceState_853_);
if (v_isSharedCheck_890_ == 0)
{
v___x_868_ = v_traceState_853_;
v_isShared_869_ = v_isSharedCheck_890_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_traces_866_);
lean_dec(v_traceState_853_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_890_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; double v___x_871_; uint8_t v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_870_ = lean_box(0);
v___x_871_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0);
v___x_872_ = 0;
v___x_873_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__1));
v___x_874_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_874_, 0, v_cls_839_);
lean_ctor_set(v___x_874_, 1, v___x_870_);
lean_ctor_set(v___x_874_, 2, v___x_873_);
lean_ctor_set_float(v___x_874_, sizeof(void*)*3, v___x_871_);
lean_ctor_set_float(v___x_874_, sizeof(void*)*3 + 8, v___x_871_);
lean_ctor_set_uint8(v___x_874_, sizeof(void*)*3 + 16, v___x_872_);
v___x_875_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__2));
v___x_876_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_876_, 0, v___x_874_);
lean_ctor_set(v___x_876_, 1, v_a_848_);
lean_ctor_set(v___x_876_, 2, v___x_875_);
lean_inc(v_ref_846_);
v___x_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_877_, 0, v_ref_846_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = l_Lean_PersistentArray_push___redArg(v_traces_866_, v___x_877_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_878_);
v___x_880_ = v___x_868_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_878_);
lean_ctor_set_uint64(v_reuseFailAlloc_889_, sizeof(void*)*1, v_tid_865_);
v___x_880_ = v_reuseFailAlloc_889_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_882_; 
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 4, v___x_880_);
v___x_882_ = v___x_863_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_env_854_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_nextMacroScope_855_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v_ngen_856_);
lean_ctor_set(v_reuseFailAlloc_888_, 3, v_auxDeclNGen_857_);
lean_ctor_set(v_reuseFailAlloc_888_, 4, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_888_, 5, v_cache_858_);
lean_ctor_set(v_reuseFailAlloc_888_, 6, v_messages_859_);
lean_ctor_set(v_reuseFailAlloc_888_, 7, v_infoState_860_);
lean_ctor_set(v_reuseFailAlloc_888_, 8, v_snapshotTasks_861_);
v___x_882_ = v_reuseFailAlloc_888_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_883_ = lean_st_ref_set(v___y_844_, v___x_882_);
v___x_884_ = lean_box(0);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_884_);
v___x_886_ = v___x_850_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___boxed(lean_object* v_cls_893_, lean_object* v_msg_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v_cls_893_, v_msg_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
return v_res_900_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_909_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__2));
v___x_910_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4));
v___x_911_ = l_Lean_Name_append(v___x_910_, v___x_909_);
return v___x_911_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__6));
v___x_914_ = l_Lean_stringToMessageData(v___x_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f(uint8_t v_kind_915_, lean_object* v_exceptionSet_916_, lean_object* v_e_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1(v_kind_915_, v_exceptionSet_916_, v_e_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_a_924_);
if (lean_obj_tag(v_a_924_) == 1)
{
lean_object* v_options_925_; uint8_t v_hasTrace_926_; 
v_options_925_ = lean_ctor_get(v_a_920_, 2);
v_hasTrace_926_ = lean_ctor_get_uint8(v_options_925_, sizeof(void*)*1);
if (v_hasTrace_926_ == 0)
{
lean_dec_ref(v_a_924_);
return v___x_923_;
}
else
{
lean_object* v_val_927_; lean_object* v_inheritedTraceOptions_928_; lean_object* v___x_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v_val_927_ = lean_ctor_get(v_a_924_, 0);
v_inheritedTraceOptions_928_ = lean_ctor_get(v_a_920_, 13);
v___x_929_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__2));
v___x_930_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5);
v___x_931_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_928_, v_options_925_, v___x_930_);
if (v___x_931_ == 0)
{
lean_dec_ref(v_a_924_);
return v___x_923_;
}
else
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
lean_dec_ref(v___x_923_);
v___x_932_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7);
lean_inc(v_val_927_);
v___x_933_ = l_Lean_indentExpr(v_val_927_);
v___x_934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_932_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_929_, v___x_934_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_942_ == 0)
{
lean_object* v_unused_943_; 
v_unused_943_ = lean_ctor_get(v___x_935_, 0);
lean_dec(v_unused_943_);
v___x_937_ = v___x_935_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_dec(v___x_935_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v_a_924_);
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_924_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
else
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
lean_dec_ref(v_a_924_);
v_a_944_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_951_ == 0)
{
v___x_946_ = v___x_935_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_935_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_944_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
}
}
else
{
lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_959_; 
lean_dec(v_a_924_);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_959_ == 0)
{
lean_object* v_unused_960_; 
v_unused_960_ = lean_ctor_get(v___x_923_, 0);
lean_dec(v_unused_960_);
v___x_953_ = v___x_923_;
v_isShared_954_ = v_isSharedCheck_959_;
goto v_resetjp_952_;
}
else
{
lean_dec(v___x_923_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_959_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_955_; lean_object* v___x_957_; 
v___x_955_ = lean_box(0);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 0, v___x_955_);
v___x_957_ = v___x_953_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_955_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
else
{
return v___x_923_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___boxed(lean_object* v_kind_961_, lean_object* v_exceptionSet_962_, lean_object* v_e_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
uint8_t v_kind_boxed_969_; lean_object* v_res_970_; 
v_kind_boxed_969_ = lean_unbox(v_kind_961_);
v_res_970_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f(v_kind_boxed_969_, v_exceptionSet_962_, v_e_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
lean_dec(v_a_967_);
lean_dec_ref(v_a_966_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(uint8_t v_kind_971_, lean_object* v_exceptionSet_972_, lean_object* v_e_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_){
_start:
{
lean_object* v___y_980_; lean_object* v___x_983_; 
lean_inc_ref(v_exceptionSet_972_);
v___x_983_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f(v_kind_971_, v_exceptionSet_972_, v_e_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
if (lean_obj_tag(v_a_984_) == 1)
{
lean_object* v_val_985_; uint8_t v___y_987_; uint8_t v___x_993_; 
v_val_985_ = lean_ctor_get(v_a_984_, 0);
lean_inc(v_val_985_);
lean_dec_ref(v_a_984_);
v___x_993_ = l_Lean_Expr_isIte(v_val_985_);
if (v___x_993_ == 0)
{
uint8_t v___x_994_; 
v___x_994_ = l_Lean_Expr_isDIte(v_val_985_);
v___y_987_ = v___x_994_;
goto v___jp_986_;
}
else
{
v___y_987_ = v___x_993_;
goto v___jp_986_;
}
v___jp_986_:
{
if (v___y_987_ == 0)
{
lean_dec(v_val_985_);
lean_dec_ref(v_exceptionSet_972_);
return v___x_983_;
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
lean_dec_ref(v___x_983_);
v___x_988_ = lean_unsigned_to_nat(3u);
v___x_989_ = l_Lean_Expr_getRevArg_x21(v_val_985_, v___x_988_);
v___x_990_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(v_kind_971_, v_exceptionSet_972_, v___x_989_, v_a_974_, v_a_975_, v_a_976_, v_a_977_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
lean_dec_ref(v___x_990_);
if (lean_obj_tag(v_a_991_) == 0)
{
v___y_980_ = v_val_985_;
goto v___jp_979_;
}
else
{
lean_object* v_val_992_; 
lean_dec(v_val_985_);
v_val_992_ = lean_ctor_get(v_a_991_, 0);
lean_inc(v_val_992_);
lean_dec_ref(v_a_991_);
v___y_980_ = v_val_992_;
goto v___jp_979_;
}
}
else
{
lean_dec(v_val_985_);
return v___x_990_;
}
}
}
}
else
{
lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1002_; 
lean_dec(v_a_984_);
lean_dec_ref(v_exceptionSet_972_);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1002_ == 0)
{
lean_object* v_unused_1003_; 
v_unused_1003_ = lean_ctor_get(v___x_983_, 0);
lean_dec(v_unused_1003_);
v___x_996_ = v___x_983_;
v_isShared_997_ = v_isSharedCheck_1002_;
goto v_resetjp_995_;
}
else
{
lean_dec(v___x_983_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1002_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_998_; lean_object* v___x_1000_; 
v___x_998_ = lean_box(0);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_998_);
v___x_1000_ = v___x_996_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_998_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
else
{
lean_dec_ref(v_exceptionSet_972_);
return v___x_983_;
}
v___jp_979_:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_981_, 0, v___y_980_);
v___x_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
return v___x_982_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go___boxed(lean_object* v_kind_1004_, lean_object* v_exceptionSet_1005_, lean_object* v_e_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
uint8_t v_kind_boxed_1012_; lean_object* v_res_1013_; 
v_kind_boxed_1012_ = lean_unbox(v_kind_1004_);
v_res_1013_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(v_kind_boxed_1012_, v_exceptionSet_1005_, v_e_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(lean_object* v_e_1014_, lean_object* v___y_1015_){
_start:
{
uint8_t v___x_1017_; 
v___x_1017_ = l_Lean_Expr_hasMVar(v_e_1014_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1018_, 0, v_e_1014_);
return v___x_1018_;
}
else
{
lean_object* v___x_1019_; lean_object* v_mctx_1020_; lean_object* v___x_1021_; lean_object* v_fst_1022_; lean_object* v_snd_1023_; lean_object* v___x_1024_; lean_object* v_cache_1025_; lean_object* v_zetaDeltaFVarIds_1026_; lean_object* v_postponed_1027_; lean_object* v_diag_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1037_; 
v___x_1019_ = lean_st_ref_get(v___y_1015_);
v_mctx_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc_ref(v_mctx_1020_);
lean_dec(v___x_1019_);
v___x_1021_ = l_Lean_instantiateMVarsCore(v_mctx_1020_, v_e_1014_);
v_fst_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_fst_1022_);
v_snd_1023_ = lean_ctor_get(v___x_1021_, 1);
lean_inc(v_snd_1023_);
lean_dec_ref(v___x_1021_);
v___x_1024_ = lean_st_ref_take(v___y_1015_);
v_cache_1025_ = lean_ctor_get(v___x_1024_, 1);
v_zetaDeltaFVarIds_1026_ = lean_ctor_get(v___x_1024_, 2);
v_postponed_1027_ = lean_ctor_get(v___x_1024_, 3);
v_diag_1028_ = lean_ctor_get(v___x_1024_, 4);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1037_ == 0)
{
lean_object* v_unused_1038_; 
v_unused_1038_ = lean_ctor_get(v___x_1024_, 0);
lean_dec(v_unused_1038_);
v___x_1030_ = v___x_1024_;
v_isShared_1031_ = v_isSharedCheck_1037_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_diag_1028_);
lean_inc(v_postponed_1027_);
lean_inc(v_zetaDeltaFVarIds_1026_);
lean_inc(v_cache_1025_);
lean_dec(v___x_1024_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1037_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v_snd_1023_);
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_snd_1023_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_cache_1025_);
lean_ctor_set(v_reuseFailAlloc_1036_, 2, v_zetaDeltaFVarIds_1026_);
lean_ctor_set(v_reuseFailAlloc_1036_, 3, v_postponed_1027_);
lean_ctor_set(v_reuseFailAlloc_1036_, 4, v_diag_1028_);
v___x_1033_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = lean_st_ref_set(v___y_1015_, v___x_1033_);
v___x_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1035_, 0, v_fst_1022_);
return v___x_1035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg___boxed(lean_object* v_e_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_1039_, v___y_1040_);
lean_dec(v___y_1040_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0(lean_object* v_e_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_1043_, v___y_1045_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___boxed(lean_object* v_e_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0(v_e_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f(lean_object* v_e_1057_, uint8_t v_kind_1058_, lean_object* v_exceptionSet_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v___x_1065_; lean_object* v_a_1066_; lean_object* v___x_1067_; 
v___x_1065_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_1057_, v_a_1061_);
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_a_1066_);
lean_dec_ref(v___x_1065_);
v___x_1067_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(v_kind_1058_, v_exceptionSet_1059_, v_a_1066_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f___boxed(lean_object* v_e_1068_, lean_object* v_kind_1069_, lean_object* v_exceptionSet_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_){
_start:
{
uint8_t v_kind_boxed_1076_; lean_object* v_res_1077_; 
v_kind_boxed_1076_ = lean_unbox(v_kind_1069_);
v_res_1077_ = l_Lean_Meta_findSplit_x3f(v_e_1068_, v_kind_boxed_1076_, v_exceptionSet_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
return v_res_1077_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1078_ = lean_box(0);
v___x_1079_ = lean_unsigned_to_nat(16u);
v___x_1080_ = lean_mk_array(v___x_1079_, v___x_1078_);
return v___x_1080_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1081_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0);
v___x_1082_ = lean_unsigned_to_nat(0u);
v___x_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
lean_ctor_set(v___x_1083_, 1, v___x_1081_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(lean_object* v_e_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
uint8_t v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1090_ = 0;
v___x_1091_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1);
v___x_1092_ = l_Lean_Meta_findSplit_x3f(v_e_1084_, v___x_1090_, v___x_1091_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1117_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1095_ = v___x_1092_;
v_isShared_1096_ = v_isSharedCheck_1117_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1092_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1117_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
if (lean_obj_tag(v_a_1093_) == 1)
{
lean_object* v_val_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1112_; 
v_val_1097_ = lean_ctor_get(v_a_1093_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v_a_1093_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1099_ = v_a_1093_;
v_isShared_1100_ = v_isSharedCheck_1112_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_val_1097_);
lean_dec(v_a_1093_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1112_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1107_; 
v___x_1101_ = lean_unsigned_to_nat(3u);
v___x_1102_ = l_Lean_Expr_getRevArg_x21(v_val_1097_, v___x_1101_);
v___x_1103_ = lean_unsigned_to_nat(2u);
v___x_1104_ = l_Lean_Expr_getRevArg_x21(v_val_1097_, v___x_1103_);
lean_dec(v_val_1097_);
v___x_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1102_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v___x_1105_);
v___x_1107_ = v___x_1099_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1105_);
v___x_1107_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1109_; 
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v___x_1107_);
v___x_1109_ = v___x_1095_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1107_);
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
else
{
lean_object* v___x_1113_; lean_object* v___x_1115_; 
lean_dec(v_a_1093_);
v___x_1113_ = lean_box(0);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v___x_1113_);
v___x_1115_ = v___x_1095_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
v_a_1118_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1092_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1092_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___boxed(lean_object* v_e_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(v_e_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec_ref(v_a_1127_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(lean_object* v_name_1133_, lean_object* v_decl_1134_, lean_object* v_ref_1135_){
_start:
{
lean_object* v_defValue_1137_; lean_object* v_descr_1138_; lean_object* v_deprecation_x3f_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v_defValue_1137_ = lean_ctor_get(v_decl_1134_, 0);
v_descr_1138_ = lean_ctor_get(v_decl_1134_, 1);
v_deprecation_x3f_1139_ = lean_ctor_get(v_decl_1134_, 2);
v___x_1140_ = lean_alloc_ctor(1, 0, 1);
v___x_1141_ = lean_unbox(v_defValue_1137_);
lean_ctor_set_uint8(v___x_1140_, 0, v___x_1141_);
lean_inc(v_deprecation_x3f_1139_);
lean_inc_ref(v_descr_1138_);
lean_inc_n(v_name_1133_, 2);
v___x_1142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1142_, 0, v_name_1133_);
lean_ctor_set(v___x_1142_, 1, v_ref_1135_);
lean_ctor_set(v___x_1142_, 2, v___x_1140_);
lean_ctor_set(v___x_1142_, 3, v_descr_1138_);
lean_ctor_set(v___x_1142_, 4, v_deprecation_x3f_1139_);
v___x_1143_ = lean_register_option(v_name_1133_, v___x_1142_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1151_; 
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1151_ == 0)
{
lean_object* v_unused_1152_; 
v_unused_1152_ = lean_ctor_get(v___x_1143_, 0);
lean_dec(v_unused_1152_);
v___x_1145_ = v___x_1143_;
v_isShared_1146_ = v_isSharedCheck_1151_;
goto v_resetjp_1144_;
}
else
{
lean_dec(v___x_1143_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1151_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1149_; 
lean_inc(v_defValue_1137_);
v___x_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1147_, 0, v_name_1133_);
lean_ctor_set(v___x_1147_, 1, v_defValue_1137_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1147_);
v___x_1149_ = v___x_1145_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec(v_name_1133_);
v_a_1153_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1143_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1143_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1161_, lean_object* v_decl_1162_, lean_object* v_ref_1163_, lean_object* v_a_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(v_name_1161_, v_decl_1162_, v_ref_1163_);
lean_dec_ref(v_decl_1162_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1184_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_));
v___x_1185_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_));
v___x_1186_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_));
v___x_1187_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(v___x_1184_, v___x_1185_, v___x_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4____boxed(lean_object* v_a_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_();
return v_res_1189_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1190_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0);
v___x_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0(lean_object* v_00_u03b2_1193_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1);
return v___x_1194_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1195_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0);
v___x_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1(lean_object* v_00_u03b2_1198_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1);
return v___x_1199_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__0(void){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_1200_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__1(void){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0(lean_box(0));
return v___x_1201_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__2(void){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1(lean_box(0));
return v___x_1202_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__3(void){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1203_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__4(void){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__3, &l_Lean_Meta_SplitIf_getSimpContext___closed__3_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__3);
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
return v___x_1205_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__5(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v_s_1210_; 
v___x_1206_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__4, &l_Lean_Meta_SplitIf_getSimpContext___closed__4_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__4);
v___x_1207_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__2, &l_Lean_Meta_SplitIf_getSimpContext___closed__2_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__2);
v___x_1208_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__1, &l_Lean_Meta_SplitIf_getSimpContext___closed__1_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__1);
v___x_1209_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__0, &l_Lean_Meta_SplitIf_getSimpContext___closed__0_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__0);
v_s_1210_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_s_1210_, 0, v___x_1209_);
lean_ctor_set(v_s_1210_, 1, v___x_1209_);
lean_ctor_set(v_s_1210_, 2, v___x_1208_);
lean_ctor_set(v_s_1210_, 3, v___x_1207_);
lean_ctor_set(v_s_1210_, 4, v___x_1208_);
lean_ctor_set(v_s_1210_, 5, v___x_1206_);
return v_s_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_getSimpContext(lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v_s_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; uint8_t v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v_s_1228_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__5, &l_Lean_Meta_SplitIf_getSimpContext___closed__5_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__5);
v___x_1229_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__7));
v___x_1230_ = 1;
v___x_1231_ = 0;
v___x_1232_ = lean_unsigned_to_nat(1000u);
v___x_1233_ = l_Lean_Meta_SimpTheorems_addConst(v_s_1228_, v___x_1229_, v___x_1230_, v___x_1231_, v___x_1232_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_a_1234_);
lean_dec_ref(v___x_1233_);
v___x_1235_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__9));
v___x_1236_ = l_Lean_Meta_SimpTheorems_addConst(v_a_1234_, v___x_1235_, v___x_1230_, v___x_1231_, v___x_1232_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_a_1237_);
lean_dec_ref(v___x_1236_);
v___x_1238_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__11));
v___x_1239_ = l_Lean_Meta_SimpTheorems_addConst(v_a_1237_, v___x_1238_, v___x_1230_, v___x_1231_, v___x_1232_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_a_1240_);
lean_dec_ref(v___x_1239_);
v___x_1241_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__13));
v___x_1242_ = l_Lean_Meta_SimpTheorems_addConst(v_a_1240_, v___x_1241_, v___x_1230_, v___x_1231_, v___x_1232_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v___x_1244_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_a_1243_);
lean_dec_ref(v___x_1242_);
v___x_1244_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_1226_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1246_; lean_object* v_maxSteps_1247_; lean_object* v_maxDischargeDepth_1248_; uint8_t v_contextual_1249_; uint8_t v_memoize_1250_; uint8_t v_singlePass_1251_; uint8_t v_zeta_1252_; uint8_t v_beta_1253_; uint8_t v_eta_1254_; uint8_t v_etaStruct_1255_; uint8_t v_iota_1256_; uint8_t v_proj_1257_; uint8_t v_decide_1258_; uint8_t v_arith_1259_; uint8_t v_autoUnfold_1260_; uint8_t v_failIfUnchanged_1261_; uint8_t v_ground_1262_; uint8_t v_unfoldPartialApp_1263_; uint8_t v_zetaDelta_1264_; uint8_t v_index_1265_; uint8_t v_implicitDefEqProofs_1266_; uint8_t v_zetaUnused_1267_; uint8_t v_catchRuntime_1268_; uint8_t v_zetaHave_1269_; uint8_t v_congrConsts_1270_; uint8_t v_bitVecOfNat_1271_; uint8_t v_warnExponents_1272_; uint8_t v_suggestions_1273_; lean_object* v_maxSuggestions_1274_; uint8_t v_locals_1275_; uint8_t v_instances_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref(v___x_1244_);
v___x_1246_ = l_Lean_Meta_Simp_neutralConfig;
v_maxSteps_1247_ = lean_ctor_get(v___x_1246_, 0);
v_maxDischargeDepth_1248_ = lean_ctor_get(v___x_1246_, 1);
v_contextual_1249_ = lean_ctor_get_uint8(v___x_1246_, sizeof(void*)*3);
v_memoize_1250_ = lean_ctor_get_uint8(v___x_1246_, sizeof(void*)*3 + 1);
v_singlePass_1251_ = lean_ctor_get_uint8(v___x_1246_, sizeof(void*)*3 + 2);
v_zeta_1252_ = lean_ctor_get_uint8(v___x_1246_, sizeof(void*)*3 + 3);
v_beta_1253_ = lean_ctor_get_uint8(v___x_1246_, sizeof(void*)*3 + 4);
v_eta_1254_ = lean_ctor_get_uint8(v___x_1246_, sizeof(void*)*3 + 5);
v_etaStruct_1255_ = lean_ctor_get_uint8(v___x_1246_, sizeof(void*)*3 + 6);
v_iota_1256_ = lean_ctor_get_uint8(v___x_1246_, sizeof(void*)*3 + 7);
v_proj_1257_ = lean_ctor_get_uint8(v___x_1246_, sizeof(void*)*3 + 8);
v_decide_1258_ = lean_ctor_get_uint8(v___x_1246_, sizeof(void*)*3 + 9);
v_arith_1259_ = lean_ctor_get_uint8(v___x_1246_, sizeof(void*)*3 + 10);
v_autoUnfold_1260_ = lean_ctor_get_uint8(v___x_1246_, sizeof(void*)*3 + 11);
v_failIfUnchanged_1261_ = lean_ctor_get_uint8(v___x_1246_, sizeof(void*)*3 + 13);
v_ground_1262_ = lean_ctor_get_uint8(v___x_1246_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_1263_ = lean_ctor_get_uint8(v___x_1246_, sizeof(void*)*3 + 15);
v_zetaDelta_1264_ = lean_ctor_get_uint8(v___x_1246_, sizeof(void*)*3 + 16);
v_index_1265_ = lean_ctor_get_uint8(v___x_1246_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_1266_ = lean_ctor_get_uint8(v___x_1246_, sizeof(void*)*3 + 18);
v_zetaUnused_1267_ = lean_ctor_get_uint8(v___x_1246_, sizeof(void*)*3 + 19);
v_catchRuntime_1268_ = lean_ctor_get_uint8(v___x_1246_, sizeof(void*)*3 + 20);
v_zetaHave_1269_ = lean_ctor_get_uint8(v___x_1246_, sizeof(void*)*3 + 21);
v_congrConsts_1270_ = lean_ctor_get_uint8(v___x_1246_, sizeof(void*)*3 + 23);
v_bitVecOfNat_1271_ = lean_ctor_get_uint8(v___x_1246_, sizeof(void*)*3 + 24);
v_warnExponents_1272_ = lean_ctor_get_uint8(v___x_1246_, sizeof(void*)*3 + 25);
v_suggestions_1273_ = lean_ctor_get_uint8(v___x_1246_, sizeof(void*)*3 + 26);
v_maxSuggestions_1274_ = lean_ctor_get(v___x_1246_, 2);
v_locals_1275_ = lean_ctor_get_uint8(v___x_1246_, sizeof(void*)*3 + 27);
v_instances_1276_ = lean_ctor_get_uint8(v___x_1246_, sizeof(void*)*3 + 28);
lean_inc(v_maxSuggestions_1274_);
lean_inc(v_maxDischargeDepth_1248_);
lean_inc(v_maxSteps_1247_);
v___x_1277_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1277_, 0, v_maxSteps_1247_);
lean_ctor_set(v___x_1277_, 1, v_maxDischargeDepth_1248_);
lean_ctor_set(v___x_1277_, 2, v_maxSuggestions_1274_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3, v_contextual_1249_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 1, v_memoize_1250_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 2, v_singlePass_1251_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 3, v_zeta_1252_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 4, v_beta_1253_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 5, v_eta_1254_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 6, v_etaStruct_1255_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 7, v_iota_1256_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 8, v_proj_1257_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 9, v_decide_1258_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 10, v_arith_1259_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 11, v_autoUnfold_1260_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 12, v___x_1231_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 13, v_failIfUnchanged_1261_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 14, v_ground_1262_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 15, v_unfoldPartialApp_1263_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 16, v_zetaDelta_1264_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 17, v_index_1265_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_1266_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 19, v_zetaUnused_1267_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 20, v_catchRuntime_1268_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 21, v_zetaHave_1269_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 22, v___x_1230_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 23, v_congrConsts_1270_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 24, v_bitVecOfNat_1271_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 25, v_warnExponents_1272_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 26, v_suggestions_1273_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 27, v_locals_1275_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 28, v_instances_1276_);
v___x_1278_ = lean_unsigned_to_nat(1u);
v___x_1279_ = lean_mk_empty_array_with_capacity(v___x_1278_);
v___x_1280_ = lean_array_push(v___x_1279_, v_a_1243_);
v___x_1281_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1277_, v___x_1280_, v_a_1245_, v_a_1223_, v_a_1225_, v_a_1226_);
return v___x_1281_;
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_dec(v_a_1243_);
v_a_1282_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1244_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1244_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
v_a_1290_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1242_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1242_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
v_a_1298_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1239_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1239_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
v_a_1306_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1236_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1236_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
v_a_1314_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1233_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1233_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_getSimpContext___boxed(lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec(v_a_1323_);
lean_dec_ref(v_a_1322_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_1332_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; lean_object* v___x_1336_; lean_object* v_maxSteps_1337_; lean_object* v_maxDischargeDepth_1338_; uint8_t v_contextual_1339_; uint8_t v_memoize_1340_; uint8_t v_singlePass_1341_; uint8_t v_zeta_1342_; uint8_t v_beta_1343_; uint8_t v_eta_1344_; uint8_t v_etaStruct_1345_; uint8_t v_iota_1346_; uint8_t v_proj_1347_; uint8_t v_decide_1348_; uint8_t v_arith_1349_; uint8_t v_autoUnfold_1350_; uint8_t v_failIfUnchanged_1351_; uint8_t v_ground_1352_; uint8_t v_unfoldPartialApp_1353_; uint8_t v_zetaDelta_1354_; uint8_t v_index_1355_; uint8_t v_implicitDefEqProofs_1356_; uint8_t v_zetaUnused_1357_; uint8_t v_catchRuntime_1358_; uint8_t v_zetaHave_1359_; uint8_t v_congrConsts_1360_; uint8_t v_bitVecOfNat_1361_; uint8_t v_warnExponents_1362_; uint8_t v_suggestions_1363_; lean_object* v_maxSuggestions_1364_; uint8_t v_locals_1365_; uint8_t v_instances_1366_; uint8_t v___x_1367_; uint8_t v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_a_1335_);
lean_dec_ref(v___x_1334_);
v___x_1336_ = l_Lean_Meta_Simp_neutralConfig;
v_maxSteps_1337_ = lean_ctor_get(v___x_1336_, 0);
v_maxDischargeDepth_1338_ = lean_ctor_get(v___x_1336_, 1);
v_contextual_1339_ = lean_ctor_get_uint8(v___x_1336_, sizeof(void*)*3);
v_memoize_1340_ = lean_ctor_get_uint8(v___x_1336_, sizeof(void*)*3 + 1);
v_singlePass_1341_ = lean_ctor_get_uint8(v___x_1336_, sizeof(void*)*3 + 2);
v_zeta_1342_ = lean_ctor_get_uint8(v___x_1336_, sizeof(void*)*3 + 3);
v_beta_1343_ = lean_ctor_get_uint8(v___x_1336_, sizeof(void*)*3 + 4);
v_eta_1344_ = lean_ctor_get_uint8(v___x_1336_, sizeof(void*)*3 + 5);
v_etaStruct_1345_ = lean_ctor_get_uint8(v___x_1336_, sizeof(void*)*3 + 6);
v_iota_1346_ = lean_ctor_get_uint8(v___x_1336_, sizeof(void*)*3 + 7);
v_proj_1347_ = lean_ctor_get_uint8(v___x_1336_, sizeof(void*)*3 + 8);
v_decide_1348_ = lean_ctor_get_uint8(v___x_1336_, sizeof(void*)*3 + 9);
v_arith_1349_ = lean_ctor_get_uint8(v___x_1336_, sizeof(void*)*3 + 10);
v_autoUnfold_1350_ = lean_ctor_get_uint8(v___x_1336_, sizeof(void*)*3 + 11);
v_failIfUnchanged_1351_ = lean_ctor_get_uint8(v___x_1336_, sizeof(void*)*3 + 13);
v_ground_1352_ = lean_ctor_get_uint8(v___x_1336_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_1353_ = lean_ctor_get_uint8(v___x_1336_, sizeof(void*)*3 + 15);
v_zetaDelta_1354_ = lean_ctor_get_uint8(v___x_1336_, sizeof(void*)*3 + 16);
v_index_1355_ = lean_ctor_get_uint8(v___x_1336_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_1356_ = lean_ctor_get_uint8(v___x_1336_, sizeof(void*)*3 + 18);
v_zetaUnused_1357_ = lean_ctor_get_uint8(v___x_1336_, sizeof(void*)*3 + 19);
v_catchRuntime_1358_ = lean_ctor_get_uint8(v___x_1336_, sizeof(void*)*3 + 20);
v_zetaHave_1359_ = lean_ctor_get_uint8(v___x_1336_, sizeof(void*)*3 + 21);
v_congrConsts_1360_ = lean_ctor_get_uint8(v___x_1336_, sizeof(void*)*3 + 23);
v_bitVecOfNat_1361_ = lean_ctor_get_uint8(v___x_1336_, sizeof(void*)*3 + 24);
v_warnExponents_1362_ = lean_ctor_get_uint8(v___x_1336_, sizeof(void*)*3 + 25);
v_suggestions_1363_ = lean_ctor_get_uint8(v___x_1336_, sizeof(void*)*3 + 26);
v_maxSuggestions_1364_ = lean_ctor_get(v___x_1336_, 2);
v_locals_1365_ = lean_ctor_get_uint8(v___x_1336_, sizeof(void*)*3 + 27);
v_instances_1366_ = lean_ctor_get_uint8(v___x_1336_, sizeof(void*)*3 + 28);
v___x_1367_ = 0;
v___x_1368_ = 1;
lean_inc(v_maxSuggestions_1364_);
lean_inc(v_maxDischargeDepth_1338_);
lean_inc(v_maxSteps_1337_);
v___x_1369_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1369_, 0, v_maxSteps_1337_);
lean_ctor_set(v___x_1369_, 1, v_maxDischargeDepth_1338_);
lean_ctor_set(v___x_1369_, 2, v_maxSuggestions_1364_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3, v_contextual_1339_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3 + 1, v_memoize_1340_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3 + 2, v_singlePass_1341_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3 + 3, v_zeta_1342_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3 + 4, v_beta_1343_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3 + 5, v_eta_1344_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3 + 6, v_etaStruct_1345_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3 + 7, v_iota_1346_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3 + 8, v_proj_1347_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3 + 9, v_decide_1348_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3 + 10, v_arith_1349_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3 + 11, v_autoUnfold_1350_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3 + 12, v___x_1367_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3 + 13, v_failIfUnchanged_1351_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3 + 14, v_ground_1352_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3 + 15, v_unfoldPartialApp_1353_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3 + 16, v_zetaDelta_1354_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3 + 17, v_index_1355_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_1356_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3 + 19, v_zetaUnused_1357_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3 + 20, v_catchRuntime_1358_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3 + 21, v_zetaHave_1359_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3 + 22, v___x_1368_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3 + 23, v_congrConsts_1360_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3 + 24, v_bitVecOfNat_1361_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3 + 25, v_warnExponents_1362_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3 + 26, v_suggestions_1363_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3 + 27, v_locals_1365_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*3 + 28, v_instances_1366_);
v___x_1370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg___closed__0));
v___x_1371_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1369_, v___x_1370_, v_a_1335_, v_a_1330_, v_a_1331_, v_a_1332_);
return v___x_1371_;
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
v_a_1372_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1334_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1334_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg___boxed(lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_1380_, v_a_1381_, v_a_1382_);
lean_dec(v_a_1382_);
lean_dec_ref(v_a_1381_);
lean_dec_ref(v_a_1380_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27(lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_1385_, v_a_1387_, v_a_1388_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___boxed(lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27(v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_);
lean_dec(v_a_1394_);
lean_dec_ref(v_a_1393_);
lean_dec(v_a_1392_);
lean_dec_ref(v_a_1391_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(lean_object* v_e_1397_, lean_object* v___y_1398_){
_start:
{
uint8_t v___x_1400_; 
v___x_1400_ = l_Lean_Expr_hasMVar(v_e_1397_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; 
v___x_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1401_, 0, v_e_1397_);
return v___x_1401_;
}
else
{
lean_object* v___x_1402_; lean_object* v_mctx_1403_; lean_object* v___x_1404_; lean_object* v_fst_1405_; lean_object* v_snd_1406_; lean_object* v___x_1407_; lean_object* v_cache_1408_; lean_object* v_zetaDeltaFVarIds_1409_; lean_object* v_postponed_1410_; lean_object* v_diag_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1420_; 
v___x_1402_ = lean_st_ref_get(v___y_1398_);
v_mctx_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc_ref(v_mctx_1403_);
lean_dec(v___x_1402_);
v___x_1404_ = l_Lean_instantiateMVarsCore(v_mctx_1403_, v_e_1397_);
v_fst_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_fst_1405_);
v_snd_1406_ = lean_ctor_get(v___x_1404_, 1);
lean_inc(v_snd_1406_);
lean_dec_ref(v___x_1404_);
v___x_1407_ = lean_st_ref_take(v___y_1398_);
v_cache_1408_ = lean_ctor_get(v___x_1407_, 1);
v_zetaDeltaFVarIds_1409_ = lean_ctor_get(v___x_1407_, 2);
v_postponed_1410_ = lean_ctor_get(v___x_1407_, 3);
v_diag_1411_ = lean_ctor_get(v___x_1407_, 4);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1420_ == 0)
{
lean_object* v_unused_1421_; 
v_unused_1421_ = lean_ctor_get(v___x_1407_, 0);
lean_dec(v_unused_1421_);
v___x_1413_ = v___x_1407_;
v_isShared_1414_ = v_isSharedCheck_1420_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_diag_1411_);
lean_inc(v_postponed_1410_);
lean_inc(v_zetaDeltaFVarIds_1409_);
lean_inc(v_cache_1408_);
lean_dec(v___x_1407_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1420_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 0, v_snd_1406_);
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_snd_1406_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v_cache_1408_);
lean_ctor_set(v_reuseFailAlloc_1419_, 2, v_zetaDeltaFVarIds_1409_);
lean_ctor_set(v_reuseFailAlloc_1419_, 3, v_postponed_1410_);
lean_ctor_set(v_reuseFailAlloc_1419_, 4, v_diag_1411_);
v___x_1416_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = lean_st_ref_set(v___y_1398_, v___x_1416_);
v___x_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1418_, 0, v_fst_1405_);
return v___x_1418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg___boxed(lean_object* v_e_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_e_1422_, v___y_1423_);
lean_dec(v___y_1423_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0(lean_object* v_e_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_e_1426_, v___y_1431_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___boxed(lean_object* v_e_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0(v_e_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(lean_object* v_cls_1446_, lean_object* v_msg_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_ref_1453_; lean_object* v___x_1454_; lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1499_; 
v_ref_1453_ = lean_ctor_get(v___y_1450_, 5);
v___x_1454_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(v_msg_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1457_ = v___x_1454_;
v_isShared_1458_ = v_isSharedCheck_1499_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1499_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1459_; lean_object* v_traceState_1460_; lean_object* v_env_1461_; lean_object* v_nextMacroScope_1462_; lean_object* v_ngen_1463_; lean_object* v_auxDeclNGen_1464_; lean_object* v_cache_1465_; lean_object* v_messages_1466_; lean_object* v_infoState_1467_; lean_object* v_snapshotTasks_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1498_; 
v___x_1459_ = lean_st_ref_take(v___y_1451_);
v_traceState_1460_ = lean_ctor_get(v___x_1459_, 4);
v_env_1461_ = lean_ctor_get(v___x_1459_, 0);
v_nextMacroScope_1462_ = lean_ctor_get(v___x_1459_, 1);
v_ngen_1463_ = lean_ctor_get(v___x_1459_, 2);
v_auxDeclNGen_1464_ = lean_ctor_get(v___x_1459_, 3);
v_cache_1465_ = lean_ctor_get(v___x_1459_, 5);
v_messages_1466_ = lean_ctor_get(v___x_1459_, 6);
v_infoState_1467_ = lean_ctor_get(v___x_1459_, 7);
v_snapshotTasks_1468_ = lean_ctor_get(v___x_1459_, 8);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1470_ = v___x_1459_;
v_isShared_1471_ = v_isSharedCheck_1498_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_snapshotTasks_1468_);
lean_inc(v_infoState_1467_);
lean_inc(v_messages_1466_);
lean_inc(v_cache_1465_);
lean_inc(v_traceState_1460_);
lean_inc(v_auxDeclNGen_1464_);
lean_inc(v_ngen_1463_);
lean_inc(v_nextMacroScope_1462_);
lean_inc(v_env_1461_);
lean_dec(v___x_1459_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1498_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
uint64_t v_tid_1472_; lean_object* v_traces_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1497_; 
v_tid_1472_ = lean_ctor_get_uint64(v_traceState_1460_, sizeof(void*)*1);
v_traces_1473_ = lean_ctor_get(v_traceState_1460_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v_traceState_1460_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1475_ = v_traceState_1460_;
v_isShared_1476_ = v_isSharedCheck_1497_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_traces_1473_);
lean_dec(v_traceState_1460_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1497_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; double v___x_1478_; uint8_t v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1487_; 
v___x_1477_ = lean_box(0);
v___x_1478_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0);
v___x_1479_ = 0;
v___x_1480_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__1));
v___x_1481_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1481_, 0, v_cls_1446_);
lean_ctor_set(v___x_1481_, 1, v___x_1477_);
lean_ctor_set(v___x_1481_, 2, v___x_1480_);
lean_ctor_set_float(v___x_1481_, sizeof(void*)*3, v___x_1478_);
lean_ctor_set_float(v___x_1481_, sizeof(void*)*3 + 8, v___x_1478_);
lean_ctor_set_uint8(v___x_1481_, sizeof(void*)*3 + 16, v___x_1479_);
v___x_1482_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__2));
v___x_1483_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1481_);
lean_ctor_set(v___x_1483_, 1, v_a_1455_);
lean_ctor_set(v___x_1483_, 2, v___x_1482_);
lean_inc(v_ref_1453_);
v___x_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1484_, 0, v_ref_1453_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
v___x_1485_ = l_Lean_PersistentArray_push___redArg(v_traces_1473_, v___x_1484_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 0, v___x_1485_);
v___x_1487_ = v___x_1475_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1485_);
lean_ctor_set_uint64(v_reuseFailAlloc_1496_, sizeof(void*)*1, v_tid_1472_);
v___x_1487_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1489_; 
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 4, v___x_1487_);
v___x_1489_ = v___x_1470_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_env_1461_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_nextMacroScope_1462_);
lean_ctor_set(v_reuseFailAlloc_1495_, 2, v_ngen_1463_);
lean_ctor_set(v_reuseFailAlloc_1495_, 3, v_auxDeclNGen_1464_);
lean_ctor_set(v_reuseFailAlloc_1495_, 4, v___x_1487_);
lean_ctor_set(v_reuseFailAlloc_1495_, 5, v_cache_1465_);
lean_ctor_set(v_reuseFailAlloc_1495_, 6, v_messages_1466_);
lean_ctor_set(v_reuseFailAlloc_1495_, 7, v_infoState_1467_);
lean_ctor_set(v_reuseFailAlloc_1495_, 8, v_snapshotTasks_1468_);
v___x_1489_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1493_; 
v___x_1490_ = lean_st_ref_set(v___y_1451_, v___x_1489_);
v___x_1491_ = lean_box(0);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 0, v___x_1491_);
v___x_1493_ = v___x_1457_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg___boxed(lean_object* v_cls_1500_, lean_object* v_msg_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v_cls_1500_, v_msg_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
return v_res_1507_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1514_ = lean_box(0);
v___x_1515_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__3));
v___x_1516_ = l_Lean_mkConst(v___x_1515_, v___x_1514_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(lean_object* v_a_1517_, lean_object* v_numIndices_1518_, lean_object* v_as_1519_, lean_object* v_i_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v_zero_1526_; uint8_t v_isZero_1527_; 
v_zero_1526_ = lean_unsigned_to_nat(0u);
v_isZero_1527_ = lean_nat_dec_eq(v_i_1520_, v_zero_1526_);
if (v_isZero_1527_ == 1)
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
lean_dec(v_i_1520_);
lean_dec_ref(v_a_1517_);
v___x_1528_ = lean_box(0);
v___x_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
return v___x_1529_;
}
else
{
lean_object* v_one_1530_; lean_object* v_n_1531_; lean_object* v___x_1532_; 
v_one_1530_ = lean_unsigned_to_nat(1u);
v_n_1531_ = lean_nat_sub(v_i_1520_, v_one_1530_);
lean_dec(v_i_1520_);
v___x_1532_ = lean_array_fget(v_as_1519_, v_n_1531_);
if (lean_obj_tag(v___x_1532_) == 0)
{
v_i_1520_ = v_n_1531_;
goto _start;
}
else
{
lean_object* v_val_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1599_; 
v_val_1534_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1536_ = v___x_1532_;
v_isShared_1537_ = v_isSharedCheck_1599_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_val_1534_);
lean_dec(v___x_1532_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1599_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
uint8_t v___y_1539_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1596_ = l_Lean_LocalDecl_index(v_val_1534_);
v___x_1597_ = lean_nat_dec_le(v_numIndices_1518_, v___x_1596_);
lean_dec(v___x_1596_);
if (v___x_1597_ == 0)
{
uint8_t v___x_1598_; 
v___x_1598_ = l_Lean_LocalDecl_isAuxDecl(v_val_1534_);
v___y_1539_ = v___x_1598_;
goto v___jp_1538_;
}
else
{
v___y_1539_ = v___x_1597_;
goto v___jp_1538_;
}
v___jp_1538_:
{
if (v___y_1539_ == 0)
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = l_Lean_LocalDecl_type(v_val_1534_);
lean_inc_ref(v___x_1540_);
lean_inc_ref(v_a_1517_);
v___x_1541_ = l_Lean_Meta_isExprDefEq(v_a_1517_, v___x_1540_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1586_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1544_ = v___x_1541_;
v_isShared_1545_ = v_isSharedCheck_1586_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1541_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1586_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
uint8_t v___x_1546_; 
v___x_1546_ = lean_unbox(v_a_1542_);
lean_dec(v_a_1542_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; uint8_t v___x_1548_; 
lean_del_object(v___x_1544_);
v___x_1547_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__1));
v___x_1548_ = l_Lean_Expr_isAppOfArity(v_a_1517_, v___x_1547_, v_one_1530_);
if (v___x_1548_ == 0)
{
lean_dec_ref(v___x_1540_);
lean_del_object(v___x_1536_);
lean_dec(v_val_1534_);
v_i_1520_ = v_n_1531_;
goto _start;
}
else
{
lean_object* v___x_1550_; uint8_t v___x_1551_; 
v___x_1550_ = l_Lean_Expr_appArg_x21(v_a_1517_);
v___x_1551_ = l_Lean_Expr_isAppOfArity(v___x_1550_, v___x_1547_, v_one_1530_);
if (v___x_1551_ == 0)
{
lean_dec_ref(v___x_1550_);
lean_dec_ref(v___x_1540_);
lean_del_object(v___x_1536_);
lean_dec(v_val_1534_);
v_i_1520_ = v_n_1531_;
goto _start;
}
else
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = l_Lean_Expr_appArg_x21(v___x_1550_);
lean_dec_ref(v___x_1550_);
lean_inc_ref(v___x_1553_);
v___x_1554_ = l_Lean_Meta_isExprDefEq(v___x_1553_, v___x_1540_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1570_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1557_ = v___x_1554_;
v_isShared_1558_ = v_isSharedCheck_1570_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1554_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1570_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
uint8_t v___x_1559_; 
v___x_1559_ = lean_unbox(v_a_1555_);
lean_dec(v_a_1555_);
if (v___x_1559_ == 0)
{
lean_del_object(v___x_1557_);
lean_dec_ref(v___x_1553_);
lean_del_object(v___x_1536_);
lean_dec(v_val_1534_);
v_i_1520_ = v_n_1531_;
goto _start;
}
else
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1565_; 
lean_dec(v_n_1531_);
lean_dec_ref(v_a_1517_);
v___x_1561_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4);
v___x_1562_ = l_Lean_LocalDecl_toExpr(v_val_1534_);
v___x_1563_ = l_Lean_mkAppB(v___x_1561_, v___x_1553_, v___x_1562_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 0, v___x_1563_);
v___x_1565_ = v___x_1536_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
lean_object* v___x_1567_; 
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 0, v___x_1565_);
v___x_1567_ = v___x_1557_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1565_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_dec_ref(v___x_1553_);
lean_del_object(v___x_1536_);
lean_dec(v_val_1534_);
lean_dec(v_n_1531_);
lean_dec_ref(v_a_1517_);
v_a_1571_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1554_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1554_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
}
}
else
{
lean_object* v___x_1579_; lean_object* v___x_1581_; 
lean_dec_ref(v___x_1540_);
lean_dec(v_n_1531_);
lean_dec_ref(v_a_1517_);
v___x_1579_ = l_Lean_LocalDecl_toExpr(v_val_1534_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 0, v___x_1579_);
v___x_1581_ = v___x_1536_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1579_);
v___x_1581_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1583_; 
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 0, v___x_1581_);
v___x_1583_ = v___x_1544_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_dec_ref(v___x_1540_);
lean_del_object(v___x_1536_);
lean_dec(v_val_1534_);
lean_dec(v_n_1531_);
lean_dec_ref(v_a_1517_);
v_a_1587_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1541_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1541_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
else
{
lean_del_object(v___x_1536_);
lean_dec(v_val_1534_);
v_i_1520_ = v_n_1531_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_a_1600_, lean_object* v_numIndices_1601_, lean_object* v_as_1602_, lean_object* v_i_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_a_1600_, v_numIndices_1601_, v_as_1602_, v_i_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec_ref(v_as_1602_);
lean_dec(v_numIndices_1601_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(lean_object* v_a_1610_, lean_object* v_numIndices_1611_, lean_object* v_as_1612_, lean_object* v_i_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v_zero_1622_; uint8_t v_isZero_1623_; 
v_zero_1622_ = lean_unsigned_to_nat(0u);
v_isZero_1623_ = lean_nat_dec_eq(v_i_1613_, v_zero_1622_);
if (v_isZero_1623_ == 1)
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
lean_dec(v_i_1613_);
lean_dec_ref(v_a_1610_);
v___x_1624_ = lean_box(0);
v___x_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
return v___x_1625_;
}
else
{
lean_object* v_one_1626_; lean_object* v_n_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v_one_1626_ = lean_unsigned_to_nat(1u);
v_n_1627_ = lean_nat_sub(v_i_1613_, v_one_1626_);
lean_dec(v_i_1613_);
v___x_1628_ = lean_array_fget_borrowed(v_as_1612_, v_n_1627_);
lean_inc_ref(v_a_1610_);
v___x_1629_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_a_1610_, v_numIndices_1611_, v___x_1628_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1630_);
if (lean_obj_tag(v_a_1630_) == 0)
{
lean_dec_ref(v___x_1629_);
v_i_1613_ = v_n_1627_;
goto _start;
}
else
{
lean_dec_ref(v_a_1630_);
lean_dec(v_n_1627_);
lean_dec_ref(v_a_1610_);
return v___x_1629_;
}
}
else
{
lean_dec(v_n_1627_);
lean_dec_ref(v_a_1610_);
return v___x_1629_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(lean_object* v_a_1632_, lean_object* v_numIndices_1633_, lean_object* v_x_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
if (lean_obj_tag(v_x_1634_) == 0)
{
lean_object* v_cs_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v_cs_1643_ = lean_ctor_get(v_x_1634_, 0);
v___x_1644_ = lean_array_get_size(v_cs_1643_);
v___x_1645_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_a_1632_, v_numIndices_1633_, v_cs_1643_, v___x_1644_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
return v___x_1645_;
}
else
{
lean_object* v_vs_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v_vs_1646_ = lean_ctor_get(v_x_1634_, 0);
v___x_1647_ = lean_array_get_size(v_vs_1646_);
v___x_1648_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_a_1632_, v_numIndices_1633_, v_vs_1646_, v___x_1647_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
return v___x_1648_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3___boxed(lean_object* v_a_1649_, lean_object* v_numIndices_1650_, lean_object* v_x_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_a_1649_, v_numIndices_1650_, v_x_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v_x_1651_);
lean_dec(v_numIndices_1650_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_a_1661_, lean_object* v_numIndices_1662_, lean_object* v_as_1663_, lean_object* v_i_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_a_1661_, v_numIndices_1662_, v_as_1663_, v_i_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v_as_1663_);
lean_dec(v_numIndices_1662_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(lean_object* v_a_1674_, lean_object* v_numIndices_1675_, lean_object* v_t_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v_root_1685_; lean_object* v_tail_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v_root_1685_ = lean_ctor_get(v_t_1676_, 0);
v_tail_1686_ = lean_ctor_get(v_t_1676_, 1);
v___x_1687_ = lean_array_get_size(v_tail_1686_);
lean_inc_ref(v_a_1674_);
v___x_1688_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_a_1674_, v_numIndices_1675_, v_tail_1686_, v___x_1687_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_a_1689_);
if (lean_obj_tag(v_a_1689_) == 0)
{
lean_object* v___x_1690_; 
lean_dec_ref(v___x_1688_);
v___x_1690_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_a_1674_, v_numIndices_1675_, v_root_1685_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
return v___x_1690_;
}
else
{
lean_dec_ref(v_a_1689_);
lean_dec_ref(v_a_1674_);
return v___x_1688_;
}
}
else
{
lean_dec_ref(v_a_1674_);
return v___x_1688_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1___boxed(lean_object* v_a_1691_, lean_object* v_numIndices_1692_, lean_object* v_t_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(v_a_1691_, v_numIndices_1692_, v_t_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v_t_1693_);
lean_dec(v_numIndices_1692_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(lean_object* v_a_1703_, lean_object* v_numIndices_1704_, lean_object* v_lctx_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v_decls_1714_; lean_object* v___x_1715_; 
v_decls_1714_ = lean_ctor_get(v_lctx_1705_, 1);
v___x_1715_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(v_a_1703_, v_numIndices_1704_, v_decls_1714_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1___boxed(lean_object* v_a_1716_, lean_object* v_numIndices_1717_, lean_object* v_lctx_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(v_a_1716_, v_numIndices_1717_, v_lctx_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v_lctx_1718_);
lean_dec(v_numIndices_1717_);
return v_res_1727_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3(void){
_start:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1733_ = lean_box(0);
v___x_1734_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2));
v___x_1735_ = l_Lean_mkConst(v___x_1734_, v___x_1733_);
return v___x_1735_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6(void){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1739_ = lean_box(0);
v___x_1740_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__5));
v___x_1741_ = l_Lean_mkConst(v___x_1740_, v___x_1739_);
return v___x_1741_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7(void){
_start:
{
uint8_t v___x_1742_; uint64_t v___x_1743_; 
v___x_1742_ = 1;
v___x_1743_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1742_);
return v___x_1743_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11(void){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1750_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10));
v___x_1751_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4));
v___x_1752_ = l_Lean_Name_append(v___x_1751_, v___x_1750_);
return v___x_1752_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12));
v___x_1755_ = l_Lean_stringToMessageData(v___x_1754_);
return v___x_1755_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__15(void){
_start:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14));
v___x_1758_ = l_Lean_stringToMessageData(v___x_1757_);
return v___x_1758_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__18(void){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17));
v___x_1763_ = l_Lean_MessageData_ofFormat(v___x_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(lean_object* v_numIndices_1764_, uint8_t v_useDecide_1765_, lean_object* v_prop_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_){
_start:
{
lean_object* v___x_1775_; lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1937_; 
v___x_1775_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_prop_1766_, v_a_1771_);
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1778_ = v___x_1775_;
v_isShared_1779_ = v_isSharedCheck_1937_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1937_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v_a_1800_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v_options_1905_; uint8_t v_hasTrace_1906_; 
v_options_1905_ = lean_ctor_get(v_a_1772_, 2);
v_hasTrace_1906_ = lean_ctor_get_uint8(v_options_1905_, sizeof(void*)*1);
if (v_hasTrace_1906_ == 0)
{
v___y_1828_ = v_a_1767_;
v___y_1829_ = v_a_1768_;
v___y_1830_ = v_a_1769_;
v___y_1831_ = v_a_1770_;
v___y_1832_ = v_a_1771_;
v___y_1833_ = v_a_1772_;
v___y_1834_ = v_a_1773_;
goto v___jp_1827_;
}
else
{
lean_object* v_inheritedTraceOptions_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; uint8_t v___x_1910_; 
v_inheritedTraceOptions_1907_ = lean_ctor_get(v_a_1772_, 13);
v___x_1908_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10));
v___x_1909_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11);
v___x_1910_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1907_, v_options_1905_, v___x_1909_);
if (v___x_1910_ == 0)
{
v___y_1828_ = v_a_1767_;
v___y_1829_ = v_a_1768_;
v___y_1830_ = v_a_1769_;
v___y_1831_ = v_a_1770_;
v___y_1832_ = v_a_1771_;
v___y_1833_ = v_a_1772_;
v___y_1834_ = v_a_1773_;
goto v___jp_1827_;
}
else
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___y_1917_; lean_object* v___x_1930_; lean_object* v___x_1931_; uint8_t v___x_1932_; 
v___x_1911_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13);
lean_inc(v_a_1776_);
v___x_1912_ = l_Lean_MessageData_ofExpr(v_a_1776_);
v___x_1913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1911_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__15, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__15_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__15);
v___x_1915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1913_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1930_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__1));
v___x_1931_ = lean_unsigned_to_nat(1u);
v___x_1932_ = l_Lean_Expr_isAppOfArity(v_a_1776_, v___x_1930_, v___x_1931_);
if (v___x_1932_ == 0)
{
goto v___jp_1928_;
}
else
{
lean_object* v___x_1933_; uint8_t v___x_1934_; 
v___x_1933_ = l_Lean_Expr_appArg_x21(v_a_1776_);
v___x_1934_ = l_Lean_Expr_isAppOfArity(v___x_1933_, v___x_1930_, v___x_1931_);
if (v___x_1934_ == 0)
{
lean_dec_ref(v___x_1933_);
goto v___jp_1928_;
}
else
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = l_Lean_Expr_appArg_x21(v___x_1933_);
lean_dec_ref(v___x_1933_);
v___x_1936_ = l_Lean_MessageData_ofExpr(v___x_1935_);
v___y_1917_ = v___x_1936_;
goto v___jp_1916_;
}
}
v___jp_1916_:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1915_);
lean_ctor_set(v___x_1918_, 1, v___y_1917_);
v___x_1919_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v___x_1908_, v___x_1918_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_dec_ref(v___x_1919_);
v___y_1828_ = v_a_1767_;
v___y_1829_ = v_a_1768_;
v___y_1830_ = v_a_1769_;
v___y_1831_ = v_a_1770_;
v___y_1832_ = v_a_1771_;
v___y_1833_ = v_a_1772_;
v___y_1834_ = v_a_1773_;
goto v___jp_1827_;
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
lean_del_object(v___x_1778_);
lean_dec(v_a_1776_);
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1919_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1919_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
v___jp_1928_:
{
lean_object* v___x_1929_; 
v___x_1929_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__18, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__18_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__18);
v___y_1917_ = v___x_1929_;
goto v___jp_1916_;
}
}
}
v___jp_1780_:
{
lean_object* v_lctx_1788_; lean_object* v___x_1789_; 
v_lctx_1788_ = lean_ctor_get(v___y_1784_, 2);
v___x_1789_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(v_a_1776_, v_numIndices_1764_, v_lctx_1788_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
return v___x_1789_;
}
v___jp_1790_:
{
lean_object* v___x_1801_; uint8_t v___x_1802_; 
v___x_1801_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2));
v___x_1802_ = l_Lean_Expr_isConstOf(v_a_1800_, v___x_1801_);
lean_dec_ref(v_a_1800_);
if (v___x_1802_ == 0)
{
lean_dec_ref(v___y_1795_);
lean_dec_ref(v___y_1792_);
lean_del_object(v___x_1778_);
v___y_1781_ = v___y_1791_;
v___y_1782_ = v___y_1797_;
v___y_1783_ = v___y_1799_;
v___y_1784_ = v___y_1798_;
v___y_1785_ = v___y_1794_;
v___y_1786_ = v___y_1796_;
v___y_1787_ = v___y_1793_;
goto v___jp_1780_;
}
else
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
lean_dec(v_a_1776_);
v___x_1803_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3);
v___x_1804_ = l_Lean_Meta_mkEqRefl(v___x_1803_, v___y_1798_, v___y_1794_, v___y_1796_, v___y_1793_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1818_; 
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1807_ = v___x_1804_;
v_isShared_1808_ = v_isSharedCheck_1818_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1804_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1818_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1813_; 
v___x_1809_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6);
v___x_1810_ = l_Lean_Expr_appArg_x21(v___y_1795_);
lean_dec_ref(v___y_1795_);
v___x_1811_ = l_Lean_mkApp3(v___x_1809_, v___y_1792_, v___x_1810_, v_a_1805_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set_tag(v___x_1778_, 1);
lean_ctor_set(v___x_1778_, 0, v___x_1811_);
v___x_1813_ = v___x_1778_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
lean_object* v___x_1815_; 
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v___x_1813_);
v___x_1815_ = v___x_1807_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
else
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
lean_dec_ref(v___y_1795_);
lean_dec_ref(v___y_1792_);
lean_del_object(v___x_1778_);
v_a_1819_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v___x_1804_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1804_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1819_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
}
v___jp_1827_:
{
if (v_useDecide_1765_ == 0)
{
lean_del_object(v___x_1778_);
v___y_1781_ = v___y_1828_;
v___y_1782_ = v___y_1829_;
v___y_1783_ = v___y_1830_;
v___y_1784_ = v___y_1831_;
v___y_1785_ = v___y_1832_;
v___y_1786_ = v___y_1833_;
v___y_1787_ = v___y_1834_;
goto v___jp_1780_;
}
else
{
lean_object* v___x_1835_; lean_object* v_a_1836_; uint8_t v___x_1837_; 
lean_inc(v_a_1776_);
v___x_1835_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_a_1776_, v___y_1832_);
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1836_);
lean_dec_ref(v___x_1835_);
v___x_1837_ = l_Lean_Expr_hasFVar(v_a_1836_);
if (v___x_1837_ == 0)
{
uint8_t v___x_1838_; 
v___x_1838_ = l_Lean_Expr_hasMVar(v_a_1836_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; 
lean_inc(v_a_1836_);
v___x_1839_ = l_Lean_Meta_mkDecide(v_a_1836_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1841_; uint8_t v_foApprox_1842_; uint8_t v_ctxApprox_1843_; uint8_t v_quasiPatternApprox_1844_; uint8_t v_constApprox_1845_; uint8_t v_isDefEqStuckEx_1846_; uint8_t v_unificationHints_1847_; uint8_t v_proofIrrelevance_1848_; uint8_t v_assignSyntheticOpaque_1849_; uint8_t v_offsetCnstrs_1850_; uint8_t v_etaStruct_1851_; uint8_t v_univApprox_1852_; uint8_t v_iota_1853_; uint8_t v_beta_1854_; uint8_t v_proj_1855_; uint8_t v_zeta_1856_; uint8_t v_zetaDelta_1857_; uint8_t v_zetaUnused_1858_; uint8_t v_zetaHave_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1896_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_a_1840_);
lean_dec_ref(v___x_1839_);
v___x_1841_ = l_Lean_Meta_Context_config(v___y_1831_);
v_foApprox_1842_ = lean_ctor_get_uint8(v___x_1841_, 0);
v_ctxApprox_1843_ = lean_ctor_get_uint8(v___x_1841_, 1);
v_quasiPatternApprox_1844_ = lean_ctor_get_uint8(v___x_1841_, 2);
v_constApprox_1845_ = lean_ctor_get_uint8(v___x_1841_, 3);
v_isDefEqStuckEx_1846_ = lean_ctor_get_uint8(v___x_1841_, 4);
v_unificationHints_1847_ = lean_ctor_get_uint8(v___x_1841_, 5);
v_proofIrrelevance_1848_ = lean_ctor_get_uint8(v___x_1841_, 6);
v_assignSyntheticOpaque_1849_ = lean_ctor_get_uint8(v___x_1841_, 7);
v_offsetCnstrs_1850_ = lean_ctor_get_uint8(v___x_1841_, 8);
v_etaStruct_1851_ = lean_ctor_get_uint8(v___x_1841_, 10);
v_univApprox_1852_ = lean_ctor_get_uint8(v___x_1841_, 11);
v_iota_1853_ = lean_ctor_get_uint8(v___x_1841_, 12);
v_beta_1854_ = lean_ctor_get_uint8(v___x_1841_, 13);
v_proj_1855_ = lean_ctor_get_uint8(v___x_1841_, 14);
v_zeta_1856_ = lean_ctor_get_uint8(v___x_1841_, 15);
v_zetaDelta_1857_ = lean_ctor_get_uint8(v___x_1841_, 16);
v_zetaUnused_1858_ = lean_ctor_get_uint8(v___x_1841_, 17);
v_zetaHave_1859_ = lean_ctor_get_uint8(v___x_1841_, 18);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1861_ = v___x_1841_;
v_isShared_1862_ = v_isSharedCheck_1896_;
goto v_resetjp_1860_;
}
else
{
lean_dec(v___x_1841_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1896_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
uint8_t v_trackZetaDelta_1863_; lean_object* v_zetaDeltaSet_1864_; lean_object* v_lctx_1865_; lean_object* v_localInstances_1866_; lean_object* v_defEqCtx_x3f_1867_; lean_object* v_synthPendingDepth_1868_; lean_object* v_canUnfold_x3f_1869_; uint8_t v_univApprox_1870_; uint8_t v_inTypeClassResolution_1871_; uint8_t v_cacheInferType_1872_; uint8_t v___x_1873_; lean_object* v_config_1875_; 
v_trackZetaDelta_1863_ = lean_ctor_get_uint8(v___y_1831_, sizeof(void*)*7);
v_zetaDeltaSet_1864_ = lean_ctor_get(v___y_1831_, 1);
v_lctx_1865_ = lean_ctor_get(v___y_1831_, 2);
v_localInstances_1866_ = lean_ctor_get(v___y_1831_, 3);
v_defEqCtx_x3f_1867_ = lean_ctor_get(v___y_1831_, 4);
v_synthPendingDepth_1868_ = lean_ctor_get(v___y_1831_, 5);
v_canUnfold_x3f_1869_ = lean_ctor_get(v___y_1831_, 6);
v_univApprox_1870_ = lean_ctor_get_uint8(v___y_1831_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1871_ = lean_ctor_get_uint8(v___y_1831_, sizeof(void*)*7 + 2);
v_cacheInferType_1872_ = lean_ctor_get_uint8(v___y_1831_, sizeof(void*)*7 + 3);
v___x_1873_ = 1;
if (v_isShared_1862_ == 0)
{
v_config_1875_ = v___x_1861_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, 0, v_foApprox_1842_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, 1, v_ctxApprox_1843_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, 2, v_quasiPatternApprox_1844_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, 3, v_constApprox_1845_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, 4, v_isDefEqStuckEx_1846_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, 5, v_unificationHints_1847_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, 6, v_proofIrrelevance_1848_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, 7, v_assignSyntheticOpaque_1849_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, 8, v_offsetCnstrs_1850_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, 10, v_etaStruct_1851_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, 11, v_univApprox_1852_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, 12, v_iota_1853_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, 13, v_beta_1854_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, 14, v_proj_1855_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, 15, v_zeta_1856_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, 16, v_zetaDelta_1857_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, 17, v_zetaUnused_1858_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, 18, v_zetaHave_1859_);
v_config_1875_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
uint64_t v___x_1876_; uint64_t v___x_1877_; uint64_t v___x_1878_; uint64_t v___x_1879_; uint64_t v___x_1880_; uint64_t v_key_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
lean_ctor_set_uint8(v_config_1875_, 9, v___x_1873_);
v___x_1876_ = l_Lean_Meta_Context_configKey(v___y_1831_);
v___x_1877_ = 2ULL;
v___x_1878_ = lean_uint64_shift_right(v___x_1876_, v___x_1877_);
v___x_1879_ = lean_uint64_shift_left(v___x_1878_, v___x_1877_);
v___x_1880_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7);
v_key_1881_ = lean_uint64_lor(v___x_1879_, v___x_1880_);
v___x_1882_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1882_, 0, v_config_1875_);
lean_ctor_set_uint64(v___x_1882_, sizeof(void*)*1, v_key_1881_);
lean_inc(v_canUnfold_x3f_1869_);
lean_inc(v_synthPendingDepth_1868_);
lean_inc(v_defEqCtx_x3f_1867_);
lean_inc_ref(v_localInstances_1866_);
lean_inc_ref(v_lctx_1865_);
lean_inc(v_zetaDeltaSet_1864_);
v___x_1883_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
lean_ctor_set(v___x_1883_, 1, v_zetaDeltaSet_1864_);
lean_ctor_set(v___x_1883_, 2, v_lctx_1865_);
lean_ctor_set(v___x_1883_, 3, v_localInstances_1866_);
lean_ctor_set(v___x_1883_, 4, v_defEqCtx_x3f_1867_);
lean_ctor_set(v___x_1883_, 5, v_synthPendingDepth_1868_);
lean_ctor_set(v___x_1883_, 6, v_canUnfold_x3f_1869_);
lean_ctor_set_uint8(v___x_1883_, sizeof(void*)*7, v_trackZetaDelta_1863_);
lean_ctor_set_uint8(v___x_1883_, sizeof(void*)*7 + 1, v_univApprox_1870_);
lean_ctor_set_uint8(v___x_1883_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1871_);
lean_ctor_set_uint8(v___x_1883_, sizeof(void*)*7 + 3, v_cacheInferType_1872_);
lean_inc(v___y_1834_);
lean_inc_ref(v___y_1833_);
lean_inc(v___y_1832_);
lean_inc(v_a_1840_);
v___x_1884_ = lean_whnf(v_a_1840_, v___x_1883_, v___y_1832_, v___y_1833_, v___y_1834_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1885_);
lean_dec_ref(v___x_1884_);
v___y_1791_ = v___y_1828_;
v___y_1792_ = v_a_1836_;
v___y_1793_ = v___y_1834_;
v___y_1794_ = v___y_1832_;
v___y_1795_ = v_a_1840_;
v___y_1796_ = v___y_1833_;
v___y_1797_ = v___y_1829_;
v___y_1798_ = v___y_1831_;
v___y_1799_ = v___y_1830_;
v_a_1800_ = v_a_1885_;
goto v___jp_1790_;
}
else
{
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1886_; 
v_a_1886_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1886_);
lean_dec_ref(v___x_1884_);
v___y_1791_ = v___y_1828_;
v___y_1792_ = v_a_1836_;
v___y_1793_ = v___y_1834_;
v___y_1794_ = v___y_1832_;
v___y_1795_ = v_a_1840_;
v___y_1796_ = v___y_1833_;
v___y_1797_ = v___y_1829_;
v___y_1798_ = v___y_1831_;
v___y_1799_ = v___y_1830_;
v_a_1800_ = v_a_1886_;
goto v___jp_1790_;
}
else
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1894_; 
lean_dec(v_a_1840_);
lean_dec(v_a_1836_);
lean_del_object(v___x_1778_);
lean_dec(v_a_1776_);
v_a_1887_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1889_ = v___x_1884_;
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1884_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1892_; 
if (v_isShared_1890_ == 0)
{
v___x_1892_ = v___x_1889_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_a_1887_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
lean_dec(v_a_1836_);
lean_del_object(v___x_1778_);
lean_dec(v_a_1776_);
v_a_1897_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1839_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1839_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
else
{
lean_dec(v_a_1836_);
lean_del_object(v___x_1778_);
v___y_1781_ = v___y_1828_;
v___y_1782_ = v___y_1829_;
v___y_1783_ = v___y_1830_;
v___y_1784_ = v___y_1831_;
v___y_1785_ = v___y_1832_;
v___y_1786_ = v___y_1833_;
v___y_1787_ = v___y_1834_;
goto v___jp_1780_;
}
}
else
{
lean_dec(v_a_1836_);
lean_del_object(v___x_1778_);
v___y_1781_ = v___y_1828_;
v___y_1782_ = v___y_1829_;
v___y_1783_ = v___y_1830_;
v___y_1784_ = v___y_1831_;
v___y_1785_ = v___y_1832_;
v___y_1786_ = v___y_1833_;
v___y_1787_ = v___y_1834_;
goto v___jp_1780_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___boxed(lean_object* v_numIndices_1938_, lean_object* v_useDecide_1939_, lean_object* v_prop_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
uint8_t v_useDecide_boxed_1949_; lean_object* v_res_1950_; 
v_useDecide_boxed_1949_ = lean_unbox(v_useDecide_1939_);
v_res_1950_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_1938_, v_useDecide_boxed_1949_, v_prop_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_);
lean_dec(v_a_1947_);
lean_dec_ref(v_a_1946_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec(v_a_1941_);
lean_dec(v_numIndices_1938_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2(lean_object* v_cls_1951_, lean_object* v_msg_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v___x_1961_; 
v___x_1961_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v_cls_1951_, v_msg_1952_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___boxed(lean_object* v_cls_1962_, lean_object* v_msg_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2(v_cls_1962_, v_msg_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2(lean_object* v_a_1973_, lean_object* v_numIndices_1974_, lean_object* v_as_1975_, lean_object* v_i_1976_, lean_object* v_a_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
lean_object* v___x_1986_; 
v___x_1986_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_a_1973_, v_numIndices_1974_, v_as_1975_, v_i_1976_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_a_1987_, lean_object* v_numIndices_1988_, lean_object* v_as_1989_, lean_object* v_i_1990_, lean_object* v_a_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2(v_a_1987_, v_numIndices_1988_, v_as_1989_, v_i_1990_, v_a_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v_as_1989_);
lean_dec(v_numIndices_1988_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5(lean_object* v_a_2001_, lean_object* v_numIndices_2002_, lean_object* v_as_2003_, lean_object* v_i_2004_, lean_object* v_a_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v___x_2014_; 
v___x_2014_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_a_2001_, v_numIndices_2002_, v_as_2003_, v_i_2004_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_a_2015_, lean_object* v_numIndices_2016_, lean_object* v_as_2017_, lean_object* v_i_2018_, lean_object* v_a_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5(v_a_2015_, v_numIndices_2016_, v_as_2017_, v_i_2018_, v_a_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v_as_2017_);
lean_dec(v_numIndices_2016_);
return v_res_2028_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3(void){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2034_ = lean_box(0);
v___x_2035_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__2));
v___x_2036_ = l_Lean_mkConst(v___x_2035_, v___x_2034_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27(lean_object* v_numIndices_2040_, uint8_t v_useDecideBool_2041_, lean_object* v_e_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_){
_start:
{
lean_object* v___x_2051_; 
lean_inc_ref(v_e_2042_);
v___x_2051_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2042_, v_a_2047_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2232_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2054_ = v___x_2051_;
v_isShared_2055_ = v_isSharedCheck_2232_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2051_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2232_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2061_; uint8_t v___x_2062_; 
v___x_2061_ = l_Lean_Expr_cleanupAnnotations(v_a_2052_);
v___x_2062_ = l_Lean_Expr_isApp(v___x_2061_);
if (v___x_2062_ == 0)
{
lean_dec_ref(v___x_2061_);
lean_dec_ref(v_e_2042_);
goto v___jp_2056_;
}
else
{
lean_object* v_arg_2063_; lean_object* v___x_2064_; uint8_t v___x_2065_; 
v_arg_2063_ = lean_ctor_get(v___x_2061_, 1);
lean_inc_ref(v_arg_2063_);
v___x_2064_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2061_);
v___x_2065_ = l_Lean_Expr_isApp(v___x_2064_);
if (v___x_2065_ == 0)
{
lean_dec_ref(v___x_2064_);
lean_dec_ref(v_arg_2063_);
lean_dec_ref(v_e_2042_);
goto v___jp_2056_;
}
else
{
lean_object* v_arg_2066_; lean_object* v___x_2067_; uint8_t v___x_2068_; 
v_arg_2066_ = lean_ctor_get(v___x_2064_, 1);
lean_inc_ref(v_arg_2066_);
v___x_2067_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2064_);
v___x_2068_ = l_Lean_Expr_isApp(v___x_2067_);
if (v___x_2068_ == 0)
{
lean_dec_ref(v___x_2067_);
lean_dec_ref(v_arg_2066_);
lean_dec_ref(v_arg_2063_);
lean_dec_ref(v_e_2042_);
goto v___jp_2056_;
}
else
{
lean_object* v_arg_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; 
v_arg_2069_ = lean_ctor_get(v___x_2067_, 1);
lean_inc_ref(v_arg_2069_);
v___x_2070_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2067_);
v___x_2071_ = l_Lean_Expr_isApp(v___x_2070_);
if (v___x_2071_ == 0)
{
lean_dec_ref(v___x_2070_);
lean_dec_ref(v_arg_2069_);
lean_dec_ref(v_arg_2066_);
lean_dec_ref(v_arg_2063_);
lean_dec_ref(v_e_2042_);
goto v___jp_2056_;
}
else
{
lean_object* v_arg_2072_; lean_object* v___x_2073_; uint8_t v___x_2074_; 
v_arg_2072_ = lean_ctor_get(v___x_2070_, 1);
lean_inc_ref(v_arg_2072_);
v___x_2073_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2070_);
v___x_2074_ = l_Lean_Expr_isApp(v___x_2073_);
if (v___x_2074_ == 0)
{
lean_dec_ref(v___x_2073_);
lean_dec_ref(v_arg_2072_);
lean_dec_ref(v_arg_2069_);
lean_dec_ref(v_arg_2066_);
lean_dec_ref(v_arg_2063_);
lean_dec_ref(v_e_2042_);
goto v___jp_2056_;
}
else
{
lean_object* v_arg_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; uint8_t v___x_2078_; 
v_arg_2075_ = lean_ctor_get(v___x_2073_, 1);
lean_inc_ref(v_arg_2075_);
v___x_2076_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2073_);
v___x_2077_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__2));
v___x_2078_ = l_Lean_Expr_isConstOf(v___x_2076_, v___x_2077_);
if (v___x_2078_ == 0)
{
lean_dec_ref(v___x_2076_);
lean_dec_ref(v_arg_2075_);
lean_dec_ref(v_arg_2072_);
lean_dec_ref(v_arg_2069_);
lean_dec_ref(v_arg_2066_);
lean_dec_ref(v_arg_2063_);
lean_dec_ref(v_e_2042_);
goto v___jp_2056_;
}
else
{
lean_object* v___x_2079_; 
lean_del_object(v___x_2054_);
lean_inc_ref(v_arg_2072_);
v___x_2079_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2040_, v_useDecideBool_2041_, v_arg_2072_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2223_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2082_ = v___x_2079_;
v_isShared_2083_ = v_isSharedCheck_2223_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2079_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2223_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2084_; 
v___x_2084_ = l_Lean_Expr_constLevels_x21(v___x_2076_);
if (lean_obj_tag(v_a_2080_) == 1)
{
lean_object* v_val_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2100_; 
lean_dec_ref(v___x_2076_);
lean_dec_ref(v_e_2042_);
v_val_2085_ = lean_ctor_get(v_a_2080_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v_a_2080_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2087_ = v_a_2080_;
v_isShared_2088_ = v_isSharedCheck_2100_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_val_2085_);
lean_dec(v_a_2080_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2100_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2093_; 
v___x_2089_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__7));
v___x_2090_ = l_Lean_mkConst(v___x_2089_, v___x_2084_);
lean_inc_ref(v_arg_2066_);
v___x_2091_ = l_Lean_mkApp6(v___x_2090_, v_arg_2072_, v_arg_2069_, v_val_2085_, v_arg_2075_, v_arg_2066_, v_arg_2063_);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 0, v___x_2091_);
v___x_2093_ = v___x_2087_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2097_; 
v___x_2094_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2094_, 0, v_arg_2066_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
lean_ctor_set_uint8(v___x_2094_, sizeof(void*)*2, v___x_2078_);
v___x_2095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2094_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 0, v___x_2095_);
v___x_2097_ = v___x_2082_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
else
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
lean_del_object(v___x_2082_);
lean_dec(v_a_2080_);
lean_inc_ref(v_arg_2072_);
v___x_2101_ = l_Lean_mkNot(v_arg_2072_);
v___x_2102_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2040_, v_useDecideBool_2041_, v___x_2101_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2214_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2105_ = v___x_2102_;
v_isShared_2106_ = v_isSharedCheck_2214_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2102_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2214_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
if (lean_obj_tag(v_a_2103_) == 1)
{
lean_object* v_val_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2122_; 
lean_dec_ref(v___x_2076_);
lean_dec_ref(v_e_2042_);
v_val_2107_ = lean_ctor_get(v_a_2103_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v_a_2103_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2109_ = v_a_2103_;
v_isShared_2110_ = v_isSharedCheck_2122_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_val_2107_);
lean_dec(v_a_2103_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2122_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2115_; 
v___x_2111_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__9));
v___x_2112_ = l_Lean_mkConst(v___x_2111_, v___x_2084_);
lean_inc_ref(v_arg_2063_);
v___x_2113_ = l_Lean_mkApp6(v___x_2112_, v_arg_2072_, v_arg_2069_, v_val_2107_, v_arg_2075_, v_arg_2066_, v_arg_2063_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v___x_2113_);
v___x_2115_ = v___x_2109_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_2113_);
v___x_2115_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2119_; 
v___x_2116_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2116_, 0, v_arg_2063_);
lean_ctor_set(v___x_2116_, 1, v___x_2115_);
lean_ctor_set_uint8(v___x_2116_, sizeof(void*)*2, v___x_2078_);
v___x_2117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 0, v___x_2117_);
v___x_2119_ = v___x_2105_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2117_);
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
else
{
lean_object* v___x_2123_; 
lean_del_object(v___x_2105_);
lean_dec(v_a_2103_);
lean_inc(v_a_2049_);
lean_inc_ref(v_a_2048_);
lean_inc(v_a_2047_);
lean_inc_ref(v_a_2046_);
lean_inc(v_a_2045_);
lean_inc_ref(v_a_2044_);
lean_inc(v_a_2043_);
lean_inc_ref(v_arg_2072_);
v___x_2123_ = lean_simp(v_arg_2072_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2205_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2126_ = v___x_2123_;
v_isShared_2127_ = v_isSharedCheck_2205_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2123_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2205_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v_expr_2128_; uint8_t v___x_2129_; 
v_expr_2128_ = lean_ctor_get(v_a_2124_, 0);
v___x_2129_ = lean_expr_eqv(v_expr_2128_, v_arg_2072_);
if (v___x_2129_ == 0)
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
lean_del_object(v___x_2126_);
v___x_2130_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3);
lean_inc_ref(v_expr_2128_);
v___x_2131_ = l_Lean_Expr_app___override(v___x_2130_, v_expr_2128_);
v___x_2132_ = lean_box(0);
v___x_2133_ = l_Lean_Meta_trySynthInstance(v___x_2131_, v___x_2132_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2182_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2136_ = v___x_2133_;
v_isShared_2137_ = v_isSharedCheck_2182_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2182_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
if (lean_obj_tag(v_a_2134_) == 1)
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2168_; 
lean_inc_ref(v_expr_2128_);
lean_del_object(v___x_2136_);
lean_dec_ref(v_e_2042_);
v_a_2138_ = lean_ctor_get(v_a_2134_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v_a_2134_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2140_ = v_a_2134_;
v_isShared_2141_ = v_isSharedCheck_2168_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v_a_2134_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2168_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; 
v___x_2142_ = l_Lean_Meta_Simp_Result_getProof(v_a_2124_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2159_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2145_ = v___x_2142_;
v_isShared_2146_ = v_isSharedCheck_2159_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v___x_2142_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2159_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2152_; 
v___x_2147_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__5));
v___x_2148_ = l_Lean_mkConst(v___x_2147_, v___x_2084_);
lean_inc_ref(v_arg_2063_);
lean_inc_ref(v_arg_2066_);
lean_inc(v_a_2138_);
lean_inc_ref(v_expr_2128_);
lean_inc_ref(v_arg_2075_);
v___x_2149_ = l_Lean_mkApp8(v___x_2148_, v_arg_2075_, v_arg_2072_, v_expr_2128_, v_arg_2069_, v_a_2138_, v_arg_2066_, v_arg_2063_, v_a_2143_);
v___x_2150_ = l_Lean_mkApp5(v___x_2076_, v_arg_2075_, v_expr_2128_, v_a_2138_, v_arg_2066_, v_arg_2063_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v___x_2149_);
v___x_2152_ = v___x_2140_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2149_);
v___x_2152_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2156_; 
v___x_2153_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2153_, 0, v___x_2150_);
lean_ctor_set(v___x_2153_, 1, v___x_2152_);
lean_ctor_set_uint8(v___x_2153_, sizeof(void*)*2, v___x_2078_);
v___x_2154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2153_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 0, v___x_2154_);
v___x_2156_ = v___x_2145_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2154_);
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
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
lean_del_object(v___x_2140_);
lean_dec(v_a_2138_);
lean_dec_ref(v_expr_2128_);
lean_dec(v___x_2084_);
lean_dec_ref(v___x_2076_);
lean_dec_ref(v_arg_2075_);
lean_dec_ref(v_arg_2072_);
lean_dec_ref(v_arg_2069_);
lean_dec_ref(v_arg_2066_);
lean_dec_ref(v_arg_2063_);
v_a_2160_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2142_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2142_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
}
else
{
lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2179_; 
lean_dec(v_a_2134_);
lean_dec(v___x_2084_);
lean_dec_ref(v___x_2076_);
lean_dec_ref(v_arg_2075_);
lean_dec_ref(v_arg_2072_);
lean_dec_ref(v_arg_2069_);
lean_dec_ref(v_arg_2066_);
lean_dec_ref(v_arg_2063_);
v_isSharedCheck_2179_ = !lean_is_exclusive(v_a_2124_);
if (v_isSharedCheck_2179_ == 0)
{
lean_object* v_unused_2180_; lean_object* v_unused_2181_; 
v_unused_2180_ = lean_ctor_get(v_a_2124_, 1);
lean_dec(v_unused_2180_);
v_unused_2181_ = lean_ctor_get(v_a_2124_, 0);
lean_dec(v_unused_2181_);
v___x_2170_ = v_a_2124_;
v_isShared_2171_ = v_isSharedCheck_2179_;
goto v_resetjp_2169_;
}
else
{
lean_dec(v_a_2124_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2179_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 1, v___x_2132_);
lean_ctor_set(v___x_2170_, 0, v_e_2042_);
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_e_2042_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v___x_2132_);
v___x_2173_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v___x_2174_; lean_object* v___x_2176_; 
lean_ctor_set_uint8(v___x_2173_, sizeof(void*)*2, v___x_2078_);
v___x_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 0, v___x_2174_);
v___x_2176_ = v___x_2136_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2174_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_dec(v_a_2124_);
lean_dec(v___x_2084_);
lean_dec_ref(v___x_2076_);
lean_dec_ref(v_arg_2075_);
lean_dec_ref(v_arg_2072_);
lean_dec_ref(v_arg_2069_);
lean_dec_ref(v_arg_2066_);
lean_dec_ref(v_arg_2063_);
lean_dec_ref(v_e_2042_);
v_a_2183_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2133_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2133_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
else
{
lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2202_; 
lean_dec(v___x_2084_);
lean_dec_ref(v___x_2076_);
lean_dec_ref(v_arg_2075_);
lean_dec_ref(v_arg_2072_);
lean_dec_ref(v_arg_2069_);
lean_dec_ref(v_arg_2066_);
lean_dec_ref(v_arg_2063_);
v_isSharedCheck_2202_ = !lean_is_exclusive(v_a_2124_);
if (v_isSharedCheck_2202_ == 0)
{
lean_object* v_unused_2203_; lean_object* v_unused_2204_; 
v_unused_2203_ = lean_ctor_get(v_a_2124_, 1);
lean_dec(v_unused_2203_);
v_unused_2204_ = lean_ctor_get(v_a_2124_, 0);
lean_dec(v_unused_2204_);
v___x_2192_ = v_a_2124_;
v_isShared_2193_ = v_isSharedCheck_2202_;
goto v_resetjp_2191_;
}
else
{
lean_dec(v_a_2124_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2202_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2194_ = lean_box(0);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 1, v___x_2194_);
lean_ctor_set(v___x_2192_, 0, v_e_2042_);
v___x_2196_ = v___x_2192_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_e_2042_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2197_; lean_object* v___x_2199_; 
lean_ctor_set_uint8(v___x_2196_, sizeof(void*)*2, v___x_2078_);
v___x_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 0, v___x_2197_);
v___x_2199_ = v___x_2126_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2197_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
}
}
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_dec(v___x_2084_);
lean_dec_ref(v___x_2076_);
lean_dec_ref(v_arg_2075_);
lean_dec_ref(v_arg_2072_);
lean_dec_ref(v_arg_2069_);
lean_dec_ref(v_arg_2066_);
lean_dec_ref(v_arg_2063_);
lean_dec_ref(v_e_2042_);
v_a_2206_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2123_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2123_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
}
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
lean_dec(v___x_2084_);
lean_dec_ref(v___x_2076_);
lean_dec_ref(v_arg_2075_);
lean_dec_ref(v_arg_2072_);
lean_dec_ref(v_arg_2069_);
lean_dec_ref(v_arg_2066_);
lean_dec_ref(v_arg_2063_);
lean_dec_ref(v_e_2042_);
v_a_2215_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2102_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2102_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
}
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
lean_dec_ref(v___x_2076_);
lean_dec_ref(v_arg_2075_);
lean_dec_ref(v_arg_2072_);
lean_dec_ref(v_arg_2069_);
lean_dec_ref(v_arg_2066_);
lean_dec_ref(v_arg_2063_);
lean_dec_ref(v_e_2042_);
v_a_2224_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2079_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2079_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2229_; 
if (v_isShared_2227_ == 0)
{
v___x_2229_ = v___x_2226_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2224_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
}
}
}
}
}
v___jp_2056_:
{
lean_object* v___x_2057_; lean_object* v___x_2059_; 
v___x_2057_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__0));
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v___x_2057_);
v___x_2059_ = v___x_2054_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2057_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
lean_dec_ref(v_e_2042_);
v_a_2233_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2051_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2051_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___boxed(lean_object* v_numIndices_2241_, lean_object* v_useDecideBool_2242_, lean_object* v_e_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_){
_start:
{
uint8_t v_useDecideBool_boxed_2252_; lean_object* v_res_2253_; 
v_useDecideBool_boxed_2252_ = lean_unbox(v_useDecideBool_2242_);
v_res_2253_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27(v_numIndices_2241_, v_useDecideBool_boxed_2252_, v_e_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_);
lean_dec(v_a_2250_);
lean_dec_ref(v_a_2249_);
lean_dec(v_a_2248_);
lean_dec_ref(v_a_2247_);
lean_dec(v_a_2246_);
lean_dec_ref(v_a_2245_);
lean_dec(v_a_2244_);
lean_dec(v_numIndices_2241_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(lean_object* v_e_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_){
_start:
{
if (lean_obj_tag(v_e_2257_) == 6)
{
lean_object* v_binderName_2261_; lean_object* v___x_2262_; 
v_binderName_2261_ = lean_ctor_get(v_e_2257_, 0);
lean_inc(v_binderName_2261_);
v___x_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2262_, 0, v_binderName_2261_);
return v___x_2262_;
}
else
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2263_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__1));
v___x_2264_ = l_Lean_Core_mkFreshUserName(v___x_2263_, v_a_2258_, v_a_2259_);
return v___x_2264_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___boxed(lean_object* v_e_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_e_2265_, v_a_2266_, v_a_2267_);
lean_dec(v_a_2267_);
lean_dec_ref(v_a_2266_);
lean_dec_ref(v_e_2265_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName(lean_object* v_e_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_){
_start:
{
lean_object* v___x_2276_; 
v___x_2276_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_e_2270_, v_a_2273_, v_a_2274_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___boxed(lean_object* v_e_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName(v_e_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_);
lean_dec(v_a_2281_);
lean_dec_ref(v_a_2280_);
lean_dec(v_a_2279_);
lean_dec_ref(v_a_2278_);
lean_dec_ref(v_e_2277_);
return v_res_2283_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3(void){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2289_ = lean_box(0);
v___x_2290_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__2));
v___x_2291_ = l_Lean_mkConst(v___x_2290_, v___x_2289_);
return v___x_2291_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4(void){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = lean_unsigned_to_nat(0u);
v___x_2293_ = l_Lean_mkBVar(v___x_2292_);
return v___x_2293_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7(void){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2298_ = lean_box(0);
v___x_2299_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__6));
v___x_2300_ = l_Lean_mkConst(v___x_2299_, v___x_2298_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27(lean_object* v_numIndices_2304_, uint8_t v_useDecideBool_2305_, lean_object* v_e_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_){
_start:
{
lean_object* v___x_2315_; 
lean_inc_ref(v_e_2306_);
v___x_2315_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2306_, v_a_2311_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2525_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2318_ = v___x_2315_;
v_isShared_2319_ = v_isSharedCheck_2525_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2315_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2525_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2325_; uint8_t v___x_2326_; 
v___x_2325_ = l_Lean_Expr_cleanupAnnotations(v_a_2316_);
v___x_2326_ = l_Lean_Expr_isApp(v___x_2325_);
if (v___x_2326_ == 0)
{
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_e_2306_);
goto v___jp_2320_;
}
else
{
lean_object* v_arg_2327_; lean_object* v___x_2328_; uint8_t v___x_2329_; 
v_arg_2327_ = lean_ctor_get(v___x_2325_, 1);
lean_inc_ref(v_arg_2327_);
v___x_2328_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2325_);
v___x_2329_ = l_Lean_Expr_isApp(v___x_2328_);
if (v___x_2329_ == 0)
{
lean_dec_ref(v___x_2328_);
lean_dec_ref(v_arg_2327_);
lean_dec_ref(v_e_2306_);
goto v___jp_2320_;
}
else
{
lean_object* v_arg_2330_; lean_object* v___x_2331_; uint8_t v___x_2332_; 
v_arg_2330_ = lean_ctor_get(v___x_2328_, 1);
lean_inc_ref(v_arg_2330_);
v___x_2331_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2328_);
v___x_2332_ = l_Lean_Expr_isApp(v___x_2331_);
if (v___x_2332_ == 0)
{
lean_dec_ref(v___x_2331_);
lean_dec_ref(v_arg_2330_);
lean_dec_ref(v_arg_2327_);
lean_dec_ref(v_e_2306_);
goto v___jp_2320_;
}
else
{
lean_object* v_arg_2333_; lean_object* v___x_2334_; uint8_t v___x_2335_; 
v_arg_2333_ = lean_ctor_get(v___x_2331_, 1);
lean_inc_ref(v_arg_2333_);
v___x_2334_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2331_);
v___x_2335_ = l_Lean_Expr_isApp(v___x_2334_);
if (v___x_2335_ == 0)
{
lean_dec_ref(v___x_2334_);
lean_dec_ref(v_arg_2333_);
lean_dec_ref(v_arg_2330_);
lean_dec_ref(v_arg_2327_);
lean_dec_ref(v_e_2306_);
goto v___jp_2320_;
}
else
{
lean_object* v_arg_2336_; lean_object* v___x_2337_; uint8_t v___x_2338_; 
v_arg_2336_ = lean_ctor_get(v___x_2334_, 1);
lean_inc_ref(v_arg_2336_);
v___x_2337_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2334_);
v___x_2338_ = l_Lean_Expr_isApp(v___x_2337_);
if (v___x_2338_ == 0)
{
lean_dec_ref(v___x_2337_);
lean_dec_ref(v_arg_2336_);
lean_dec_ref(v_arg_2333_);
lean_dec_ref(v_arg_2330_);
lean_dec_ref(v_arg_2327_);
lean_dec_ref(v_e_2306_);
goto v___jp_2320_;
}
else
{
lean_object* v_arg_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; uint8_t v___x_2342_; 
v_arg_2339_ = lean_ctor_get(v___x_2337_, 1);
lean_inc_ref(v_arg_2339_);
v___x_2340_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2337_);
v___x_2341_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__4));
v___x_2342_ = l_Lean_Expr_isConstOf(v___x_2340_, v___x_2341_);
if (v___x_2342_ == 0)
{
lean_dec_ref(v___x_2340_);
lean_dec_ref(v_arg_2339_);
lean_dec_ref(v_arg_2336_);
lean_dec_ref(v_arg_2333_);
lean_dec_ref(v_arg_2330_);
lean_dec_ref(v_arg_2327_);
lean_dec_ref(v_e_2306_);
goto v___jp_2320_;
}
else
{
lean_object* v___x_2343_; 
lean_del_object(v___x_2318_);
lean_inc_ref(v_arg_2336_);
v___x_2343_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2304_, v_useDecideBool_2305_, v_arg_2336_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2516_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2346_ = v___x_2343_;
v_isShared_2347_ = v_isSharedCheck_2516_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2343_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2516_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2348_; 
v___x_2348_ = l_Lean_Expr_constLevels_x21(v___x_2340_);
if (lean_obj_tag(v_a_2344_) == 1)
{
lean_object* v_val_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2366_; 
lean_dec_ref(v___x_2340_);
lean_dec_ref(v_e_2306_);
v_val_2349_ = lean_ctor_get(v_a_2344_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v_a_2344_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2351_ = v_a_2344_;
v_isShared_2352_ = v_isSharedCheck_2366_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_val_2349_);
lean_dec(v_a_2344_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2366_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2359_; 
lean_inc(v_val_2349_);
lean_inc_ref(v_arg_2330_);
v___x_2353_ = l_Lean_Expr_app___override(v_arg_2330_, v_val_2349_);
v___x_2354_ = l_Lean_Expr_headBeta(v___x_2353_);
v___x_2355_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__11));
v___x_2356_ = l_Lean_mkConst(v___x_2355_, v___x_2348_);
v___x_2357_ = l_Lean_mkApp6(v___x_2356_, v_arg_2336_, v_arg_2333_, v_val_2349_, v_arg_2339_, v_arg_2330_, v_arg_2327_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v___x_2357_);
v___x_2359_ = v___x_2351_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2357_);
v___x_2359_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2363_; 
v___x_2360_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2360_, 0, v___x_2354_);
lean_ctor_set(v___x_2360_, 1, v___x_2359_);
lean_ctor_set_uint8(v___x_2360_, sizeof(void*)*2, v___x_2342_);
v___x_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2360_);
if (v_isShared_2347_ == 0)
{
lean_ctor_set(v___x_2346_, 0, v___x_2361_);
v___x_2363_ = v___x_2346_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
else
{
lean_object* v___x_2367_; lean_object* v___x_2368_; 
lean_del_object(v___x_2346_);
lean_dec(v_a_2344_);
lean_inc_ref(v_arg_2336_);
v___x_2367_ = l_Lean_mkNot(v_arg_2336_);
v___x_2368_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2304_, v_useDecideBool_2305_, v___x_2367_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2507_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2371_ = v___x_2368_;
v_isShared_2372_ = v_isSharedCheck_2507_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2368_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2507_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
if (lean_obj_tag(v_a_2369_) == 1)
{
lean_object* v_val_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2390_; 
lean_dec_ref(v___x_2340_);
lean_dec_ref(v_e_2306_);
v_val_2373_ = lean_ctor_get(v_a_2369_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v_a_2369_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2375_ = v_a_2369_;
v_isShared_2376_ = v_isSharedCheck_2390_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_val_2373_);
lean_dec(v_a_2369_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2390_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2383_; 
lean_inc(v_val_2373_);
lean_inc_ref(v_arg_2327_);
v___x_2377_ = l_Lean_Expr_app___override(v_arg_2327_, v_val_2373_);
v___x_2378_ = l_Lean_Expr_headBeta(v___x_2377_);
v___x_2379_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__13));
v___x_2380_ = l_Lean_mkConst(v___x_2379_, v___x_2348_);
v___x_2381_ = l_Lean_mkApp6(v___x_2380_, v_arg_2336_, v_arg_2333_, v_val_2373_, v_arg_2339_, v_arg_2330_, v_arg_2327_);
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 0, v___x_2381_);
v___x_2383_ = v___x_2375_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2381_);
v___x_2383_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2387_; 
v___x_2384_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2384_, 0, v___x_2378_);
lean_ctor_set(v___x_2384_, 1, v___x_2383_);
lean_ctor_set_uint8(v___x_2384_, sizeof(void*)*2, v___x_2342_);
v___x_2385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2384_);
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 0, v___x_2385_);
v___x_2387_ = v___x_2371_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2385_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
else
{
lean_object* v___x_2391_; 
lean_del_object(v___x_2371_);
lean_dec(v_a_2369_);
lean_inc(v_a_2313_);
lean_inc_ref(v_a_2312_);
lean_inc(v_a_2311_);
lean_inc_ref(v_a_2310_);
lean_inc(v_a_2309_);
lean_inc_ref(v_a_2308_);
lean_inc(v_a_2307_);
lean_inc_ref(v_arg_2336_);
v___x_2391_ = lean_simp(v_arg_2336_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2498_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2394_ = v___x_2391_;
v_isShared_2395_ = v_isSharedCheck_2498_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2391_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2498_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v_expr_2396_; uint8_t v___x_2397_; 
v_expr_2396_ = lean_ctor_get(v_a_2392_, 0);
v___x_2397_ = lean_expr_eqv(v_expr_2396_, v_arg_2336_);
if (v___x_2397_ == 0)
{
lean_object* v___x_2398_; 
lean_inc_ref(v_expr_2396_);
lean_del_object(v___x_2394_);
v___x_2398_ = l_Lean_Meta_Simp_Result_getProof(v_a_2392_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_a_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_a_2399_);
lean_dec_ref(v___x_2398_);
v___x_2400_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3);
lean_inc_ref(v_expr_2396_);
v___x_2401_ = l_Lean_Expr_app___override(v___x_2400_, v_expr_2396_);
v___x_2402_ = lean_box(0);
v___x_2403_ = l_Lean_Meta_trySynthInstance(v___x_2401_, v___x_2402_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2467_; 
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2406_ = v___x_2403_;
v_isShared_2407_ = v_isSharedCheck_2467_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2403_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2467_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
if (lean_obj_tag(v_a_2404_) == 1)
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2461_; 
lean_del_object(v___x_2406_);
lean_dec_ref(v_e_2306_);
v_a_2408_ = lean_ctor_get(v_a_2404_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v_a_2404_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2410_ = v_a_2404_;
v_isShared_2411_ = v_isSharedCheck_2461_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v_a_2404_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2461_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2412_; 
v___x_2412_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_arg_2330_, v_a_2312_, v_a_2313_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v_a_2413_; lean_object* v___x_2414_; 
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_a_2413_);
lean_dec_ref(v___x_2412_);
v___x_2414_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_arg_2327_, v_a_2312_, v_a_2313_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2444_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2417_ = v___x_2414_;
v_isShared_2418_ = v_isSharedCheck_2444_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2414_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2444_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; uint8_t v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2437_; 
v___x_2419_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3);
v___x_2420_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4);
lean_inc_n(v_a_2399_, 2);
lean_inc_ref_n(v_expr_2396_, 5);
lean_inc_ref_n(v_arg_2336_, 2);
v___x_2421_ = l_Lean_mkApp4(v___x_2419_, v_arg_2336_, v_expr_2396_, v_a_2399_, v___x_2420_);
lean_inc_ref(v_arg_2330_);
v___x_2422_ = l_Lean_Expr_app___override(v_arg_2330_, v___x_2421_);
v___x_2423_ = l_Lean_Expr_headBeta(v___x_2422_);
v___x_2424_ = 0;
v___x_2425_ = l_Lean_mkLambda(v_a_2413_, v___x_2424_, v_expr_2396_, v___x_2423_);
v___x_2426_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7);
v___x_2427_ = l_Lean_mkApp4(v___x_2426_, v_arg_2336_, v_expr_2396_, v_a_2399_, v___x_2420_);
lean_inc_ref(v_arg_2327_);
v___x_2428_ = l_Lean_Expr_app___override(v_arg_2327_, v___x_2427_);
v___x_2429_ = l_Lean_Expr_headBeta(v___x_2428_);
v___x_2430_ = l_Lean_mkNot(v_expr_2396_);
v___x_2431_ = l_Lean_mkLambda(v_a_2415_, v___x_2424_, v___x_2430_, v___x_2429_);
lean_inc(v_a_2408_);
lean_inc_ref(v_arg_2339_);
v___x_2432_ = l_Lean_mkApp5(v___x_2340_, v_arg_2339_, v_expr_2396_, v_a_2408_, v___x_2425_, v___x_2431_);
v___x_2433_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__9));
v___x_2434_ = l_Lean_mkConst(v___x_2433_, v___x_2348_);
v___x_2435_ = l_Lean_mkApp8(v___x_2434_, v_arg_2339_, v_arg_2336_, v_expr_2396_, v_arg_2333_, v_a_2408_, v_arg_2330_, v_arg_2327_, v_a_2399_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 0, v___x_2435_);
v___x_2437_ = v___x_2410_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2435_);
v___x_2437_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2441_; 
v___x_2438_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2438_, 0, v___x_2432_);
lean_ctor_set(v___x_2438_, 1, v___x_2437_);
lean_ctor_set_uint8(v___x_2438_, sizeof(void*)*2, v___x_2342_);
v___x_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2438_);
if (v_isShared_2418_ == 0)
{
lean_ctor_set(v___x_2417_, 0, v___x_2439_);
v___x_2441_ = v___x_2417_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v___x_2439_);
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
else
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2452_; 
lean_dec(v_a_2413_);
lean_del_object(v___x_2410_);
lean_dec(v_a_2408_);
lean_dec(v_a_2399_);
lean_dec_ref(v_expr_2396_);
lean_dec(v___x_2348_);
lean_dec_ref(v___x_2340_);
lean_dec_ref(v_arg_2339_);
lean_dec_ref(v_arg_2336_);
lean_dec_ref(v_arg_2333_);
lean_dec_ref(v_arg_2330_);
lean_dec_ref(v_arg_2327_);
v_a_2445_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2447_ = v___x_2414_;
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2414_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2450_; 
if (v_isShared_2448_ == 0)
{
v___x_2450_ = v___x_2447_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_a_2445_);
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
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2460_; 
lean_del_object(v___x_2410_);
lean_dec(v_a_2408_);
lean_dec(v_a_2399_);
lean_dec_ref(v_expr_2396_);
lean_dec(v___x_2348_);
lean_dec_ref(v___x_2340_);
lean_dec_ref(v_arg_2339_);
lean_dec_ref(v_arg_2336_);
lean_dec_ref(v_arg_2333_);
lean_dec_ref(v_arg_2330_);
lean_dec_ref(v_arg_2327_);
v_a_2453_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2455_ = v___x_2412_;
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2412_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
if (v_isShared_2456_ == 0)
{
v___x_2458_ = v___x_2455_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2453_);
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
}
else
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2465_; 
lean_dec(v_a_2404_);
lean_dec(v_a_2399_);
lean_dec_ref(v_expr_2396_);
lean_dec(v___x_2348_);
lean_dec_ref(v___x_2340_);
lean_dec_ref(v_arg_2339_);
lean_dec_ref(v_arg_2336_);
lean_dec_ref(v_arg_2333_);
lean_dec_ref(v_arg_2330_);
lean_dec_ref(v_arg_2327_);
v___x_2462_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2462_, 0, v_e_2306_);
lean_ctor_set(v___x_2462_, 1, v___x_2402_);
lean_ctor_set_uint8(v___x_2462_, sizeof(void*)*2, v___x_2342_);
v___x_2463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2462_);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 0, v___x_2463_);
v___x_2465_ = v___x_2406_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2463_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
lean_dec(v_a_2399_);
lean_dec_ref(v_expr_2396_);
lean_dec(v___x_2348_);
lean_dec_ref(v___x_2340_);
lean_dec_ref(v_arg_2339_);
lean_dec_ref(v_arg_2336_);
lean_dec_ref(v_arg_2333_);
lean_dec_ref(v_arg_2330_);
lean_dec_ref(v_arg_2327_);
lean_dec_ref(v_e_2306_);
v_a_2468_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2403_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2403_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
else
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
lean_dec_ref(v_expr_2396_);
lean_dec(v___x_2348_);
lean_dec_ref(v___x_2340_);
lean_dec_ref(v_arg_2339_);
lean_dec_ref(v_arg_2336_);
lean_dec_ref(v_arg_2333_);
lean_dec_ref(v_arg_2330_);
lean_dec_ref(v_arg_2327_);
lean_dec_ref(v_e_2306_);
v_a_2476_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2398_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2398_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
else
{
lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2495_; 
lean_dec(v___x_2348_);
lean_dec_ref(v___x_2340_);
lean_dec_ref(v_arg_2339_);
lean_dec_ref(v_arg_2336_);
lean_dec_ref(v_arg_2333_);
lean_dec_ref(v_arg_2330_);
lean_dec_ref(v_arg_2327_);
v_isSharedCheck_2495_ = !lean_is_exclusive(v_a_2392_);
if (v_isSharedCheck_2495_ == 0)
{
lean_object* v_unused_2496_; lean_object* v_unused_2497_; 
v_unused_2496_ = lean_ctor_get(v_a_2392_, 1);
lean_dec(v_unused_2496_);
v_unused_2497_ = lean_ctor_get(v_a_2392_, 0);
lean_dec(v_unused_2497_);
v___x_2485_ = v_a_2392_;
v_isShared_2486_ = v_isSharedCheck_2495_;
goto v_resetjp_2484_;
}
else
{
lean_dec(v_a_2392_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2495_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2487_; lean_object* v___x_2489_; 
v___x_2487_ = lean_box(0);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 1, v___x_2487_);
lean_ctor_set(v___x_2485_, 0, v_e_2306_);
v___x_2489_ = v___x_2485_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_e_2306_);
lean_ctor_set(v_reuseFailAlloc_2494_, 1, v___x_2487_);
v___x_2489_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
lean_object* v___x_2490_; lean_object* v___x_2492_; 
lean_ctor_set_uint8(v___x_2489_, sizeof(void*)*2, v___x_2342_);
v___x_2490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2489_);
if (v_isShared_2395_ == 0)
{
lean_ctor_set(v___x_2394_, 0, v___x_2490_);
v___x_2492_ = v___x_2394_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2490_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
}
}
else
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
lean_dec(v___x_2348_);
lean_dec_ref(v___x_2340_);
lean_dec_ref(v_arg_2339_);
lean_dec_ref(v_arg_2336_);
lean_dec_ref(v_arg_2333_);
lean_dec_ref(v_arg_2330_);
lean_dec_ref(v_arg_2327_);
lean_dec_ref(v_e_2306_);
v_a_2499_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2501_ = v___x_2391_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2391_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_a_2499_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
}
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
lean_dec(v___x_2348_);
lean_dec_ref(v___x_2340_);
lean_dec_ref(v_arg_2339_);
lean_dec_ref(v_arg_2336_);
lean_dec_ref(v_arg_2333_);
lean_dec_ref(v_arg_2330_);
lean_dec_ref(v_arg_2327_);
lean_dec_ref(v_e_2306_);
v_a_2508_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2368_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2368_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
}
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2524_; 
lean_dec_ref(v___x_2340_);
lean_dec_ref(v_arg_2339_);
lean_dec_ref(v_arg_2336_);
lean_dec_ref(v_arg_2333_);
lean_dec_ref(v_arg_2330_);
lean_dec_ref(v_arg_2327_);
lean_dec_ref(v_e_2306_);
v_a_2517_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2519_ = v___x_2343_;
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2343_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2522_; 
if (v_isShared_2520_ == 0)
{
v___x_2522_ = v___x_2519_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_a_2517_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
}
}
}
}
}
}
v___jp_2320_:
{
lean_object* v___x_2321_; lean_object* v___x_2323_; 
v___x_2321_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__0));
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 0, v___x_2321_);
v___x_2323_ = v___x_2318_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2321_);
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
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
lean_dec_ref(v_e_2306_);
v_a_2526_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2315_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2315_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___boxed(lean_object* v_numIndices_2534_, lean_object* v_useDecideBool_2535_, lean_object* v_e_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_){
_start:
{
uint8_t v_useDecideBool_boxed_2545_; lean_object* v_res_2546_; 
v_useDecideBool_boxed_2545_ = lean_unbox(v_useDecideBool_2535_);
v_res_2546_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27(v_numIndices_2534_, v_useDecideBool_boxed_2545_, v_e_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_);
lean_dec(v_a_2543_);
lean_dec_ref(v_a_2542_);
lean_dec(v_a_2541_);
lean_dec_ref(v_a_2540_);
lean_dec(v_a_2539_);
lean_dec_ref(v_a_2538_);
lean_dec(v_a_2537_);
lean_dec(v_numIndices_2534_);
return v_res_2546_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0(void){
_start:
{
lean_object* v___x_2547_; 
v___x_2547_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_2547_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1(void){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v_s_2550_; 
v___x_2548_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__2, &l_Lean_Meta_SplitIf_getSimpContext___closed__2_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__2);
v___x_2549_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0);
v_s_2550_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_s_2550_, 0, v___x_2549_);
lean_ctor_set(v_s_2550_, 1, v___x_2549_);
lean_ctor_set(v_s_2550_, 2, v___x_2548_);
lean_ctor_set(v_s_2550_, 3, v___x_2548_);
return v_s_2550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(lean_object* v_numIndices_2614_, uint8_t v_useDecide_2615_){
_start:
{
lean_object* v_s_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; uint8_t v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v_s_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v_s_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
v_s_2617_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1);
v___x_2618_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__3));
v___x_2619_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__16));
v___x_2620_ = 0;
v___x_2621_ = lean_box(v_useDecide_2615_);
lean_inc(v_numIndices_2614_);
v___x_2622_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___boxed), 11, 2);
lean_closure_set(v___x_2622_, 0, v_numIndices_2614_);
lean_closure_set(v___x_2622_, 1, v___x_2621_);
v___x_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
v_s_2624_ = l_Lean_Meta_Simp_Simprocs_addCore(v_s_2617_, v___x_2618_, v___x_2619_, v___x_2620_, v___x_2623_);
v___x_2625_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__18));
v___x_2626_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__20));
v___x_2627_ = lean_box(v_useDecide_2615_);
v___x_2628_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___boxed), 11, 2);
lean_closure_set(v___x_2628_, 0, v_numIndices_2614_);
lean_closure_set(v___x_2628_, 1, v___x_2627_);
v___x_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2628_);
v_s_2630_ = l_Lean_Meta_Simp_Simprocs_addCore(v_s_2624_, v___x_2625_, v___x_2626_, v___x_2620_, v___x_2629_);
v___x_2631_ = lean_unsigned_to_nat(1u);
v___x_2632_ = lean_mk_empty_array_with_capacity(v___x_2631_);
v___x_2633_ = lean_array_push(v___x_2632_, v_s_2630_);
v___x_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2633_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___boxed(lean_object* v_numIndices_2635_, lean_object* v_useDecide_2636_, lean_object* v_a_2637_){
_start:
{
uint8_t v_useDecide_boxed_2638_; lean_object* v_res_2639_; 
v_useDecide_boxed_2638_ = lean_unbox(v_useDecide_2636_);
v_res_2639_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_numIndices_2635_, v_useDecide_boxed_2638_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs(lean_object* v_numIndices_2640_, uint8_t v_useDecide_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_){
_start:
{
lean_object* v___x_2647_; 
v___x_2647_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_numIndices_2640_, v_useDecide_2641_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___boxed(lean_object* v_numIndices_2648_, lean_object* v_useDecide_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_){
_start:
{
uint8_t v_useDecide_boxed_2655_; lean_object* v_res_2656_; 
v_useDecide_boxed_2655_ = lean_unbox(v_useDecide_2649_);
v_res_2656_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs(v_numIndices_2648_, v_useDecide_boxed_2655_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
lean_dec(v_a_2651_);
lean_dec_ref(v_a_2650_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(uint8_t v_useDecide_2657_, lean_object* v_a_2658_){
_start:
{
lean_object* v_lctx_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v_lctx_2660_ = lean_ctor_get(v_a_2658_, 2);
lean_inc_ref(v_lctx_2660_);
v___x_2661_ = lean_local_ctx_num_indices(v_lctx_2660_);
v___x_2662_ = lean_box(v_useDecide_2657_);
v___x_2663_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___boxed), 11, 2);
lean_closure_set(v___x_2663_, 0, v___x_2661_);
lean_closure_set(v___x_2663_, 1, v___x_2662_);
v___x_2664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2664_, 0, v___x_2663_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg___boxed(lean_object* v_useDecide_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_){
_start:
{
uint8_t v_useDecide_boxed_2668_; lean_object* v_res_2669_; 
v_useDecide_boxed_2668_ = lean_unbox(v_useDecide_2665_);
v_res_2669_ = l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(v_useDecide_boxed_2668_, v_a_2666_);
lean_dec_ref(v_a_2666_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f(uint8_t v_useDecide_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_){
_start:
{
lean_object* v___x_2676_; 
v___x_2676_ = l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(v_useDecide_2670_, v_a_2671_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed(lean_object* v_useDecide_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_){
_start:
{
uint8_t v_useDecide_boxed_2683_; lean_object* v_res_2684_; 
v_useDecide_boxed_2683_ = lean_unbox(v_useDecide_2677_);
v_res_2684_ = l_Lean_Meta_SplitIf_mkDischarge_x3f(v_useDecide_boxed_2683_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
lean_dec(v_a_2681_);
lean_dec_ref(v_a_2680_);
lean_dec(v_a_2679_);
lean_dec_ref(v_a_2678_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(lean_object* v_mvarId_2685_, lean_object* v_x_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
lean_object* v___x_2692_; 
v___x_2692_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2685_, v_x_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2695_ = v___x_2692_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2692_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2693_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
else
{
lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2708_; 
v_a_2701_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2703_ = v___x_2692_;
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_dec(v___x_2692_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2706_; 
if (v_isShared_2704_ == 0)
{
v___x_2706_ = v___x_2703_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_a_2701_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_2709_, lean_object* v_x_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2709_, v_x_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0(lean_object* v_00_u03b1_2717_, lean_object* v_mvarId_2718_, lean_object* v_x_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2718_, v_x_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___boxed(lean_object* v_00_u03b1_2726_, lean_object* v_mvarId_2727_, lean_object* v_x_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v_res_2734_; 
v_res_2734_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0(v_00_u03b1_2726_, v_mvarId_2727_, v_x_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
return v_res_2734_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2736_ = ((lean_object*)(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__0));
v___x_2737_ = l_Lean_stringToMessageData(v___x_2736_);
return v___x_2737_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2739_ = ((lean_object*)(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__2));
v___x_2740_ = l_Lean_stringToMessageData(v___x_2739_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0(lean_object* v_e_2741_, lean_object* v_mvarId_2742_, lean_object* v_hName_x3f_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v___x_2752_; lean_object* v_a_2753_; lean_object* v___x_2754_; 
v___x_2752_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_2741_, v___y_2745_);
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
lean_inc_n(v_a_2753_, 2);
lean_dec_ref(v___x_2752_);
v___x_2754_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(v_a_2753_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; 
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_a_2755_);
lean_dec_ref(v___x_2754_);
if (lean_obj_tag(v_a_2755_) == 1)
{
lean_object* v_val_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2830_; 
lean_dec(v_a_2753_);
v_val_2756_ = lean_ctor_get(v_a_2755_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v_a_2755_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2758_ = v_a_2755_;
v_isShared_2759_ = v_isSharedCheck_2830_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_val_2756_);
lean_dec(v_a_2755_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2830_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v_fst_2760_; lean_object* v_snd_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2829_; 
v_fst_2760_ = lean_ctor_get(v_val_2756_, 0);
v_snd_2761_ = lean_ctor_get(v_val_2756_, 1);
v_isSharedCheck_2829_ = !lean_is_exclusive(v_val_2756_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2763_ = v_val_2756_;
v_isShared_2764_ = v_isSharedCheck_2829_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_snd_2761_);
lean_inc(v_fst_2760_);
lean_dec(v_val_2756_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2829_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v_hName_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; 
if (lean_obj_tag(v_hName_x3f_2743_) == 0)
{
lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2817_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__1));
v___x_2818_ = l_Lean_Core_mkFreshUserName(v___x_2817_, v___y_2746_, v___y_2747_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
lean_dec_ref(v___x_2818_);
v_hName_2792_ = v_a_2819_;
v___y_2793_ = v___y_2744_;
v___y_2794_ = v___y_2745_;
v___y_2795_ = v___y_2746_;
v___y_2796_ = v___y_2747_;
goto v___jp_2791_;
}
else
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
lean_del_object(v___x_2763_);
lean_dec(v_snd_2761_);
lean_dec(v_fst_2760_);
lean_del_object(v___x_2758_);
lean_dec(v_mvarId_2742_);
v_a_2820_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2822_ = v___x_2818_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2818_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2820_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
else
{
lean_object* v_val_2828_; 
v_val_2828_ = lean_ctor_get(v_hName_x3f_2743_, 0);
lean_inc(v_val_2828_);
lean_dec_ref(v_hName_x3f_2743_);
v_hName_2792_ = v_val_2828_;
v___y_2793_ = v___y_2744_;
v___y_2794_ = v___y_2745_;
v___y_2795_ = v___y_2746_;
v___y_2796_ = v___y_2747_;
goto v___jp_2791_;
}
v___jp_2765_:
{
lean_object* v___x_2771_; 
v___x_2771_ = l_Lean_MVarId_byCasesDec(v_mvarId_2742_, v_fst_2760_, v_snd_2761_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2782_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2774_ = v___x_2771_;
v_isShared_2775_ = v_isSharedCheck_2782_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2771_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2782_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v_a_2772_);
v___x_2777_ = v___x_2758_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2772_);
v___x_2777_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
lean_object* v___x_2779_; 
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 0, v___x_2777_);
v___x_2779_ = v___x_2774_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2777_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
else
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2790_; 
lean_del_object(v___x_2758_);
v_a_2783_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2785_ = v___x_2771_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2771_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2783_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
}
v___jp_2791_:
{
lean_object* v_options_2797_; uint8_t v_hasTrace_2798_; 
v_options_2797_ = lean_ctor_get(v___y_2795_, 2);
v_hasTrace_2798_ = lean_ctor_get_uint8(v_options_2797_, sizeof(void*)*1);
if (v_hasTrace_2798_ == 0)
{
lean_del_object(v___x_2763_);
v___y_2766_ = v_hName_2792_;
v___y_2767_ = v___y_2793_;
v___y_2768_ = v___y_2794_;
v___y_2769_ = v___y_2795_;
v___y_2770_ = v___y_2796_;
goto v___jp_2765_;
}
else
{
lean_object* v_inheritedTraceOptions_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; uint8_t v___x_2802_; 
v_inheritedTraceOptions_2799_ = lean_ctor_get(v___y_2795_, 13);
v___x_2800_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10));
v___x_2801_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11);
v___x_2802_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2799_, v_options_2797_, v___x_2801_);
if (v___x_2802_ == 0)
{
lean_del_object(v___x_2763_);
v___y_2766_ = v_hName_2792_;
v___y_2767_ = v___y_2793_;
v___y_2768_ = v___y_2794_;
v___y_2769_ = v___y_2795_;
v___y_2770_ = v___y_2796_;
goto v___jp_2765_;
}
else
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2806_; 
v___x_2803_ = lean_obj_once(&l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1, &l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1_once, _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1);
lean_inc(v_snd_2761_);
v___x_2804_ = l_Lean_MessageData_ofExpr(v_snd_2761_);
if (v_isShared_2764_ == 0)
{
lean_ctor_set_tag(v___x_2763_, 7);
lean_ctor_set(v___x_2763_, 1, v___x_2804_);
lean_ctor_set(v___x_2763_, 0, v___x_2803_);
v___x_2806_ = v___x_2763_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v___x_2803_);
lean_ctor_set(v_reuseFailAlloc_2816_, 1, v___x_2804_);
v___x_2806_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
lean_object* v___x_2807_; 
v___x_2807_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_2800_, v___x_2806_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_dec_ref(v___x_2807_);
v___y_2766_ = v_hName_2792_;
v___y_2767_ = v___y_2793_;
v___y_2768_ = v___y_2794_;
v___y_2769_ = v___y_2795_;
v___y_2770_ = v___y_2796_;
goto v___jp_2765_;
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
lean_dec(v_hName_2792_);
lean_dec(v_snd_2761_);
lean_dec(v_fst_2760_);
lean_del_object(v___x_2758_);
lean_dec(v_mvarId_2742_);
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2807_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2807_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
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
lean_object* v_options_2831_; uint8_t v_hasTrace_2832_; 
lean_dec(v_a_2755_);
lean_dec(v_hName_x3f_2743_);
lean_dec(v_mvarId_2742_);
v_options_2831_ = lean_ctor_get(v___y_2746_, 2);
v_hasTrace_2832_ = lean_ctor_get_uint8(v_options_2831_, sizeof(void*)*1);
if (v_hasTrace_2832_ == 0)
{
lean_dec(v_a_2753_);
goto v___jp_2749_;
}
else
{
lean_object* v_inheritedTraceOptions_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; uint8_t v___x_2836_; 
v_inheritedTraceOptions_2833_ = lean_ctor_get(v___y_2746_, 13);
v___x_2834_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10));
v___x_2835_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11);
v___x_2836_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2833_, v_options_2831_, v___x_2835_);
if (v___x_2836_ == 0)
{
lean_dec(v_a_2753_);
goto v___jp_2749_;
}
else
{
lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2837_ = lean_obj_once(&l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3, &l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3_once, _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3);
v___x_2838_ = l_Lean_indentExpr(v_a_2753_);
v___x_2839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2837_);
lean_ctor_set(v___x_2839_, 1, v___x_2838_);
v___x_2840_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_2834_, v___x_2839_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_dec_ref(v___x_2840_);
goto v___jp_2749_;
}
else
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2848_; 
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2843_ = v___x_2840_;
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2840_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2846_; 
if (v_isShared_2844_ == 0)
{
v___x_2846_ = v___x_2843_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2841_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
lean_dec(v_a_2753_);
lean_dec(v_hName_x3f_2743_);
lean_dec(v_mvarId_2742_);
v_a_2849_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2754_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2754_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
v___jp_2749_:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2750_ = lean_box(0);
v___x_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2750_);
return v___x_2751_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___boxed(lean_object* v_e_2857_, lean_object* v_mvarId_2858_, lean_object* v_hName_x3f_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0(v_e_2857_, v_mvarId_2858_, v_hName_x3f_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
lean_dec(v___y_2863_);
lean_dec_ref(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f(lean_object* v_mvarId_2866_, lean_object* v_e_2867_, lean_object* v_hName_x3f_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_){
_start:
{
lean_object* v___f_2874_; lean_object* v___x_2875_; 
lean_inc(v_mvarId_2866_);
v___f_2874_ = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2874_, 0, v_e_2867_);
lean_closure_set(v___f_2874_, 1, v_mvarId_2866_);
lean_closure_set(v___f_2874_, 2, v_hName_x3f_2868_);
v___x_2875_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2866_, v___f_2874_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___boxed(lean_object* v_mvarId_2876_, lean_object* v_e_2877_, lean_object* v_hName_x3f_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(v_mvarId_2876_, v_e_2877_, v_hName_x3f_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_);
lean_dec(v_a_2882_);
lean_dec_ref(v_a_2881_);
lean_dec(v_a_2880_);
lean_dec_ref(v_a_2879_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0(lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v_lctx_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v_lctx_2890_ = lean_ctor_get(v___y_2885_, 2);
lean_inc_ref(v_lctx_2890_);
lean_dec_ref(v___y_2885_);
v___x_2891_ = lean_local_ctx_num_indices(v_lctx_2890_);
v___x_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2891_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0___boxed(lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
lean_object* v_res_2898_; 
v_res_2898_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0(v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
lean_dec(v___y_2896_);
lean_dec_ref(v___y_2895_);
lean_dec(v___y_2894_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(lean_object* v_mvarId_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_){
_start:
{
lean_object* v___f_2906_; lean_object* v___x_2907_; 
v___f_2906_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___closed__0));
v___x_2907_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2900_, v___f_2906_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_);
return v___x_2907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___boxed(lean_object* v_mvarId_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(v_mvarId_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
lean_dec(v_a_2912_);
lean_dec_ref(v_a_2911_);
lean_dec(v_a_2910_);
lean_dec_ref(v_a_2909_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_simpIfTarget_spec__0(lean_object* v_msg_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v___f_2922_; lean_object* v___x_1955__overap_2923_; lean_object* v___x_2924_; 
v___f_2922_ = ((lean_object*)(l_panic___at___00Lean_Meta_simpIfTarget_spec__0___closed__0));
v___x_1955__overap_2923_ = lean_panic_fn_borrowed(v___f_2922_, v_msg_2916_);
lean_inc(v___y_2920_);
lean_inc_ref(v___y_2919_);
lean_inc(v___y_2918_);
lean_inc_ref(v___y_2917_);
v___x_2924_ = lean_apply_5(v___x_1955__overap_2923_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, lean_box(0));
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_simpIfTarget_spec__0___boxed(lean_object* v_msg_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v_msg_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
return v_res_2931_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(lean_object* v_opts_2932_, lean_object* v_opt_2933_){
_start:
{
lean_object* v_name_2934_; lean_object* v_defValue_2935_; lean_object* v_map_2936_; lean_object* v___x_2937_; 
v_name_2934_ = lean_ctor_get(v_opt_2933_, 0);
v_defValue_2935_ = lean_ctor_get(v_opt_2933_, 1);
v_map_2936_ = lean_ctor_get(v_opts_2932_, 0);
v___x_2937_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2936_, v_name_2934_);
if (lean_obj_tag(v___x_2937_) == 0)
{
uint8_t v___x_2938_; 
v___x_2938_ = lean_unbox(v_defValue_2935_);
return v___x_2938_;
}
else
{
lean_object* v_val_2939_; 
v_val_2939_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_val_2939_);
lean_dec_ref(v___x_2937_);
if (lean_obj_tag(v_val_2939_) == 1)
{
uint8_t v_v_2940_; 
v_v_2940_ = lean_ctor_get_uint8(v_val_2939_, 0);
lean_dec_ref(v_val_2939_);
return v_v_2940_;
}
else
{
uint8_t v___x_2941_; 
lean_dec(v_val_2939_);
v___x_2941_ = lean_unbox(v_defValue_2935_);
return v___x_2941_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1___boxed(lean_object* v_opts_2942_, lean_object* v_opt_2943_){
_start:
{
uint8_t v_res_2944_; lean_object* v_r_2945_; 
v_res_2944_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v_opts_2942_, v_opt_2943_);
lean_dec_ref(v_opt_2943_);
lean_dec_ref(v_opts_2942_);
v_r_2945_ = lean_box(v_res_2944_);
return v_r_2945_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__0(void){
_start:
{
lean_object* v___x_2946_; 
v___x_2946_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2946_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__1(void){
_start:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2947_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__0, &l_Lean_Meta_simpIfTarget___closed__0_once, _init_l_Lean_Meta_simpIfTarget___closed__0);
v___x_2948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2947_);
return v___x_2948_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__2(void){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2949_ = lean_unsigned_to_nat(0u);
v___x_2950_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__1, &l_Lean_Meta_simpIfTarget___closed__1_once, _init_l_Lean_Meta_simpIfTarget___closed__1);
v___x_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
lean_ctor_set(v___x_2951_, 1, v___x_2949_);
return v___x_2951_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__3(void){
_start:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2952_ = lean_unsigned_to_nat(32u);
v___x_2953_ = lean_mk_empty_array_with_capacity(v___x_2952_);
v___x_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
return v___x_2954_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__4(void){
_start:
{
size_t v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2955_ = ((size_t)5ULL);
v___x_2956_ = lean_unsigned_to_nat(0u);
v___x_2957_ = lean_unsigned_to_nat(32u);
v___x_2958_ = lean_mk_empty_array_with_capacity(v___x_2957_);
v___x_2959_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__3, &l_Lean_Meta_simpIfTarget___closed__3_once, _init_l_Lean_Meta_simpIfTarget___closed__3);
v___x_2960_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
lean_ctor_set(v___x_2960_, 1, v___x_2958_);
lean_ctor_set(v___x_2960_, 2, v___x_2956_);
lean_ctor_set(v___x_2960_, 3, v___x_2956_);
lean_ctor_set_usize(v___x_2960_, 4, v___x_2955_);
return v___x_2960_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__5(void){
_start:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2961_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__4, &l_Lean_Meta_simpIfTarget___closed__4_once, _init_l_Lean_Meta_simpIfTarget___closed__4);
v___x_2962_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__1, &l_Lean_Meta_simpIfTarget___closed__1_once, _init_l_Lean_Meta_simpIfTarget___closed__1);
v___x_2963_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2962_);
lean_ctor_set(v___x_2963_, 1, v___x_2962_);
lean_ctor_set(v___x_2963_, 2, v___x_2962_);
lean_ctor_set(v___x_2963_, 3, v___x_2961_);
return v___x_2963_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__6(void){
_start:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2964_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__5, &l_Lean_Meta_simpIfTarget___closed__5_once, _init_l_Lean_Meta_simpIfTarget___closed__5);
v___x_2965_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__2, &l_Lean_Meta_simpIfTarget___closed__2_once, _init_l_Lean_Meta_simpIfTarget___closed__2);
v___x_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2965_);
lean_ctor_set(v___x_2966_, 1, v___x_2964_);
return v___x_2966_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__10(void){
_start:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2970_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__9));
v___x_2971_ = lean_unsigned_to_nat(78u);
v___x_2972_ = lean_unsigned_to_nat(289u);
v___x_2973_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__8));
v___x_2974_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_2975_ = l_mkPanicMessageWithDecl(v___x_2974_, v___x_2973_, v___x_2972_, v___x_2971_, v___x_2970_);
return v___x_2975_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__12(void){
_start:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2978_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__9));
v___x_2979_ = lean_unsigned_to_nat(128u);
v___x_2980_ = lean_unsigned_to_nat(293u);
v___x_2981_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__8));
v___x_2982_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_2983_ = l_mkPanicMessageWithDecl(v___x_2982_, v___x_2981_, v___x_2980_, v___x_2979_, v___x_2978_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfTarget(lean_object* v_mvarId_2984_, uint8_t v_useDecide_2985_, uint8_t v_useNewSemantics_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_){
_start:
{
if (v_useNewSemantics_2986_ == 0)
{
lean_object* v_options_3039_; lean_object* v___x_3040_; uint8_t v___x_3041_; 
v_options_3039_ = lean_ctor_get(v_a_2989_, 2);
v___x_3040_ = l_Lean_Meta_backward_split;
v___x_3041_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v_options_3039_, v___x_3040_);
if (v___x_3041_ == 0)
{
goto v___jp_2992_;
}
else
{
lean_object* v___x_3042_; 
v___x_3042_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3043_);
lean_dec_ref(v___x_3042_);
v___x_3044_ = lean_box(v_useDecide_2985_);
v___x_3045_ = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed), 6, 1);
lean_closure_set(v___x_3045_, 0, v___x_3044_);
lean_inc(v_mvarId_2984_);
v___x_3046_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2984_, v___x_3045_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v_a_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
lean_inc(v_a_3047_);
lean_dec_ref(v___x_3046_);
v___x_3048_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__11));
v___x_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3049_, 0, v_a_3047_);
v___x_3050_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__6, &l_Lean_Meta_simpIfTarget___closed__6_once, _init_l_Lean_Meta_simpIfTarget___closed__6);
v___x_3051_ = l_Lean_Meta_simpTarget(v_mvarId_2984_, v_a_3043_, v___x_3048_, v___x_3049_, v_useNewSemantics_2986_, v___x_3050_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3063_; 
v_a_3052_ = lean_ctor_get(v___x_3051_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3054_ = v___x_3051_;
v_isShared_3055_ = v_isSharedCheck_3063_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_3051_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3063_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v_fst_3056_; 
v_fst_3056_ = lean_ctor_get(v_a_3052_, 0);
lean_inc(v_fst_3056_);
lean_dec(v_a_3052_);
if (lean_obj_tag(v_fst_3056_) == 1)
{
lean_object* v_val_3057_; lean_object* v___x_3059_; 
v_val_3057_ = lean_ctor_get(v_fst_3056_, 0);
lean_inc(v_val_3057_);
lean_dec_ref(v_fst_3056_);
if (v_isShared_3055_ == 0)
{
lean_ctor_set(v___x_3054_, 0, v_val_3057_);
v___x_3059_ = v___x_3054_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_val_3057_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
else
{
lean_object* v___x_3061_; lean_object* v___x_3062_; 
lean_dec(v_fst_3056_);
lean_del_object(v___x_3054_);
v___x_3061_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__12, &l_Lean_Meta_simpIfTarget___closed__12_once, _init_l_Lean_Meta_simpIfTarget___closed__12);
v___x_3062_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3061_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
return v___x_3062_;
}
}
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
v_a_3064_ = lean_ctor_get(v___x_3051_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_3051_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_3051_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3064_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
}
else
{
lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3079_; 
lean_dec(v_a_3043_);
lean_dec(v_mvarId_2984_);
v_a_3072_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3074_ = v___x_3046_;
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_3046_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3077_; 
if (v_isShared_3075_ == 0)
{
v___x_3077_ = v___x_3074_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_a_3072_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
}
else
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
lean_dec(v_mvarId_2984_);
v_a_3080_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3042_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3042_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
}
else
{
goto v___jp_2992_;
}
v___jp_2992_:
{
lean_object* v___x_2993_; 
v___x_2993_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_2987_, v_a_2989_, v_a_2990_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v___x_2995_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_a_2994_);
lean_dec_ref(v___x_2993_);
lean_inc(v_mvarId_2984_);
v___x_2995_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(v_mvarId_2984_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_a_2996_; lean_object* v___x_2997_; lean_object* v_a_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_a_2996_);
lean_dec_ref(v___x_2995_);
v___x_2997_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_a_2996_, v_useDecide_2985_);
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
lean_dec_ref(v___x_2997_);
v___x_2999_ = lean_box(0);
v___x_3000_ = 0;
v___x_3001_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__6, &l_Lean_Meta_simpIfTarget___closed__6_once, _init_l_Lean_Meta_simpIfTarget___closed__6);
v___x_3002_ = l_Lean_Meta_simpTarget(v_mvarId_2984_, v_a_2994_, v_a_2998_, v___x_2999_, v___x_3000_, v___x_3001_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3014_; 
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3005_ = v___x_3002_;
v_isShared_3006_ = v_isSharedCheck_3014_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_3002_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3014_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v_fst_3007_; 
v_fst_3007_ = lean_ctor_get(v_a_3003_, 0);
lean_inc(v_fst_3007_);
lean_dec(v_a_3003_);
if (lean_obj_tag(v_fst_3007_) == 1)
{
lean_object* v_val_3008_; lean_object* v___x_3010_; 
v_val_3008_ = lean_ctor_get(v_fst_3007_, 0);
lean_inc(v_val_3008_);
lean_dec_ref(v_fst_3007_);
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 0, v_val_3008_);
v___x_3010_ = v___x_3005_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_val_3008_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
else
{
lean_object* v___x_3012_; lean_object* v___x_3013_; 
lean_dec(v_fst_3007_);
lean_del_object(v___x_3005_);
v___x_3012_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__10, &l_Lean_Meta_simpIfTarget___closed__10_once, _init_l_Lean_Meta_simpIfTarget___closed__10);
v___x_3013_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3012_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
return v___x_3013_;
}
}
}
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
v_a_3015_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_3002_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_3002_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3015_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
}
else
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
lean_dec(v_a_2994_);
lean_dec(v_mvarId_2984_);
v_a_3023_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_2995_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_2995_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
else
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3038_; 
lean_dec(v_mvarId_2984_);
v_a_3031_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3033_ = v___x_2993_;
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_2993_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3036_; 
if (v_isShared_3034_ == 0)
{
v___x_3036_ = v___x_3033_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3031_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfTarget___boxed(lean_object* v_mvarId_3088_, lean_object* v_useDecide_3089_, lean_object* v_useNewSemantics_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_){
_start:
{
uint8_t v_useDecide_boxed_3096_; uint8_t v_useNewSemantics_boxed_3097_; lean_object* v_res_3098_; 
v_useDecide_boxed_3096_ = lean_unbox(v_useDecide_3089_);
v_useNewSemantics_boxed_3097_ = lean_unbox(v_useNewSemantics_3090_);
v_res_3098_ = l_Lean_Meta_simpIfTarget(v_mvarId_3088_, v_useDecide_boxed_3096_, v_useNewSemantics_boxed_3097_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_);
lean_dec(v_a_3094_);
lean_dec_ref(v_a_3093_);
lean_dec(v_a_3092_);
lean_dec_ref(v_a_3091_);
return v_res_3098_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfLocalDecl___closed__1(void){
_start:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3100_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__9));
v___x_3101_ = lean_unsigned_to_nat(93u);
v___x_3102_ = lean_unsigned_to_nat(305u);
v___x_3103_ = ((lean_object*)(l_Lean_Meta_simpIfLocalDecl___closed__0));
v___x_3104_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_3105_ = l_mkPanicMessageWithDecl(v___x_3104_, v___x_3103_, v___x_3102_, v___x_3101_, v___x_3100_);
return v___x_3105_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfLocalDecl___closed__2(void){
_start:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3106_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__9));
v___x_3107_ = lean_unsigned_to_nat(133u);
v___x_3108_ = lean_unsigned_to_nat(309u);
v___x_3109_ = ((lean_object*)(l_Lean_Meta_simpIfLocalDecl___closed__0));
v___x_3110_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_3111_ = l_mkPanicMessageWithDecl(v___x_3110_, v___x_3109_, v___x_3108_, v___x_3107_, v___x_3106_);
return v___x_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfLocalDecl(lean_object* v_mvarId_3112_, lean_object* v_fvarId_3113_, uint8_t v_useNewSemantics_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_){
_start:
{
if (v_useNewSemantics_3114_ == 0)
{
lean_object* v_options_3168_; lean_object* v___x_3169_; uint8_t v___x_3170_; 
v_options_3168_ = lean_ctor_get(v_a_3117_, 2);
v___x_3169_ = l_Lean_Meta_backward_split;
v___x_3170_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v_options_3168_, v___x_3169_);
if (v___x_3170_ == 0)
{
goto v___jp_3120_;
}
else
{
lean_object* v___x_3171_; 
v___x_3171_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v_a_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v_a_3172_ = lean_ctor_get(v___x_3171_, 0);
lean_inc(v_a_3172_);
lean_dec_ref(v___x_3171_);
v___x_3173_ = lean_box(v_useNewSemantics_3114_);
v___x_3174_ = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed), 6, 1);
lean_closure_set(v___x_3174_, 0, v___x_3173_);
lean_inc(v_mvarId_3112_);
v___x_3175_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_3112_, v___x_3174_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_);
if (lean_obj_tag(v___x_3175_) == 0)
{
lean_object* v_a_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v_a_3176_ = lean_ctor_get(v___x_3175_, 0);
lean_inc(v_a_3176_);
lean_dec_ref(v___x_3175_);
v___x_3177_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__11));
v___x_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3178_, 0, v_a_3176_);
v___x_3179_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__6, &l_Lean_Meta_simpIfTarget___closed__6_once, _init_l_Lean_Meta_simpIfTarget___closed__6);
v___x_3180_ = l_Lean_Meta_simpLocalDecl(v_mvarId_3112_, v_fvarId_3113_, v_a_3172_, v___x_3177_, v___x_3178_, v_useNewSemantics_3114_, v___x_3179_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3193_; 
v_a_3181_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3183_ = v___x_3180_;
v_isShared_3184_ = v_isSharedCheck_3193_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3180_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3193_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v_fst_3185_; 
v_fst_3185_ = lean_ctor_get(v_a_3181_, 0);
lean_inc(v_fst_3185_);
lean_dec(v_a_3181_);
if (lean_obj_tag(v_fst_3185_) == 1)
{
lean_object* v_val_3186_; lean_object* v_snd_3187_; lean_object* v___x_3189_; 
v_val_3186_ = lean_ctor_get(v_fst_3185_, 0);
lean_inc(v_val_3186_);
lean_dec_ref(v_fst_3185_);
v_snd_3187_ = lean_ctor_get(v_val_3186_, 1);
lean_inc(v_snd_3187_);
lean_dec(v_val_3186_);
if (v_isShared_3184_ == 0)
{
lean_ctor_set(v___x_3183_, 0, v_snd_3187_);
v___x_3189_ = v___x_3183_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_snd_3187_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
else
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
lean_dec(v_fst_3185_);
lean_del_object(v___x_3183_);
v___x_3191_ = lean_obj_once(&l_Lean_Meta_simpIfLocalDecl___closed__2, &l_Lean_Meta_simpIfLocalDecl___closed__2_once, _init_l_Lean_Meta_simpIfLocalDecl___closed__2);
v___x_3192_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3191_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_);
return v___x_3192_;
}
}
}
else
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3201_; 
v_a_3194_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3196_ = v___x_3180_;
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3180_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
if (v_isShared_3197_ == 0)
{
v___x_3199_ = v___x_3196_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_a_3194_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec(v_a_3172_);
lean_dec(v_fvarId_3113_);
lean_dec(v_mvarId_3112_);
v_a_3202_ = lean_ctor_get(v___x_3175_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3175_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3175_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
else
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3217_; 
lean_dec(v_fvarId_3113_);
lean_dec(v_mvarId_3112_);
v_a_3210_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3212_ = v___x_3171_;
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___x_3171_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3215_; 
if (v_isShared_3213_ == 0)
{
v___x_3215_ = v___x_3212_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_a_3210_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
}
}
else
{
goto v___jp_3120_;
}
v___jp_3120_:
{
lean_object* v___x_3121_; 
v___x_3121_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_3115_, v_a_3117_, v_a_3118_);
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_object* v_a_3122_; lean_object* v___x_3123_; 
v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
lean_inc(v_a_3122_);
lean_dec_ref(v___x_3121_);
lean_inc(v_mvarId_3112_);
v___x_3123_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(v_mvarId_3112_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v_a_3124_; uint8_t v___x_3125_; lean_object* v___x_3126_; lean_object* v_a_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
lean_inc(v_a_3124_);
lean_dec_ref(v___x_3123_);
v___x_3125_ = 0;
v___x_3126_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_a_3124_, v___x_3125_);
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_a_3127_);
lean_dec_ref(v___x_3126_);
v___x_3128_ = lean_box(0);
v___x_3129_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__6, &l_Lean_Meta_simpIfTarget___closed__6_once, _init_l_Lean_Meta_simpIfTarget___closed__6);
v___x_3130_ = l_Lean_Meta_simpLocalDecl(v_mvarId_3112_, v_fvarId_3113_, v_a_3122_, v_a_3127_, v___x_3128_, v___x_3125_, v___x_3129_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3143_; 
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3133_ = v___x_3130_;
v_isShared_3134_ = v_isSharedCheck_3143_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3130_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3143_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v_fst_3135_; 
v_fst_3135_ = lean_ctor_get(v_a_3131_, 0);
lean_inc(v_fst_3135_);
lean_dec(v_a_3131_);
if (lean_obj_tag(v_fst_3135_) == 1)
{
lean_object* v_val_3136_; lean_object* v_snd_3137_; lean_object* v___x_3139_; 
v_val_3136_ = lean_ctor_get(v_fst_3135_, 0);
lean_inc(v_val_3136_);
lean_dec_ref(v_fst_3135_);
v_snd_3137_ = lean_ctor_get(v_val_3136_, 1);
lean_inc(v_snd_3137_);
lean_dec(v_val_3136_);
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 0, v_snd_3137_);
v___x_3139_ = v___x_3133_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_snd_3137_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
else
{
lean_object* v___x_3141_; lean_object* v___x_3142_; 
lean_dec(v_fst_3135_);
lean_del_object(v___x_3133_);
v___x_3141_ = lean_obj_once(&l_Lean_Meta_simpIfLocalDecl___closed__1, &l_Lean_Meta_simpIfLocalDecl___closed__1_once, _init_l_Lean_Meta_simpIfLocalDecl___closed__1);
v___x_3142_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3141_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_);
return v___x_3142_;
}
}
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
v_a_3144_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3130_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3130_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
else
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_dec(v_a_3122_);
lean_dec(v_fvarId_3113_);
lean_dec(v_mvarId_3112_);
v_a_3152_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3123_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3123_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
lean_dec(v_fvarId_3113_);
lean_dec(v_mvarId_3112_);
v_a_3160_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3121_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3121_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfLocalDecl___boxed(lean_object* v_mvarId_3218_, lean_object* v_fvarId_3219_, lean_object* v_useNewSemantics_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_){
_start:
{
uint8_t v_useNewSemantics_boxed_3226_; lean_object* v_res_3227_; 
v_useNewSemantics_boxed_3226_ = lean_unbox(v_useNewSemantics_3220_);
v_res_3227_ = l_Lean_Meta_simpIfLocalDecl(v_mvarId_3218_, v_fvarId_3219_, v_useNewSemantics_boxed_3226_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_);
lean_dec(v_a_3224_);
lean_dec_ref(v_a_3223_);
lean_dec(v_a_3222_);
lean_dec_ref(v_a_3221_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(lean_object* v_x_x3f_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
lean_object* v___x_3234_; 
v___x_3234_ = l_Lean_Meta_saveState___redArg(v___y_3230_, v___y_3232_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3279_; 
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3237_ = v___x_3234_;
v_isShared_3238_ = v_isSharedCheck_3279_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3234_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3279_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___y_3240_; uint8_t v___y_3241_; lean_object* v_a_3263_; lean_object* v___x_3266_; 
lean_inc(v___y_3232_);
lean_inc_ref(v___y_3231_);
lean_inc(v___y_3230_);
lean_inc_ref(v___y_3229_);
v___x_3266_ = lean_apply_5(v_x_x3f_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, lean_box(0));
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_a_3267_; 
v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_a_3267_);
if (lean_obj_tag(v_a_3267_) == 0)
{
lean_object* v___x_3268_; 
lean_dec_ref(v___x_3266_);
v___x_3268_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3235_, v___y_3230_, v___y_3232_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3275_; 
lean_del_object(v___x_3237_);
lean_dec(v_a_3235_);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3275_ == 0)
{
lean_object* v_unused_3276_; 
v_unused_3276_ = lean_ctor_get(v___x_3268_, 0);
lean_dec(v_unused_3276_);
v___x_3270_ = v___x_3268_;
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
else
{
lean_dec(v___x_3268_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3273_; 
if (v_isShared_3271_ == 0)
{
lean_ctor_set(v___x_3270_, 0, v_a_3267_);
v___x_3273_ = v___x_3270_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_a_3267_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
}
else
{
lean_object* v_a_3277_; 
v_a_3277_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3277_);
lean_dec_ref(v___x_3268_);
v_a_3263_ = v_a_3277_;
goto v___jp_3262_;
}
}
else
{
lean_dec_ref(v_a_3267_);
lean_del_object(v___x_3237_);
lean_dec(v_a_3235_);
return v___x_3266_;
}
}
else
{
lean_object* v_a_3278_; 
v_a_3278_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_a_3278_);
lean_dec_ref(v___x_3266_);
v_a_3263_ = v_a_3278_;
goto v___jp_3262_;
}
v___jp_3239_:
{
if (v___y_3241_ == 0)
{
lean_object* v___x_3242_; 
lean_del_object(v___x_3237_);
v___x_3242_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3235_, v___y_3230_, v___y_3232_);
lean_dec(v_a_3235_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3249_ == 0)
{
lean_object* v_unused_3250_; 
v_unused_3250_ = lean_ctor_get(v___x_3242_, 0);
lean_dec(v_unused_3250_);
v___x_3244_ = v___x_3242_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_dec(v___x_3242_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3247_; 
if (v_isShared_3245_ == 0)
{
lean_ctor_set_tag(v___x_3244_, 1);
lean_ctor_set(v___x_3244_, 0, v___y_3240_);
v___x_3247_ = v___x_3244_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___y_3240_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
else
{
lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3258_; 
lean_dec_ref(v___y_3240_);
v_a_3251_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3253_ = v___x_3242_;
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3242_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3256_; 
if (v_isShared_3254_ == 0)
{
v___x_3256_ = v___x_3253_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_a_3251_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
}
else
{
lean_object* v___x_3260_; 
lean_dec(v_a_3235_);
if (v_isShared_3238_ == 0)
{
lean_ctor_set_tag(v___x_3237_, 1);
lean_ctor_set(v___x_3237_, 0, v___y_3240_);
v___x_3260_ = v___x_3237_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v___y_3240_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
v___jp_3262_:
{
uint8_t v___x_3264_; 
v___x_3264_ = l_Lean_Exception_isInterrupt(v_a_3263_);
if (v___x_3264_ == 0)
{
uint8_t v___x_3265_; 
lean_inc_ref(v_a_3263_);
v___x_3265_ = l_Lean_Exception_isRuntime(v_a_3263_);
v___y_3240_ = v_a_3263_;
v___y_3241_ = v___x_3265_;
goto v___jp_3239_;
}
else
{
v___y_3240_ = v_a_3263_;
v___y_3241_ = v___x_3264_;
goto v___jp_3239_;
}
}
}
}
else
{
lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
lean_dec_ref(v_x_x3f_3228_);
v_a_3280_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3282_ = v___x_3234_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_dec(v___x_3234_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3280_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg___boxed(lean_object* v_x_x3f_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
lean_object* v_res_3294_; 
v_res_3294_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v_x_x3f_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec(v___y_3290_);
lean_dec_ref(v___y_3289_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0(lean_object* v_00_u03b1_3295_, lean_object* v_x_x3f_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_){
_start:
{
lean_object* v___x_3302_; 
v___x_3302_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v_x_x3f_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___boxed(lean_object* v_00_u03b1_3303_, lean_object* v_x_x3f_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0(v_00_u03b1_3303_, v_x_x3f_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
return v_res_3310_;
}
}
static lean_object* _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3315_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1));
v___x_3316_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4));
v___x_3317_ = l_Lean_Name_append(v___x_3316_, v___x_3315_);
return v___x_3317_;
}
}
static lean_object* _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3319_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__3));
v___x_3320_ = l_Lean_stringToMessageData(v___x_3319_);
return v___x_3320_;
}
}
static lean_object* _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3322_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__5));
v___x_3323_ = l_Lean_stringToMessageData(v___x_3322_);
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0(lean_object* v_mvarId_3324_, lean_object* v_hName_x3f_3325_, uint8_t v_useNewSemantics_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_){
_start:
{
lean_object* v___x_3335_; 
lean_inc(v_mvarId_3324_);
v___x_3335_ = l_Lean_MVarId_getType(v_mvarId_3324_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v___x_3337_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_a_3336_);
lean_dec_ref(v___x_3335_);
v___x_3337_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(v_mvarId_3324_, v_a_3336_, v_hName_x3f_3325_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3434_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3340_ = v___x_3337_;
v_isShared_3341_ = v_isSharedCheck_3434_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3337_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3434_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
if (lean_obj_tag(v_a_3338_) == 1)
{
lean_object* v_val_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3429_; 
lean_del_object(v___x_3340_);
v_val_3342_ = lean_ctor_get(v_a_3338_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v_a_3338_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3344_ = v_a_3338_;
v_isShared_3345_ = v_isSharedCheck_3429_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_val_3342_);
lean_dec(v_a_3338_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3429_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v_fst_3346_; lean_object* v_snd_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3428_; 
v_fst_3346_ = lean_ctor_get(v_val_3342_, 0);
v_snd_3347_ = lean_ctor_get(v_val_3342_, 1);
v_isSharedCheck_3428_ = !lean_is_exclusive(v_val_3342_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3349_ = v_val_3342_;
v_isShared_3350_ = v_isSharedCheck_3428_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_snd_3347_);
lean_inc(v_fst_3346_);
lean_dec(v_val_3342_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3428_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v_mvarId_3351_; lean_object* v_fvarId_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3427_; 
v_mvarId_3351_ = lean_ctor_get(v_fst_3346_, 0);
v_fvarId_3352_ = lean_ctor_get(v_fst_3346_, 1);
v_isSharedCheck_3427_ = !lean_is_exclusive(v_fst_3346_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3354_ = v_fst_3346_;
v_isShared_3355_ = v_isSharedCheck_3427_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_fvarId_3352_);
lean_inc(v_mvarId_3351_);
lean_dec(v_fst_3346_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3427_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
uint8_t v___x_3356_; lean_object* v___x_3357_; 
v___x_3356_ = 0;
lean_inc(v_mvarId_3351_);
v___x_3357_ = l_Lean_Meta_simpIfTarget(v_mvarId_3351_, v___x_3356_, v_useNewSemantics_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_a_3358_; lean_object* v_mvarId_3359_; lean_object* v_fvarId_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3418_; 
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_a_3358_);
lean_dec_ref(v___x_3357_);
v_mvarId_3359_ = lean_ctor_get(v_snd_3347_, 0);
v_fvarId_3360_ = lean_ctor_get(v_snd_3347_, 1);
v_isSharedCheck_3418_ = !lean_is_exclusive(v_snd_3347_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3362_ = v_snd_3347_;
v_isShared_3363_ = v_isSharedCheck_3418_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_fvarId_3360_);
lean_inc(v_mvarId_3359_);
lean_dec(v_snd_3347_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3418_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v___x_3364_; 
lean_inc(v_mvarId_3359_);
v___x_3364_ = l_Lean_Meta_simpIfTarget(v_mvarId_3359_, v___x_3356_, v_useNewSemantics_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3409_; 
v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3367_ = v___x_3364_;
v_isShared_3368_ = v_isSharedCheck_3409_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v___x_3364_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3409_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
uint8_t v___x_3385_; 
v___x_3385_ = l_Lean_instBEqMVarId_beq(v_mvarId_3351_, v_a_3358_);
lean_dec(v_mvarId_3351_);
if (v___x_3385_ == 0)
{
lean_dec(v_mvarId_3359_);
goto v___jp_3369_;
}
else
{
uint8_t v___x_3386_; 
v___x_3386_ = l_Lean_instBEqMVarId_beq(v_mvarId_3359_, v_a_3365_);
lean_dec(v_mvarId_3359_);
if (v___x_3386_ == 0)
{
goto v___jp_3369_;
}
else
{
lean_object* v_options_3387_; uint8_t v_hasTrace_3388_; 
lean_del_object(v___x_3367_);
lean_del_object(v___x_3362_);
lean_dec(v_fvarId_3360_);
lean_del_object(v___x_3354_);
lean_dec(v_fvarId_3352_);
lean_del_object(v___x_3349_);
lean_del_object(v___x_3344_);
v_options_3387_ = lean_ctor_get(v___y_3329_, 2);
v_hasTrace_3388_ = lean_ctor_get_uint8(v_options_3387_, sizeof(void*)*1);
if (v_hasTrace_3388_ == 0)
{
lean_dec(v_a_3365_);
lean_dec(v_a_3358_);
goto v___jp_3332_;
}
else
{
lean_object* v_inheritedTraceOptions_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; uint8_t v___x_3392_; 
v_inheritedTraceOptions_3389_ = lean_ctor_get(v___y_3329_, 13);
v___x_3390_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1));
v___x_3391_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2);
v___x_3392_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3389_, v_options_3387_, v___x_3391_);
if (v___x_3392_ == 0)
{
lean_dec(v_a_3365_);
lean_dec(v_a_3358_);
goto v___jp_3332_;
}
else
{
lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3393_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4);
v___x_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3394_, 0, v_a_3358_);
v___x_3395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3393_);
lean_ctor_set(v___x_3395_, 1, v___x_3394_);
v___x_3396_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6);
v___x_3397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3395_);
lean_ctor_set(v___x_3397_, 1, v___x_3396_);
v___x_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3398_, 0, v_a_3365_);
v___x_3399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3397_);
lean_ctor_set(v___x_3399_, 1, v___x_3398_);
v___x_3400_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_3390_, v___x_3399_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_dec_ref(v___x_3400_);
goto v___jp_3332_;
}
else
{
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3408_; 
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3403_ = v___x_3400_;
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3400_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3406_; 
if (v_isShared_3404_ == 0)
{
v___x_3406_ = v___x_3403_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_a_3401_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
}
}
}
}
v___jp_3369_:
{
lean_object* v___x_3371_; 
if (v_isShared_3363_ == 0)
{
lean_ctor_set(v___x_3362_, 1, v_fvarId_3352_);
lean_ctor_set(v___x_3362_, 0, v_a_3358_);
v___x_3371_ = v___x_3362_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_a_3358_);
lean_ctor_set(v_reuseFailAlloc_3384_, 1, v_fvarId_3352_);
v___x_3371_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
lean_object* v___x_3373_; 
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 1, v_fvarId_3360_);
lean_ctor_set(v___x_3354_, 0, v_a_3365_);
v___x_3373_ = v___x_3354_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3365_);
lean_ctor_set(v_reuseFailAlloc_3383_, 1, v_fvarId_3360_);
v___x_3373_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
lean_object* v___x_3375_; 
if (v_isShared_3350_ == 0)
{
lean_ctor_set(v___x_3349_, 1, v___x_3373_);
lean_ctor_set(v___x_3349_, 0, v___x_3371_);
v___x_3375_ = v___x_3349_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v___x_3371_);
lean_ctor_set(v_reuseFailAlloc_3382_, 1, v___x_3373_);
v___x_3375_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
lean_object* v___x_3377_; 
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 0, v___x_3375_);
v___x_3377_ = v___x_3344_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3375_);
v___x_3377_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
lean_object* v___x_3379_; 
if (v_isShared_3368_ == 0)
{
lean_ctor_set(v___x_3367_, 0, v___x_3377_);
v___x_3379_ = v___x_3367_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3377_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
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
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
lean_del_object(v___x_3362_);
lean_dec(v_fvarId_3360_);
lean_dec(v_mvarId_3359_);
lean_dec(v_a_3358_);
lean_del_object(v___x_3354_);
lean_dec(v_fvarId_3352_);
lean_dec(v_mvarId_3351_);
lean_del_object(v___x_3349_);
lean_del_object(v___x_3344_);
v_a_3410_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v___x_3364_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3364_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3410_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
}
else
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3426_; 
lean_del_object(v___x_3354_);
lean_dec(v_fvarId_3352_);
lean_dec(v_mvarId_3351_);
lean_del_object(v___x_3349_);
lean_dec(v_snd_3347_);
lean_del_object(v___x_3344_);
v_a_3419_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3357_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3357_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3424_; 
if (v_isShared_3422_ == 0)
{
v___x_3424_ = v___x_3421_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_a_3419_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3430_; lean_object* v___x_3432_; 
lean_dec(v_a_3338_);
v___x_3430_ = lean_box(0);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 0, v___x_3430_);
v___x_3432_ = v___x_3340_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v___x_3430_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
}
else
{
return v___x_3337_;
}
}
else
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3442_; 
lean_dec(v_hName_x3f_3325_);
lean_dec(v_mvarId_3324_);
v_a_3435_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3437_ = v___x_3335_;
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3335_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3440_; 
if (v_isShared_3438_ == 0)
{
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3435_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
v___jp_3332_:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3333_ = lean_box(0);
v___x_3334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3333_);
return v___x_3334_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0___boxed(lean_object* v_mvarId_3443_, lean_object* v_hName_x3f_3444_, lean_object* v_useNewSemantics_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
uint8_t v_useNewSemantics_boxed_3451_; lean_object* v_res_3452_; 
v_useNewSemantics_boxed_3451_ = lean_unbox(v_useNewSemantics_3445_);
v_res_3452_ = l_Lean_Meta_splitIfTarget_x3f___lam__0(v_mvarId_3443_, v_hName_x3f_3444_, v_useNewSemantics_boxed_3451_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f(lean_object* v_mvarId_3453_, lean_object* v_hName_x3f_3454_, uint8_t v_useNewSemantics_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_){
_start:
{
lean_object* v___x_3461_; lean_object* v___f_3462_; lean_object* v___x_3463_; 
v___x_3461_ = lean_box(v_useNewSemantics_3455_);
v___f_3462_ = lean_alloc_closure((void*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3462_, 0, v_mvarId_3453_);
lean_closure_set(v___f_3462_, 1, v_hName_x3f_3454_);
lean_closure_set(v___f_3462_, 2, v___x_3461_);
v___x_3463_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v___f_3462_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_);
return v___x_3463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___boxed(lean_object* v_mvarId_3464_, lean_object* v_hName_x3f_3465_, lean_object* v_useNewSemantics_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_){
_start:
{
uint8_t v_useNewSemantics_boxed_3472_; lean_object* v_res_3473_; 
v_useNewSemantics_boxed_3472_ = lean_unbox(v_useNewSemantics_3466_);
v_res_3473_ = l_Lean_Meta_splitIfTarget_x3f(v_mvarId_3464_, v_hName_x3f_3465_, v_useNewSemantics_boxed_3472_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_);
lean_dec(v_a_3470_);
lean_dec_ref(v_a_3469_);
lean_dec(v_a_3468_);
lean_dec_ref(v_a_3467_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___lam__0(lean_object* v___x_3474_, lean_object* v_mvarId_3475_, lean_object* v_hName_x3f_3476_, lean_object* v_fvarId_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_){
_start:
{
lean_object* v___x_3486_; 
lean_inc(v___y_3481_);
lean_inc_ref(v___y_3480_);
lean_inc(v___y_3479_);
lean_inc_ref(v___y_3478_);
v___x_3486_ = lean_infer_type(v___x_3474_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; lean_object* v___x_3488_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_a_3487_);
lean_dec_ref(v___x_3486_);
v___x_3488_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(v_mvarId_3475_, v_a_3487_, v_hName_x3f_3476_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3583_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3491_ = v___x_3488_;
v_isShared_3492_ = v_isSharedCheck_3583_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_dec(v___x_3488_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3583_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
if (lean_obj_tag(v_a_3489_) == 1)
{
lean_object* v_val_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3578_; 
lean_del_object(v___x_3491_);
v_val_3493_ = lean_ctor_get(v_a_3489_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v_a_3489_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3495_ = v_a_3489_;
v_isShared_3496_ = v_isSharedCheck_3578_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_val_3493_);
lean_dec(v_a_3489_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3578_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v_fst_3497_; lean_object* v_snd_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3577_; 
v_fst_3497_ = lean_ctor_get(v_val_3493_, 0);
v_snd_3498_ = lean_ctor_get(v_val_3493_, 1);
v_isSharedCheck_3577_ = !lean_is_exclusive(v_val_3493_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3500_ = v_val_3493_;
v_isShared_3501_ = v_isSharedCheck_3577_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_snd_3498_);
lean_inc(v_fst_3497_);
lean_dec(v_val_3493_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3577_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v_mvarId_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3575_; 
v_mvarId_3502_ = lean_ctor_get(v_fst_3497_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v_fst_3497_);
if (v_isSharedCheck_3575_ == 0)
{
lean_object* v_unused_3576_; 
v_unused_3576_ = lean_ctor_get(v_fst_3497_, 1);
lean_dec(v_unused_3576_);
v___x_3504_ = v_fst_3497_;
v_isShared_3505_ = v_isSharedCheck_3575_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_mvarId_3502_);
lean_dec(v_fst_3497_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3575_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
uint8_t v___x_3506_; lean_object* v___x_3507_; 
v___x_3506_ = 0;
lean_inc(v_fvarId_3477_);
lean_inc(v_mvarId_3502_);
v___x_3507_ = l_Lean_Meta_simpIfLocalDecl(v_mvarId_3502_, v_fvarId_3477_, v___x_3506_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v_a_3508_; lean_object* v_mvarId_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3565_; 
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
lean_inc(v_a_3508_);
lean_dec_ref(v___x_3507_);
v_mvarId_3509_ = lean_ctor_get(v_snd_3498_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v_snd_3498_);
if (v_isSharedCheck_3565_ == 0)
{
lean_object* v_unused_3566_; 
v_unused_3566_ = lean_ctor_get(v_snd_3498_, 1);
lean_dec(v_unused_3566_);
v___x_3511_ = v_snd_3498_;
v_isShared_3512_ = v_isSharedCheck_3565_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_mvarId_3509_);
lean_dec(v_snd_3498_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3565_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3513_; 
lean_inc(v_mvarId_3509_);
v___x_3513_ = l_Lean_Meta_simpIfLocalDecl(v_mvarId_3509_, v_fvarId_3477_, v___x_3506_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3556_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3516_ = v___x_3513_;
v_isShared_3517_ = v_isSharedCheck_3556_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3513_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3556_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
uint8_t v___x_3528_; 
v___x_3528_ = l_Lean_instBEqMVarId_beq(v_mvarId_3502_, v_a_3508_);
lean_dec(v_mvarId_3502_);
if (v___x_3528_ == 0)
{
lean_del_object(v___x_3511_);
lean_dec(v_mvarId_3509_);
lean_del_object(v___x_3504_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
goto v___jp_3518_;
}
else
{
uint8_t v___x_3529_; 
v___x_3529_ = l_Lean_instBEqMVarId_beq(v_mvarId_3509_, v_a_3514_);
lean_dec(v_mvarId_3509_);
if (v___x_3529_ == 0)
{
lean_del_object(v___x_3511_);
lean_del_object(v___x_3504_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
goto v___jp_3518_;
}
else
{
lean_object* v_options_3530_; uint8_t v_hasTrace_3531_; 
lean_del_object(v___x_3516_);
lean_del_object(v___x_3500_);
lean_del_object(v___x_3495_);
v_options_3530_ = lean_ctor_get(v___y_3480_, 2);
v_hasTrace_3531_ = lean_ctor_get_uint8(v_options_3530_, sizeof(void*)*1);
if (v_hasTrace_3531_ == 0)
{
lean_dec(v_a_3514_);
lean_del_object(v___x_3511_);
lean_dec(v_a_3508_);
lean_del_object(v___x_3504_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
goto v___jp_3483_;
}
else
{
lean_object* v_inheritedTraceOptions_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; uint8_t v___x_3535_; 
v_inheritedTraceOptions_3532_ = lean_ctor_get(v___y_3480_, 13);
v___x_3533_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1));
v___x_3534_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2);
v___x_3535_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3532_, v_options_3530_, v___x_3534_);
if (v___x_3535_ == 0)
{
lean_dec(v_a_3514_);
lean_del_object(v___x_3511_);
lean_dec(v_a_3508_);
lean_del_object(v___x_3504_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
goto v___jp_3483_;
}
else
{
lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3539_; 
v___x_3536_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4);
v___x_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3537_, 0, v_a_3508_);
if (v_isShared_3512_ == 0)
{
lean_ctor_set_tag(v___x_3511_, 7);
lean_ctor_set(v___x_3511_, 1, v___x_3537_);
lean_ctor_set(v___x_3511_, 0, v___x_3536_);
v___x_3539_ = v___x_3511_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v___x_3536_);
lean_ctor_set(v_reuseFailAlloc_3555_, 1, v___x_3537_);
v___x_3539_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
lean_object* v___x_3540_; lean_object* v___x_3542_; 
v___x_3540_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6);
if (v_isShared_3505_ == 0)
{
lean_ctor_set_tag(v___x_3504_, 7);
lean_ctor_set(v___x_3504_, 1, v___x_3540_);
lean_ctor_set(v___x_3504_, 0, v___x_3539_);
v___x_3542_ = v___x_3504_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3539_);
lean_ctor_set(v_reuseFailAlloc_3554_, 1, v___x_3540_);
v___x_3542_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3543_, 0, v_a_3514_);
v___x_3544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3542_);
lean_ctor_set(v___x_3544_, 1, v___x_3543_);
v___x_3545_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_3533_, v___x_3544_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_dec_ref(v___x_3545_);
goto v___jp_3483_;
}
else
{
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
v_a_3546_ = lean_ctor_get(v___x_3545_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3545_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3548_ = v___x_3545_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3545_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3551_; 
if (v_isShared_3549_ == 0)
{
v___x_3551_ = v___x_3548_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3546_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
}
}
}
}
}
v___jp_3518_:
{
lean_object* v___x_3520_; 
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 1, v_a_3514_);
lean_ctor_set(v___x_3500_, 0, v_a_3508_);
v___x_3520_ = v___x_3500_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_a_3508_);
lean_ctor_set(v_reuseFailAlloc_3527_, 1, v_a_3514_);
v___x_3520_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
lean_object* v___x_3522_; 
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 0, v___x_3520_);
v___x_3522_ = v___x_3495_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v___x_3520_);
v___x_3522_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
lean_object* v___x_3524_; 
if (v_isShared_3517_ == 0)
{
lean_ctor_set(v___x_3516_, 0, v___x_3522_);
v___x_3524_ = v___x_3516_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v___x_3522_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
}
}
}
else
{
lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3564_; 
lean_del_object(v___x_3511_);
lean_dec(v_mvarId_3509_);
lean_dec(v_a_3508_);
lean_del_object(v___x_3504_);
lean_dec(v_mvarId_3502_);
lean_del_object(v___x_3500_);
lean_del_object(v___x_3495_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
v_a_3557_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3559_ = v___x_3513_;
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_3513_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3562_; 
if (v_isShared_3560_ == 0)
{
v___x_3562_ = v___x_3559_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_a_3557_);
v___x_3562_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
return v___x_3562_;
}
}
}
}
}
else
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
lean_del_object(v___x_3504_);
lean_dec(v_mvarId_3502_);
lean_del_object(v___x_3500_);
lean_dec(v_snd_3498_);
lean_del_object(v___x_3495_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
lean_dec(v_fvarId_3477_);
v_a_3567_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___x_3507_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3507_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_a_3567_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3579_; lean_object* v___x_3581_; 
lean_dec(v_a_3489_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
lean_dec(v_fvarId_3477_);
v___x_3579_ = lean_box(0);
if (v_isShared_3492_ == 0)
{
lean_ctor_set(v___x_3491_, 0, v___x_3579_);
v___x_3581_ = v___x_3491_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v___x_3579_);
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
else
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3591_; 
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
lean_dec(v_fvarId_3477_);
v_a_3584_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3586_ = v___x_3488_;
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v___x_3488_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3589_; 
if (v_isShared_3587_ == 0)
{
v___x_3589_ = v___x_3586_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_a_3584_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
}
else
{
lean_object* v_a_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3599_; 
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
lean_dec(v_fvarId_3477_);
lean_dec(v_hName_x3f_3476_);
lean_dec(v_mvarId_3475_);
v_a_3592_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3594_ = v___x_3486_;
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_a_3592_);
lean_dec(v___x_3486_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3597_; 
if (v_isShared_3595_ == 0)
{
v___x_3597_ = v___x_3594_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_a_3592_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
v___jp_3483_:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3484_ = lean_box(0);
v___x_3485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3484_);
return v___x_3485_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___lam__0___boxed(lean_object* v___x_3600_, lean_object* v_mvarId_3601_, lean_object* v_hName_x3f_3602_, lean_object* v_fvarId_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_){
_start:
{
lean_object* v_res_3609_; 
v_res_3609_ = l_Lean_Meta_splitIfLocalDecl_x3f___lam__0(v___x_3600_, v_mvarId_3601_, v_hName_x3f_3602_, v_fvarId_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_);
return v_res_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f(lean_object* v_mvarId_3610_, lean_object* v_fvarId_3611_, lean_object* v_hName_x3f_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_){
_start:
{
lean_object* v___x_3618_; lean_object* v___f_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; 
lean_inc(v_fvarId_3611_);
v___x_3618_ = l_Lean_mkFVar(v_fvarId_3611_);
lean_inc(v_mvarId_3610_);
v___f_3619_ = lean_alloc_closure((void*)(l_Lean_Meta_splitIfLocalDecl_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3619_, 0, v___x_3618_);
lean_closure_set(v___f_3619_, 1, v_mvarId_3610_);
lean_closure_set(v___f_3619_, 2, v_hName_x3f_3612_);
lean_closure_set(v___f_3619_, 3, v_fvarId_3611_);
v___x_3620_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3620_, 0, lean_box(0));
lean_closure_set(v___x_3620_, 1, v_mvarId_3610_);
lean_closure_set(v___x_3620_, 2, v___f_3619_);
v___x_3621_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v___x_3620_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___boxed(lean_object* v_mvarId_3622_, lean_object* v_fvarId_3623_, lean_object* v_hName_x3f_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_){
_start:
{
lean_object* v_res_3630_; 
v_res_3630_ = l_Lean_Meta_splitIfLocalDecl_x3f(v_mvarId_3622_, v_fvarId_3623_, v_hName_x3f_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_);
lean_dec(v_a_3628_);
lean_dec_ref(v_a_3627_);
lean_dec(v_a_3626_);
lean_dec_ref(v_a_3625_);
return v_res_3630_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3651_ = lean_unsigned_to_nat(3526097586u);
v___x_3652_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_));
v___x_3653_ = l_Lean_Name_num___override(v___x_3652_, v___x_3651_);
return v___x_3653_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3655_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_));
v___x_3656_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3657_ = l_Lean_Name_str___override(v___x_3656_, v___x_3655_);
return v___x_3657_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3659_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_));
v___x_3660_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3661_ = l_Lean_Name_str___override(v___x_3660_, v___x_3659_);
return v___x_3661_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3662_ = lean_unsigned_to_nat(2u);
v___x_3663_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3664_ = l_Lean_Name_num___override(v___x_3663_, v___x_3662_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3666_; uint8_t v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3666_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10));
v___x_3667_ = 0;
v___x_3668_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3669_ = l_Lean_registerTraceClass(v___x_3666_, v___x_3667_, v___x_3668_);
return v___x_3669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2____boxed(lean_object* v_a_3670_){
_start:
{
lean_object* v_res_3671_; 
v_res_3671_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_();
return v_res_3671_;
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
