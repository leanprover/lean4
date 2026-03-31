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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "backward"};
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 7, 10, 91, 49, 15, 80, 52)}};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 103, .m_capacity = 103, .m_length = 102, .m_data = "use the old semantics for the `split` tactic where nested `if-then-else` terms could be simplified too"};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(32, 38, 242, 87, 165, 12, 140, 145)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(102, 141, 87, 76, 47, 100, 236, 116)}};
static const lean_object* l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4____boxed(lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__5_value),((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__6_value),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__7_value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "SplitIf"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__8_value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(76, 221, 255, 40, 254, 93, 36, 145)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(77, 67, 39, 96, 166, 188, 81, 166)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__11_value),((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(56, 202, 4, 90, 23, 96, 207, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__12_value),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(148, 235, 194, 225, 124, 161, 64, 247)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(221, 224, 164, 228, 171, 225, 60, 201)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(181, 248, 17, 89, 207, 85, 0, 88)}};
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(lean_object* v_name_1133_, lean_object* v_decl_1134_, lean_object* v_ref_1135_){
_start:
{
lean_object* v_defValue_1137_; lean_object* v_descr_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1165_; 
v_defValue_1137_ = lean_ctor_get(v_decl_1134_, 0);
v_descr_1138_ = lean_ctor_get(v_decl_1134_, 1);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_decl_1134_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1140_ = v_decl_1134_;
v_isShared_1141_ = v_isSharedCheck_1165_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_descr_1138_);
lean_inc(v_defValue_1137_);
lean_dec(v_decl_1134_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1165_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1142_; uint8_t v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1142_ = lean_alloc_ctor(1, 0, 1);
v___x_1143_ = lean_unbox(v_defValue_1137_);
lean_ctor_set_uint8(v___x_1142_, 0, v___x_1143_);
lean_inc_n(v_name_1133_, 2);
v___x_1144_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1144_, 0, v_name_1133_);
lean_ctor_set(v___x_1144_, 1, v_ref_1135_);
lean_ctor_set(v___x_1144_, 2, v___x_1142_);
lean_ctor_set(v___x_1144_, 3, v_descr_1138_);
v___x_1145_ = lean_register_option(v_name_1133_, v___x_1144_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1155_; 
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1155_ == 0)
{
lean_object* v_unused_1156_; 
v_unused_1156_ = lean_ctor_get(v___x_1145_, 0);
lean_dec(v_unused_1156_);
v___x_1147_ = v___x_1145_;
v_isShared_1148_ = v_isSharedCheck_1155_;
goto v_resetjp_1146_;
}
else
{
lean_dec(v___x_1145_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1155_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 1, v_defValue_1137_);
lean_ctor_set(v___x_1140_, 0, v_name_1133_);
v___x_1150_ = v___x_1140_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_name_1133_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v_defValue_1137_);
v___x_1150_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
lean_object* v___x_1152_; 
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1150_);
v___x_1152_ = v___x_1147_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
lean_del_object(v___x_1140_);
lean_dec(v_defValue_1137_);
lean_dec(v_name_1133_);
v_a_1157_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1145_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1145_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1166_, lean_object* v_decl_1167_, lean_object* v_ref_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(v_name_1166_, v_decl_1167_, v_ref_1168_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1188_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_));
v___x_1189_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_));
v___x_1190_ = ((lean_object*)(l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_));
v___x_1191_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(v___x_1188_, v___x_1189_, v___x_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4____boxed(lean_object* v_a_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_();
return v_res_1193_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1194_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0);
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0(lean_object* v_00_u03b2_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1);
return v___x_1198_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1199_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0);
v___x_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1(lean_object* v_00_u03b2_1202_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1);
return v___x_1203_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__0(void){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_1204_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__1(void){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0(lean_box(0));
return v___x_1205_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__2(void){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1(lean_box(0));
return v___x_1206_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__3(void){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1207_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__4(void){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__3, &l_Lean_Meta_SplitIf_getSimpContext___closed__3_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__3);
v___x_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
return v___x_1209_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__5(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v_s_1214_; 
v___x_1210_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__4, &l_Lean_Meta_SplitIf_getSimpContext___closed__4_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__4);
v___x_1211_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__2, &l_Lean_Meta_SplitIf_getSimpContext___closed__2_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__2);
v___x_1212_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__1, &l_Lean_Meta_SplitIf_getSimpContext___closed__1_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__1);
v___x_1213_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__0, &l_Lean_Meta_SplitIf_getSimpContext___closed__0_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__0);
v_s_1214_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_s_1214_, 0, v___x_1213_);
lean_ctor_set(v_s_1214_, 1, v___x_1213_);
lean_ctor_set(v_s_1214_, 2, v___x_1212_);
lean_ctor_set(v_s_1214_, 3, v___x_1211_);
lean_ctor_set(v_s_1214_, 4, v___x_1212_);
lean_ctor_set(v_s_1214_, 5, v___x_1210_);
return v_s_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_getSimpContext(lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v_s_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; uint8_t v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v_s_1232_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__5, &l_Lean_Meta_SplitIf_getSimpContext___closed__5_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__5);
v___x_1233_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__7));
v___x_1234_ = 1;
v___x_1235_ = 0;
v___x_1236_ = lean_unsigned_to_nat(1000u);
v___x_1237_ = l_Lean_Meta_SimpTheorems_addConst(v_s_1232_, v___x_1233_, v___x_1234_, v___x_1235_, v___x_1236_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_a_1238_);
lean_dec_ref(v___x_1237_);
v___x_1239_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__9));
v___x_1240_ = l_Lean_Meta_SimpTheorems_addConst(v_a_1238_, v___x_1239_, v___x_1234_, v___x_1235_, v___x_1236_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1241_);
lean_dec_ref(v___x_1240_);
v___x_1242_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__11));
v___x_1243_ = l_Lean_Meta_SimpTheorems_addConst(v_a_1241_, v___x_1242_, v___x_1234_, v___x_1235_, v___x_1236_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_a_1244_);
lean_dec_ref(v___x_1243_);
v___x_1245_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__13));
v___x_1246_ = l_Lean_Meta_SimpTheorems_addConst(v_a_1244_, v___x_1245_, v___x_1234_, v___x_1235_, v___x_1236_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1248_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref(v___x_1246_);
v___x_1248_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_1230_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1250_; lean_object* v_maxSteps_1251_; lean_object* v_maxDischargeDepth_1252_; uint8_t v_contextual_1253_; uint8_t v_memoize_1254_; uint8_t v_singlePass_1255_; uint8_t v_zeta_1256_; uint8_t v_beta_1257_; uint8_t v_eta_1258_; uint8_t v_etaStruct_1259_; uint8_t v_iota_1260_; uint8_t v_proj_1261_; uint8_t v_decide_1262_; uint8_t v_arith_1263_; uint8_t v_autoUnfold_1264_; uint8_t v_failIfUnchanged_1265_; uint8_t v_ground_1266_; uint8_t v_unfoldPartialApp_1267_; uint8_t v_zetaDelta_1268_; uint8_t v_index_1269_; uint8_t v_implicitDefEqProofs_1270_; uint8_t v_zetaUnused_1271_; uint8_t v_catchRuntime_1272_; uint8_t v_zetaHave_1273_; uint8_t v_congrConsts_1274_; uint8_t v_bitVecOfNat_1275_; uint8_t v_warnExponents_1276_; uint8_t v_suggestions_1277_; lean_object* v_maxSuggestions_1278_; uint8_t v_locals_1279_; uint8_t v_instances_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_a_1249_);
lean_dec_ref(v___x_1248_);
v___x_1250_ = l_Lean_Meta_Simp_neutralConfig;
v_maxSteps_1251_ = lean_ctor_get(v___x_1250_, 0);
v_maxDischargeDepth_1252_ = lean_ctor_get(v___x_1250_, 1);
v_contextual_1253_ = lean_ctor_get_uint8(v___x_1250_, sizeof(void*)*3);
v_memoize_1254_ = lean_ctor_get_uint8(v___x_1250_, sizeof(void*)*3 + 1);
v_singlePass_1255_ = lean_ctor_get_uint8(v___x_1250_, sizeof(void*)*3 + 2);
v_zeta_1256_ = lean_ctor_get_uint8(v___x_1250_, sizeof(void*)*3 + 3);
v_beta_1257_ = lean_ctor_get_uint8(v___x_1250_, sizeof(void*)*3 + 4);
v_eta_1258_ = lean_ctor_get_uint8(v___x_1250_, sizeof(void*)*3 + 5);
v_etaStruct_1259_ = lean_ctor_get_uint8(v___x_1250_, sizeof(void*)*3 + 6);
v_iota_1260_ = lean_ctor_get_uint8(v___x_1250_, sizeof(void*)*3 + 7);
v_proj_1261_ = lean_ctor_get_uint8(v___x_1250_, sizeof(void*)*3 + 8);
v_decide_1262_ = lean_ctor_get_uint8(v___x_1250_, sizeof(void*)*3 + 9);
v_arith_1263_ = lean_ctor_get_uint8(v___x_1250_, sizeof(void*)*3 + 10);
v_autoUnfold_1264_ = lean_ctor_get_uint8(v___x_1250_, sizeof(void*)*3 + 11);
v_failIfUnchanged_1265_ = lean_ctor_get_uint8(v___x_1250_, sizeof(void*)*3 + 13);
v_ground_1266_ = lean_ctor_get_uint8(v___x_1250_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_1267_ = lean_ctor_get_uint8(v___x_1250_, sizeof(void*)*3 + 15);
v_zetaDelta_1268_ = lean_ctor_get_uint8(v___x_1250_, sizeof(void*)*3 + 16);
v_index_1269_ = lean_ctor_get_uint8(v___x_1250_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_1270_ = lean_ctor_get_uint8(v___x_1250_, sizeof(void*)*3 + 18);
v_zetaUnused_1271_ = lean_ctor_get_uint8(v___x_1250_, sizeof(void*)*3 + 19);
v_catchRuntime_1272_ = lean_ctor_get_uint8(v___x_1250_, sizeof(void*)*3 + 20);
v_zetaHave_1273_ = lean_ctor_get_uint8(v___x_1250_, sizeof(void*)*3 + 21);
v_congrConsts_1274_ = lean_ctor_get_uint8(v___x_1250_, sizeof(void*)*3 + 23);
v_bitVecOfNat_1275_ = lean_ctor_get_uint8(v___x_1250_, sizeof(void*)*3 + 24);
v_warnExponents_1276_ = lean_ctor_get_uint8(v___x_1250_, sizeof(void*)*3 + 25);
v_suggestions_1277_ = lean_ctor_get_uint8(v___x_1250_, sizeof(void*)*3 + 26);
v_maxSuggestions_1278_ = lean_ctor_get(v___x_1250_, 2);
v_locals_1279_ = lean_ctor_get_uint8(v___x_1250_, sizeof(void*)*3 + 27);
v_instances_1280_ = lean_ctor_get_uint8(v___x_1250_, sizeof(void*)*3 + 28);
lean_inc(v_maxSuggestions_1278_);
lean_inc(v_maxDischargeDepth_1252_);
lean_inc(v_maxSteps_1251_);
v___x_1281_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1281_, 0, v_maxSteps_1251_);
lean_ctor_set(v___x_1281_, 1, v_maxDischargeDepth_1252_);
lean_ctor_set(v___x_1281_, 2, v_maxSuggestions_1278_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3, v_contextual_1253_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 1, v_memoize_1254_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 2, v_singlePass_1255_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 3, v_zeta_1256_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 4, v_beta_1257_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 5, v_eta_1258_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 6, v_etaStruct_1259_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 7, v_iota_1260_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 8, v_proj_1261_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 9, v_decide_1262_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 10, v_arith_1263_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 11, v_autoUnfold_1264_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 12, v___x_1235_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 13, v_failIfUnchanged_1265_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 14, v_ground_1266_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 15, v_unfoldPartialApp_1267_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 16, v_zetaDelta_1268_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 17, v_index_1269_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_1270_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 19, v_zetaUnused_1271_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 20, v_catchRuntime_1272_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 21, v_zetaHave_1273_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 22, v___x_1234_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 23, v_congrConsts_1274_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 24, v_bitVecOfNat_1275_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 25, v_warnExponents_1276_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 26, v_suggestions_1277_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 27, v_locals_1279_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 28, v_instances_1280_);
v___x_1282_ = lean_unsigned_to_nat(1u);
v___x_1283_ = lean_mk_empty_array_with_capacity(v___x_1282_);
v___x_1284_ = lean_array_push(v___x_1283_, v_a_1247_);
v___x_1285_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1281_, v___x_1284_, v_a_1249_, v_a_1227_, v_a_1229_, v_a_1230_);
return v___x_1285_;
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec(v_a_1247_);
v_a_1286_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1248_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1248_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
v_a_1294_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1246_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1246_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
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
else
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
v_a_1302_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1243_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1243_);
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
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
v_a_1310_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1240_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1240_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
v_a_1318_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1237_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1237_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_getSimpContext___boxed(lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_);
lean_dec(v_a_1329_);
lean_dec_ref(v_a_1328_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_1336_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_a_1339_; lean_object* v___x_1340_; lean_object* v_maxSteps_1341_; lean_object* v_maxDischargeDepth_1342_; uint8_t v_contextual_1343_; uint8_t v_memoize_1344_; uint8_t v_singlePass_1345_; uint8_t v_zeta_1346_; uint8_t v_beta_1347_; uint8_t v_eta_1348_; uint8_t v_etaStruct_1349_; uint8_t v_iota_1350_; uint8_t v_proj_1351_; uint8_t v_decide_1352_; uint8_t v_arith_1353_; uint8_t v_autoUnfold_1354_; uint8_t v_failIfUnchanged_1355_; uint8_t v_ground_1356_; uint8_t v_unfoldPartialApp_1357_; uint8_t v_zetaDelta_1358_; uint8_t v_index_1359_; uint8_t v_implicitDefEqProofs_1360_; uint8_t v_zetaUnused_1361_; uint8_t v_catchRuntime_1362_; uint8_t v_zetaHave_1363_; uint8_t v_congrConsts_1364_; uint8_t v_bitVecOfNat_1365_; uint8_t v_warnExponents_1366_; uint8_t v_suggestions_1367_; lean_object* v_maxSuggestions_1368_; uint8_t v_locals_1369_; uint8_t v_instances_1370_; uint8_t v___x_1371_; uint8_t v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
lean_inc(v_a_1339_);
lean_dec_ref(v___x_1338_);
v___x_1340_ = l_Lean_Meta_Simp_neutralConfig;
v_maxSteps_1341_ = lean_ctor_get(v___x_1340_, 0);
v_maxDischargeDepth_1342_ = lean_ctor_get(v___x_1340_, 1);
v_contextual_1343_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*3);
v_memoize_1344_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*3 + 1);
v_singlePass_1345_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*3 + 2);
v_zeta_1346_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*3 + 3);
v_beta_1347_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*3 + 4);
v_eta_1348_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*3 + 5);
v_etaStruct_1349_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*3 + 6);
v_iota_1350_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*3 + 7);
v_proj_1351_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*3 + 8);
v_decide_1352_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*3 + 9);
v_arith_1353_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*3 + 10);
v_autoUnfold_1354_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*3 + 11);
v_failIfUnchanged_1355_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*3 + 13);
v_ground_1356_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_1357_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*3 + 15);
v_zetaDelta_1358_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*3 + 16);
v_index_1359_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_1360_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*3 + 18);
v_zetaUnused_1361_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*3 + 19);
v_catchRuntime_1362_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*3 + 20);
v_zetaHave_1363_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*3 + 21);
v_congrConsts_1364_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*3 + 23);
v_bitVecOfNat_1365_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*3 + 24);
v_warnExponents_1366_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*3 + 25);
v_suggestions_1367_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*3 + 26);
v_maxSuggestions_1368_ = lean_ctor_get(v___x_1340_, 2);
v_locals_1369_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*3 + 27);
v_instances_1370_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*3 + 28);
v___x_1371_ = 0;
v___x_1372_ = 1;
lean_inc(v_maxSuggestions_1368_);
lean_inc(v_maxDischargeDepth_1342_);
lean_inc(v_maxSteps_1341_);
v___x_1373_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1373_, 0, v_maxSteps_1341_);
lean_ctor_set(v___x_1373_, 1, v_maxDischargeDepth_1342_);
lean_ctor_set(v___x_1373_, 2, v_maxSuggestions_1368_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3, v_contextual_1343_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 1, v_memoize_1344_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 2, v_singlePass_1345_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 3, v_zeta_1346_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 4, v_beta_1347_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 5, v_eta_1348_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 6, v_etaStruct_1349_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 7, v_iota_1350_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 8, v_proj_1351_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 9, v_decide_1352_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 10, v_arith_1353_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 11, v_autoUnfold_1354_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 12, v___x_1371_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 13, v_failIfUnchanged_1355_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 14, v_ground_1356_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 15, v_unfoldPartialApp_1357_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 16, v_zetaDelta_1358_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 17, v_index_1359_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_1360_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 19, v_zetaUnused_1361_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 20, v_catchRuntime_1362_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 21, v_zetaHave_1363_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 22, v___x_1372_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 23, v_congrConsts_1364_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 24, v_bitVecOfNat_1365_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 25, v_warnExponents_1366_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 26, v_suggestions_1367_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 27, v_locals_1369_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 28, v_instances_1370_);
v___x_1374_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg___closed__0));
v___x_1375_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1373_, v___x_1374_, v_a_1339_, v_a_1334_, v_a_1335_, v_a_1336_);
return v___x_1375_;
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
v_a_1376_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1338_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1338_);
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
uint8_t v___x_1404_; 
v___x_1404_ = l_Lean_Expr_hasMVar(v_e_1401_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1405_; 
v___x_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1405_, 0, v_e_1401_);
return v___x_1405_;
}
else
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
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg___boxed(lean_object* v_e_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_e_1426_, v___y_1427_);
lean_dec(v___y_1427_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0(lean_object* v_e_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_e_1430_, v___y_1435_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___boxed(lean_object* v_e_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0(v_e_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(lean_object* v_cls_1450_, lean_object* v_msg_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_ref_1457_; lean_object* v___x_1458_; lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1503_; 
v_ref_1457_ = lean_ctor_get(v___y_1454_, 5);
v___x_1458_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(v_msg_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1461_ = v___x_1458_;
v_isShared_1462_ = v_isSharedCheck_1503_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1458_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1503_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1463_; lean_object* v_traceState_1464_; lean_object* v_env_1465_; lean_object* v_nextMacroScope_1466_; lean_object* v_ngen_1467_; lean_object* v_auxDeclNGen_1468_; lean_object* v_cache_1469_; lean_object* v_messages_1470_; lean_object* v_infoState_1471_; lean_object* v_snapshotTasks_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1502_; 
v___x_1463_ = lean_st_ref_take(v___y_1455_);
v_traceState_1464_ = lean_ctor_get(v___x_1463_, 4);
v_env_1465_ = lean_ctor_get(v___x_1463_, 0);
v_nextMacroScope_1466_ = lean_ctor_get(v___x_1463_, 1);
v_ngen_1467_ = lean_ctor_get(v___x_1463_, 2);
v_auxDeclNGen_1468_ = lean_ctor_get(v___x_1463_, 3);
v_cache_1469_ = lean_ctor_get(v___x_1463_, 5);
v_messages_1470_ = lean_ctor_get(v___x_1463_, 6);
v_infoState_1471_ = lean_ctor_get(v___x_1463_, 7);
v_snapshotTasks_1472_ = lean_ctor_get(v___x_1463_, 8);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1474_ = v___x_1463_;
v_isShared_1475_ = v_isSharedCheck_1502_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_snapshotTasks_1472_);
lean_inc(v_infoState_1471_);
lean_inc(v_messages_1470_);
lean_inc(v_cache_1469_);
lean_inc(v_traceState_1464_);
lean_inc(v_auxDeclNGen_1468_);
lean_inc(v_ngen_1467_);
lean_inc(v_nextMacroScope_1466_);
lean_inc(v_env_1465_);
lean_dec(v___x_1463_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1502_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
uint64_t v_tid_1476_; lean_object* v_traces_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1501_; 
v_tid_1476_ = lean_ctor_get_uint64(v_traceState_1464_, sizeof(void*)*1);
v_traces_1477_ = lean_ctor_get(v_traceState_1464_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_traceState_1464_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1479_ = v_traceState_1464_;
v_isShared_1480_ = v_isSharedCheck_1501_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_traces_1477_);
lean_dec(v_traceState_1464_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1501_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1481_; double v___x_1482_; uint8_t v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1491_; 
v___x_1481_ = lean_box(0);
v___x_1482_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0);
v___x_1483_ = 0;
v___x_1484_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__1));
v___x_1485_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1485_, 0, v_cls_1450_);
lean_ctor_set(v___x_1485_, 1, v___x_1481_);
lean_ctor_set(v___x_1485_, 2, v___x_1484_);
lean_ctor_set_float(v___x_1485_, sizeof(void*)*3, v___x_1482_);
lean_ctor_set_float(v___x_1485_, sizeof(void*)*3 + 8, v___x_1482_);
lean_ctor_set_uint8(v___x_1485_, sizeof(void*)*3 + 16, v___x_1483_);
v___x_1486_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__2));
v___x_1487_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1485_);
lean_ctor_set(v___x_1487_, 1, v_a_1459_);
lean_ctor_set(v___x_1487_, 2, v___x_1486_);
lean_inc(v_ref_1457_);
v___x_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1488_, 0, v_ref_1457_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = l_Lean_PersistentArray_push___redArg(v_traces_1477_, v___x_1488_);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 0, v___x_1489_);
v___x_1491_ = v___x_1479_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1489_);
lean_ctor_set_uint64(v_reuseFailAlloc_1500_, sizeof(void*)*1, v_tid_1476_);
v___x_1491_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1493_; 
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 4, v___x_1491_);
v___x_1493_ = v___x_1474_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_env_1465_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_nextMacroScope_1466_);
lean_ctor_set(v_reuseFailAlloc_1499_, 2, v_ngen_1467_);
lean_ctor_set(v_reuseFailAlloc_1499_, 3, v_auxDeclNGen_1468_);
lean_ctor_set(v_reuseFailAlloc_1499_, 4, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1499_, 5, v_cache_1469_);
lean_ctor_set(v_reuseFailAlloc_1499_, 6, v_messages_1470_);
lean_ctor_set(v_reuseFailAlloc_1499_, 7, v_infoState_1471_);
lean_ctor_set(v_reuseFailAlloc_1499_, 8, v_snapshotTasks_1472_);
v___x_1493_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1494_ = lean_st_ref_set(v___y_1455_, v___x_1493_);
v___x_1495_ = lean_box(0);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 0, v___x_1495_);
v___x_1497_ = v___x_1461_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg___boxed(lean_object* v_cls_1504_, lean_object* v_msg_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v_cls_1504_, v_msg_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
return v_res_1511_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1518_ = lean_box(0);
v___x_1519_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__3));
v___x_1520_ = l_Lean_mkConst(v___x_1519_, v___x_1518_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(lean_object* v_a_1521_, lean_object* v_numIndices_1522_, lean_object* v_as_1523_, lean_object* v_i_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v_zero_1530_; uint8_t v_isZero_1531_; 
v_zero_1530_ = lean_unsigned_to_nat(0u);
v_isZero_1531_ = lean_nat_dec_eq(v_i_1524_, v_zero_1530_);
if (v_isZero_1531_ == 1)
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
lean_dec(v_i_1524_);
lean_dec_ref(v_a_1521_);
v___x_1532_ = lean_box(0);
v___x_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
return v___x_1533_;
}
else
{
lean_object* v_one_1534_; lean_object* v_n_1535_; lean_object* v___x_1536_; 
v_one_1534_ = lean_unsigned_to_nat(1u);
v_n_1535_ = lean_nat_sub(v_i_1524_, v_one_1534_);
lean_dec(v_i_1524_);
v___x_1536_ = lean_array_fget(v_as_1523_, v_n_1535_);
if (lean_obj_tag(v___x_1536_) == 0)
{
v_i_1524_ = v_n_1535_;
goto _start;
}
else
{
lean_object* v_val_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1603_; 
v_val_1538_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1540_ = v___x_1536_;
v_isShared_1541_ = v_isSharedCheck_1603_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_val_1538_);
lean_dec(v___x_1536_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1603_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
uint8_t v___y_1543_; lean_object* v___x_1600_; uint8_t v___x_1601_; 
v___x_1600_ = l_Lean_LocalDecl_index(v_val_1538_);
v___x_1601_ = lean_nat_dec_le(v_numIndices_1522_, v___x_1600_);
lean_dec(v___x_1600_);
if (v___x_1601_ == 0)
{
uint8_t v___x_1602_; 
v___x_1602_ = l_Lean_LocalDecl_isAuxDecl(v_val_1538_);
v___y_1543_ = v___x_1602_;
goto v___jp_1542_;
}
else
{
v___y_1543_ = v___x_1601_;
goto v___jp_1542_;
}
v___jp_1542_:
{
if (v___y_1543_ == 0)
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = l_Lean_LocalDecl_type(v_val_1538_);
lean_inc_ref(v___x_1544_);
lean_inc_ref(v_a_1521_);
v___x_1545_ = l_Lean_Meta_isExprDefEq(v_a_1521_, v___x_1544_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1590_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1548_ = v___x_1545_;
v_isShared_1549_ = v_isSharedCheck_1590_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1545_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1590_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
uint8_t v___x_1550_; 
v___x_1550_ = lean_unbox(v_a_1546_);
lean_dec(v_a_1546_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; uint8_t v___x_1552_; 
lean_del_object(v___x_1548_);
v___x_1551_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__1));
v___x_1552_ = l_Lean_Expr_isAppOfArity(v_a_1521_, v___x_1551_, v_one_1534_);
if (v___x_1552_ == 0)
{
lean_dec_ref(v___x_1544_);
lean_del_object(v___x_1540_);
lean_dec(v_val_1538_);
v_i_1524_ = v_n_1535_;
goto _start;
}
else
{
lean_object* v___x_1554_; uint8_t v___x_1555_; 
v___x_1554_ = l_Lean_Expr_appArg_x21(v_a_1521_);
v___x_1555_ = l_Lean_Expr_isAppOfArity(v___x_1554_, v___x_1551_, v_one_1534_);
if (v___x_1555_ == 0)
{
lean_dec_ref(v___x_1554_);
lean_dec_ref(v___x_1544_);
lean_del_object(v___x_1540_);
lean_dec(v_val_1538_);
v_i_1524_ = v_n_1535_;
goto _start;
}
else
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = l_Lean_Expr_appArg_x21(v___x_1554_);
lean_dec_ref(v___x_1554_);
lean_inc_ref(v___x_1557_);
v___x_1558_ = l_Lean_Meta_isExprDefEq(v___x_1557_, v___x_1544_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1574_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1561_ = v___x_1558_;
v_isShared_1562_ = v_isSharedCheck_1574_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1558_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1574_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
uint8_t v___x_1563_; 
v___x_1563_ = lean_unbox(v_a_1559_);
lean_dec(v_a_1559_);
if (v___x_1563_ == 0)
{
lean_del_object(v___x_1561_);
lean_dec_ref(v___x_1557_);
lean_del_object(v___x_1540_);
lean_dec(v_val_1538_);
v_i_1524_ = v_n_1535_;
goto _start;
}
else
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1569_; 
lean_dec(v_n_1535_);
lean_dec_ref(v_a_1521_);
v___x_1565_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4);
v___x_1566_ = l_Lean_LocalDecl_toExpr(v_val_1538_);
v___x_1567_ = l_Lean_mkAppB(v___x_1565_, v___x_1557_, v___x_1566_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v___x_1567_);
v___x_1569_ = v___x_1540_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
lean_object* v___x_1571_; 
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v___x_1569_);
v___x_1571_ = v___x_1561_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1569_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
lean_dec_ref(v___x_1557_);
lean_del_object(v___x_1540_);
lean_dec(v_val_1538_);
lean_dec(v_n_1535_);
lean_dec_ref(v_a_1521_);
v_a_1575_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1558_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1558_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
}
}
else
{
lean_object* v___x_1583_; lean_object* v___x_1585_; 
lean_dec_ref(v___x_1544_);
lean_dec(v_n_1535_);
lean_dec_ref(v_a_1521_);
v___x_1583_ = l_Lean_LocalDecl_toExpr(v_val_1538_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v___x_1583_);
v___x_1585_ = v___x_1540_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
lean_object* v___x_1587_; 
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 0, v___x_1585_);
v___x_1587_ = v___x_1548_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1585_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
lean_dec_ref(v___x_1544_);
lean_del_object(v___x_1540_);
lean_dec(v_val_1538_);
lean_dec(v_n_1535_);
lean_dec_ref(v_a_1521_);
v_a_1591_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1545_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1545_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
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
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
else
{
lean_del_object(v___x_1540_);
lean_dec(v_val_1538_);
v_i_1524_ = v_n_1535_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_a_1604_, lean_object* v_numIndices_1605_, lean_object* v_as_1606_, lean_object* v_i_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_a_1604_, v_numIndices_1605_, v_as_1606_, v_i_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec_ref(v_as_1606_);
lean_dec(v_numIndices_1605_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(lean_object* v_a_1614_, lean_object* v_numIndices_1615_, lean_object* v_as_1616_, lean_object* v_i_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v_zero_1626_; uint8_t v_isZero_1627_; 
v_zero_1626_ = lean_unsigned_to_nat(0u);
v_isZero_1627_ = lean_nat_dec_eq(v_i_1617_, v_zero_1626_);
if (v_isZero_1627_ == 1)
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
lean_dec(v_i_1617_);
lean_dec_ref(v_a_1614_);
v___x_1628_ = lean_box(0);
v___x_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
return v___x_1629_;
}
else
{
lean_object* v_one_1630_; lean_object* v_n_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v_one_1630_ = lean_unsigned_to_nat(1u);
v_n_1631_ = lean_nat_sub(v_i_1617_, v_one_1630_);
lean_dec(v_i_1617_);
v___x_1632_ = lean_array_fget_borrowed(v_as_1616_, v_n_1631_);
lean_inc_ref(v_a_1614_);
v___x_1633_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_a_1614_, v_numIndices_1615_, v___x_1632_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
if (lean_obj_tag(v_a_1634_) == 0)
{
lean_dec_ref(v___x_1633_);
v_i_1617_ = v_n_1631_;
goto _start;
}
else
{
lean_dec_ref(v_a_1634_);
lean_dec(v_n_1631_);
lean_dec_ref(v_a_1614_);
return v___x_1633_;
}
}
else
{
lean_dec(v_n_1631_);
lean_dec_ref(v_a_1614_);
return v___x_1633_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(lean_object* v_a_1636_, lean_object* v_numIndices_1637_, lean_object* v_x_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
if (lean_obj_tag(v_x_1638_) == 0)
{
lean_object* v_cs_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v_cs_1647_ = lean_ctor_get(v_x_1638_, 0);
v___x_1648_ = lean_array_get_size(v_cs_1647_);
v___x_1649_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_a_1636_, v_numIndices_1637_, v_cs_1647_, v___x_1648_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
return v___x_1649_;
}
else
{
lean_object* v_vs_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v_vs_1650_ = lean_ctor_get(v_x_1638_, 0);
v___x_1651_ = lean_array_get_size(v_vs_1650_);
v___x_1652_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_a_1636_, v_numIndices_1637_, v_vs_1650_, v___x_1651_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
return v___x_1652_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3___boxed(lean_object* v_a_1653_, lean_object* v_numIndices_1654_, lean_object* v_x_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_a_1653_, v_numIndices_1654_, v_x_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v_x_1655_);
lean_dec(v_numIndices_1654_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_a_1665_, lean_object* v_numIndices_1666_, lean_object* v_as_1667_, lean_object* v_i_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_a_1665_, v_numIndices_1666_, v_as_1667_, v_i_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v_as_1667_);
lean_dec(v_numIndices_1666_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(lean_object* v_a_1678_, lean_object* v_numIndices_1679_, lean_object* v_t_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v_root_1689_; lean_object* v_tail_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v_root_1689_ = lean_ctor_get(v_t_1680_, 0);
v_tail_1690_ = lean_ctor_get(v_t_1680_, 1);
v___x_1691_ = lean_array_get_size(v_tail_1690_);
lean_inc_ref(v_a_1678_);
v___x_1692_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_a_1678_, v_numIndices_1679_, v_tail_1690_, v___x_1691_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1693_);
if (lean_obj_tag(v_a_1693_) == 0)
{
lean_object* v___x_1694_; 
lean_dec_ref(v___x_1692_);
v___x_1694_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_a_1678_, v_numIndices_1679_, v_root_1689_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
return v___x_1694_;
}
else
{
lean_dec_ref(v_a_1693_);
lean_dec_ref(v_a_1678_);
return v___x_1692_;
}
}
else
{
lean_dec_ref(v_a_1678_);
return v___x_1692_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1___boxed(lean_object* v_a_1695_, lean_object* v_numIndices_1696_, lean_object* v_t_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(v_a_1695_, v_numIndices_1696_, v_t_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec_ref(v_t_1697_);
lean_dec(v_numIndices_1696_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(lean_object* v_a_1707_, lean_object* v_numIndices_1708_, lean_object* v_lctx_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v_decls_1718_; lean_object* v___x_1719_; 
v_decls_1718_ = lean_ctor_get(v_lctx_1709_, 1);
v___x_1719_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(v_a_1707_, v_numIndices_1708_, v_decls_1718_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1___boxed(lean_object* v_a_1720_, lean_object* v_numIndices_1721_, lean_object* v_lctx_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(v_a_1720_, v_numIndices_1721_, v_lctx_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v_lctx_1722_);
lean_dec(v_numIndices_1721_);
return v_res_1731_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3(void){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1737_ = lean_box(0);
v___x_1738_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2));
v___x_1739_ = l_Lean_mkConst(v___x_1738_, v___x_1737_);
return v___x_1739_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6(void){
_start:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1743_ = lean_box(0);
v___x_1744_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__5));
v___x_1745_ = l_Lean_mkConst(v___x_1744_, v___x_1743_);
return v___x_1745_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7(void){
_start:
{
uint8_t v___x_1746_; uint64_t v___x_1747_; 
v___x_1746_ = 1;
v___x_1747_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1746_);
return v___x_1747_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1754_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10));
v___x_1755_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4));
v___x_1756_ = l_Lean_Name_append(v___x_1755_, v___x_1754_);
return v___x_1756_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13(void){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12));
v___x_1759_ = l_Lean_stringToMessageData(v___x_1758_);
return v___x_1759_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__15(void){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14));
v___x_1762_ = l_Lean_stringToMessageData(v___x_1761_);
return v___x_1762_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__18(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17));
v___x_1767_ = l_Lean_MessageData_ofFormat(v___x_1766_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(lean_object* v_numIndices_1768_, uint8_t v_useDecide_1769_, lean_object* v_prop_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_){
_start:
{
lean_object* v___x_1779_; lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1941_; 
v___x_1779_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_prop_1770_, v_a_1775_);
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1782_ = v___x_1779_;
v_isShared_1783_ = v_isSharedCheck_1941_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1779_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1941_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v_a_1804_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v_options_1909_; uint8_t v_hasTrace_1910_; 
v_options_1909_ = lean_ctor_get(v_a_1776_, 2);
v_hasTrace_1910_ = lean_ctor_get_uint8(v_options_1909_, sizeof(void*)*1);
if (v_hasTrace_1910_ == 0)
{
v___y_1832_ = v_a_1771_;
v___y_1833_ = v_a_1772_;
v___y_1834_ = v_a_1773_;
v___y_1835_ = v_a_1774_;
v___y_1836_ = v_a_1775_;
v___y_1837_ = v_a_1776_;
v___y_1838_ = v_a_1777_;
goto v___jp_1831_;
}
else
{
lean_object* v_inheritedTraceOptions_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; uint8_t v___x_1914_; 
v_inheritedTraceOptions_1911_ = lean_ctor_get(v_a_1776_, 13);
v___x_1912_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10));
v___x_1913_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11);
v___x_1914_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1911_, v_options_1909_, v___x_1913_);
if (v___x_1914_ == 0)
{
v___y_1832_ = v_a_1771_;
v___y_1833_ = v_a_1772_;
v___y_1834_ = v_a_1773_;
v___y_1835_ = v_a_1774_;
v___y_1836_ = v_a_1775_;
v___y_1837_ = v_a_1776_;
v___y_1838_ = v_a_1777_;
goto v___jp_1831_;
}
else
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___y_1921_; lean_object* v___x_1934_; lean_object* v___x_1935_; uint8_t v___x_1936_; 
v___x_1915_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13);
lean_inc(v_a_1780_);
v___x_1916_ = l_Lean_MessageData_ofExpr(v_a_1780_);
v___x_1917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1915_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__15, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__15_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__15);
v___x_1919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1917_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1934_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__1));
v___x_1935_ = lean_unsigned_to_nat(1u);
v___x_1936_ = l_Lean_Expr_isAppOfArity(v_a_1780_, v___x_1934_, v___x_1935_);
if (v___x_1936_ == 0)
{
goto v___jp_1932_;
}
else
{
lean_object* v___x_1937_; uint8_t v___x_1938_; 
v___x_1937_ = l_Lean_Expr_appArg_x21(v_a_1780_);
v___x_1938_ = l_Lean_Expr_isAppOfArity(v___x_1937_, v___x_1934_, v___x_1935_);
if (v___x_1938_ == 0)
{
lean_dec_ref(v___x_1937_);
goto v___jp_1932_;
}
else
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = l_Lean_Expr_appArg_x21(v___x_1937_);
lean_dec_ref(v___x_1937_);
v___x_1940_ = l_Lean_MessageData_ofExpr(v___x_1939_);
v___y_1921_ = v___x_1940_;
goto v___jp_1920_;
}
}
v___jp_1920_:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1919_);
lean_ctor_set(v___x_1922_, 1, v___y_1921_);
v___x_1923_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v___x_1912_, v___x_1922_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_dec_ref(v___x_1923_);
v___y_1832_ = v_a_1771_;
v___y_1833_ = v_a_1772_;
v___y_1834_ = v_a_1773_;
v___y_1835_ = v_a_1774_;
v___y_1836_ = v_a_1775_;
v___y_1837_ = v_a_1776_;
v___y_1838_ = v_a_1777_;
goto v___jp_1831_;
}
else
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1931_; 
lean_del_object(v___x_1782_);
lean_dec(v_a_1780_);
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1926_ = v___x_1923_;
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1923_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1929_; 
if (v_isShared_1927_ == 0)
{
v___x_1929_ = v___x_1926_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_a_1924_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
v___jp_1932_:
{
lean_object* v___x_1933_; 
v___x_1933_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__18, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__18_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__18);
v___y_1921_ = v___x_1933_;
goto v___jp_1920_;
}
}
}
v___jp_1784_:
{
lean_object* v_lctx_1792_; lean_object* v___x_1793_; 
v_lctx_1792_ = lean_ctor_get(v___y_1788_, 2);
v___x_1793_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(v_a_1780_, v_numIndices_1768_, v_lctx_1792_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
return v___x_1793_;
}
v___jp_1794_:
{
lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1805_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2));
v___x_1806_ = l_Lean_Expr_isConstOf(v_a_1804_, v___x_1805_);
lean_dec_ref(v_a_1804_);
if (v___x_1806_ == 0)
{
lean_dec_ref(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_del_object(v___x_1782_);
v___y_1785_ = v___y_1799_;
v___y_1786_ = v___y_1798_;
v___y_1787_ = v___y_1801_;
v___y_1788_ = v___y_1800_;
v___y_1789_ = v___y_1803_;
v___y_1790_ = v___y_1802_;
v___y_1791_ = v___y_1797_;
goto v___jp_1784_;
}
else
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
lean_dec(v_a_1780_);
v___x_1807_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3);
v___x_1808_ = l_Lean_Meta_mkEqRefl(v___x_1807_, v___y_1800_, v___y_1803_, v___y_1802_, v___y_1797_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1822_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1811_ = v___x_1808_;
v_isShared_1812_ = v_isSharedCheck_1822_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1808_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1822_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1817_; 
v___x_1813_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6);
v___x_1814_ = l_Lean_Expr_appArg_x21(v___y_1795_);
lean_dec_ref(v___y_1795_);
v___x_1815_ = l_Lean_mkApp3(v___x_1813_, v___y_1796_, v___x_1814_, v_a_1809_);
if (v_isShared_1783_ == 0)
{
lean_ctor_set_tag(v___x_1782_, 1);
lean_ctor_set(v___x_1782_, 0, v___x_1815_);
v___x_1817_ = v___x_1782_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1815_);
v___x_1817_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
lean_object* v___x_1819_; 
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v___x_1817_);
v___x_1819_ = v___x_1811_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
lean_dec_ref(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_del_object(v___x_1782_);
v_a_1823_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1808_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1808_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1823_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
}
v___jp_1831_:
{
if (v_useDecide_1769_ == 0)
{
lean_del_object(v___x_1782_);
v___y_1785_ = v___y_1832_;
v___y_1786_ = v___y_1833_;
v___y_1787_ = v___y_1834_;
v___y_1788_ = v___y_1835_;
v___y_1789_ = v___y_1836_;
v___y_1790_ = v___y_1837_;
v___y_1791_ = v___y_1838_;
goto v___jp_1784_;
}
else
{
lean_object* v___x_1839_; lean_object* v_a_1840_; uint8_t v___x_1841_; 
lean_inc(v_a_1780_);
v___x_1839_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_a_1780_, v___y_1836_);
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_a_1840_);
lean_dec_ref(v___x_1839_);
v___x_1841_ = l_Lean_Expr_hasFVar(v_a_1840_);
if (v___x_1841_ == 0)
{
uint8_t v___x_1842_; 
v___x_1842_ = l_Lean_Expr_hasMVar(v_a_1840_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; 
lean_inc(v_a_1840_);
v___x_1843_ = l_Lean_Meta_mkDecide(v_a_1840_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1845_; uint8_t v_foApprox_1846_; uint8_t v_ctxApprox_1847_; uint8_t v_quasiPatternApprox_1848_; uint8_t v_constApprox_1849_; uint8_t v_isDefEqStuckEx_1850_; uint8_t v_unificationHints_1851_; uint8_t v_proofIrrelevance_1852_; uint8_t v_assignSyntheticOpaque_1853_; uint8_t v_offsetCnstrs_1854_; uint8_t v_etaStruct_1855_; uint8_t v_univApprox_1856_; uint8_t v_iota_1857_; uint8_t v_beta_1858_; uint8_t v_proj_1859_; uint8_t v_zeta_1860_; uint8_t v_zetaDelta_1861_; uint8_t v_zetaUnused_1862_; uint8_t v_zetaHave_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1900_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref(v___x_1843_);
v___x_1845_ = l_Lean_Meta_Context_config(v___y_1835_);
v_foApprox_1846_ = lean_ctor_get_uint8(v___x_1845_, 0);
v_ctxApprox_1847_ = lean_ctor_get_uint8(v___x_1845_, 1);
v_quasiPatternApprox_1848_ = lean_ctor_get_uint8(v___x_1845_, 2);
v_constApprox_1849_ = lean_ctor_get_uint8(v___x_1845_, 3);
v_isDefEqStuckEx_1850_ = lean_ctor_get_uint8(v___x_1845_, 4);
v_unificationHints_1851_ = lean_ctor_get_uint8(v___x_1845_, 5);
v_proofIrrelevance_1852_ = lean_ctor_get_uint8(v___x_1845_, 6);
v_assignSyntheticOpaque_1853_ = lean_ctor_get_uint8(v___x_1845_, 7);
v_offsetCnstrs_1854_ = lean_ctor_get_uint8(v___x_1845_, 8);
v_etaStruct_1855_ = lean_ctor_get_uint8(v___x_1845_, 10);
v_univApprox_1856_ = lean_ctor_get_uint8(v___x_1845_, 11);
v_iota_1857_ = lean_ctor_get_uint8(v___x_1845_, 12);
v_beta_1858_ = lean_ctor_get_uint8(v___x_1845_, 13);
v_proj_1859_ = lean_ctor_get_uint8(v___x_1845_, 14);
v_zeta_1860_ = lean_ctor_get_uint8(v___x_1845_, 15);
v_zetaDelta_1861_ = lean_ctor_get_uint8(v___x_1845_, 16);
v_zetaUnused_1862_ = lean_ctor_get_uint8(v___x_1845_, 17);
v_zetaHave_1863_ = lean_ctor_get_uint8(v___x_1845_, 18);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1865_ = v___x_1845_;
v_isShared_1866_ = v_isSharedCheck_1900_;
goto v_resetjp_1864_;
}
else
{
lean_dec(v___x_1845_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1900_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
uint8_t v_trackZetaDelta_1867_; lean_object* v_zetaDeltaSet_1868_; lean_object* v_lctx_1869_; lean_object* v_localInstances_1870_; lean_object* v_defEqCtx_x3f_1871_; lean_object* v_synthPendingDepth_1872_; lean_object* v_canUnfold_x3f_1873_; uint8_t v_univApprox_1874_; uint8_t v_inTypeClassResolution_1875_; uint8_t v_cacheInferType_1876_; uint8_t v___x_1877_; lean_object* v_config_1879_; 
v_trackZetaDelta_1867_ = lean_ctor_get_uint8(v___y_1835_, sizeof(void*)*7);
v_zetaDeltaSet_1868_ = lean_ctor_get(v___y_1835_, 1);
v_lctx_1869_ = lean_ctor_get(v___y_1835_, 2);
v_localInstances_1870_ = lean_ctor_get(v___y_1835_, 3);
v_defEqCtx_x3f_1871_ = lean_ctor_get(v___y_1835_, 4);
v_synthPendingDepth_1872_ = lean_ctor_get(v___y_1835_, 5);
v_canUnfold_x3f_1873_ = lean_ctor_get(v___y_1835_, 6);
v_univApprox_1874_ = lean_ctor_get_uint8(v___y_1835_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1875_ = lean_ctor_get_uint8(v___y_1835_, sizeof(void*)*7 + 2);
v_cacheInferType_1876_ = lean_ctor_get_uint8(v___y_1835_, sizeof(void*)*7 + 3);
v___x_1877_ = 1;
if (v_isShared_1866_ == 0)
{
v_config_1879_ = v___x_1865_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1899_, 0, v_foApprox_1846_);
lean_ctor_set_uint8(v_reuseFailAlloc_1899_, 1, v_ctxApprox_1847_);
lean_ctor_set_uint8(v_reuseFailAlloc_1899_, 2, v_quasiPatternApprox_1848_);
lean_ctor_set_uint8(v_reuseFailAlloc_1899_, 3, v_constApprox_1849_);
lean_ctor_set_uint8(v_reuseFailAlloc_1899_, 4, v_isDefEqStuckEx_1850_);
lean_ctor_set_uint8(v_reuseFailAlloc_1899_, 5, v_unificationHints_1851_);
lean_ctor_set_uint8(v_reuseFailAlloc_1899_, 6, v_proofIrrelevance_1852_);
lean_ctor_set_uint8(v_reuseFailAlloc_1899_, 7, v_assignSyntheticOpaque_1853_);
lean_ctor_set_uint8(v_reuseFailAlloc_1899_, 8, v_offsetCnstrs_1854_);
lean_ctor_set_uint8(v_reuseFailAlloc_1899_, 10, v_etaStruct_1855_);
lean_ctor_set_uint8(v_reuseFailAlloc_1899_, 11, v_univApprox_1856_);
lean_ctor_set_uint8(v_reuseFailAlloc_1899_, 12, v_iota_1857_);
lean_ctor_set_uint8(v_reuseFailAlloc_1899_, 13, v_beta_1858_);
lean_ctor_set_uint8(v_reuseFailAlloc_1899_, 14, v_proj_1859_);
lean_ctor_set_uint8(v_reuseFailAlloc_1899_, 15, v_zeta_1860_);
lean_ctor_set_uint8(v_reuseFailAlloc_1899_, 16, v_zetaDelta_1861_);
lean_ctor_set_uint8(v_reuseFailAlloc_1899_, 17, v_zetaUnused_1862_);
lean_ctor_set_uint8(v_reuseFailAlloc_1899_, 18, v_zetaHave_1863_);
v_config_1879_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
uint64_t v___x_1880_; uint64_t v___x_1881_; uint64_t v___x_1882_; uint64_t v___x_1883_; uint64_t v___x_1884_; uint64_t v_key_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
lean_ctor_set_uint8(v_config_1879_, 9, v___x_1877_);
v___x_1880_ = l_Lean_Meta_Context_configKey(v___y_1835_);
v___x_1881_ = 2ULL;
v___x_1882_ = lean_uint64_shift_right(v___x_1880_, v___x_1881_);
v___x_1883_ = lean_uint64_shift_left(v___x_1882_, v___x_1881_);
v___x_1884_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7);
v_key_1885_ = lean_uint64_lor(v___x_1883_, v___x_1884_);
v___x_1886_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1886_, 0, v_config_1879_);
lean_ctor_set_uint64(v___x_1886_, sizeof(void*)*1, v_key_1885_);
lean_inc(v_canUnfold_x3f_1873_);
lean_inc(v_synthPendingDepth_1872_);
lean_inc(v_defEqCtx_x3f_1871_);
lean_inc_ref(v_localInstances_1870_);
lean_inc_ref(v_lctx_1869_);
lean_inc(v_zetaDeltaSet_1868_);
v___x_1887_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1887_, 0, v___x_1886_);
lean_ctor_set(v___x_1887_, 1, v_zetaDeltaSet_1868_);
lean_ctor_set(v___x_1887_, 2, v_lctx_1869_);
lean_ctor_set(v___x_1887_, 3, v_localInstances_1870_);
lean_ctor_set(v___x_1887_, 4, v_defEqCtx_x3f_1871_);
lean_ctor_set(v___x_1887_, 5, v_synthPendingDepth_1872_);
lean_ctor_set(v___x_1887_, 6, v_canUnfold_x3f_1873_);
lean_ctor_set_uint8(v___x_1887_, sizeof(void*)*7, v_trackZetaDelta_1867_);
lean_ctor_set_uint8(v___x_1887_, sizeof(void*)*7 + 1, v_univApprox_1874_);
lean_ctor_set_uint8(v___x_1887_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1875_);
lean_ctor_set_uint8(v___x_1887_, sizeof(void*)*7 + 3, v_cacheInferType_1876_);
lean_inc(v___y_1838_);
lean_inc_ref(v___y_1837_);
lean_inc(v___y_1836_);
lean_inc(v_a_1844_);
v___x_1888_ = lean_whnf(v_a_1844_, v___x_1887_, v___y_1836_, v___y_1837_, v___y_1838_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref(v___x_1888_);
v___y_1795_ = v_a_1844_;
v___y_1796_ = v_a_1840_;
v___y_1797_ = v___y_1838_;
v___y_1798_ = v___y_1833_;
v___y_1799_ = v___y_1832_;
v___y_1800_ = v___y_1835_;
v___y_1801_ = v___y_1834_;
v___y_1802_ = v___y_1837_;
v___y_1803_ = v___y_1836_;
v_a_1804_ = v_a_1889_;
goto v___jp_1794_;
}
else
{
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1890_; 
v_a_1890_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1890_);
lean_dec_ref(v___x_1888_);
v___y_1795_ = v_a_1844_;
v___y_1796_ = v_a_1840_;
v___y_1797_ = v___y_1838_;
v___y_1798_ = v___y_1833_;
v___y_1799_ = v___y_1832_;
v___y_1800_ = v___y_1835_;
v___y_1801_ = v___y_1834_;
v___y_1802_ = v___y_1837_;
v___y_1803_ = v___y_1836_;
v_a_1804_ = v_a_1890_;
goto v___jp_1794_;
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_dec(v_a_1844_);
lean_dec(v_a_1840_);
lean_del_object(v___x_1782_);
lean_dec(v_a_1780_);
v_a_1891_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1888_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1888_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
lean_dec(v_a_1840_);
lean_del_object(v___x_1782_);
lean_dec(v_a_1780_);
v_a_1901_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1843_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1843_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
else
{
lean_dec(v_a_1840_);
lean_del_object(v___x_1782_);
v___y_1785_ = v___y_1832_;
v___y_1786_ = v___y_1833_;
v___y_1787_ = v___y_1834_;
v___y_1788_ = v___y_1835_;
v___y_1789_ = v___y_1836_;
v___y_1790_ = v___y_1837_;
v___y_1791_ = v___y_1838_;
goto v___jp_1784_;
}
}
else
{
lean_dec(v_a_1840_);
lean_del_object(v___x_1782_);
v___y_1785_ = v___y_1832_;
v___y_1786_ = v___y_1833_;
v___y_1787_ = v___y_1834_;
v___y_1788_ = v___y_1835_;
v___y_1789_ = v___y_1836_;
v___y_1790_ = v___y_1837_;
v___y_1791_ = v___y_1838_;
goto v___jp_1784_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___boxed(lean_object* v_numIndices_1942_, lean_object* v_useDecide_1943_, lean_object* v_prop_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_){
_start:
{
uint8_t v_useDecide_boxed_1953_; lean_object* v_res_1954_; 
v_useDecide_boxed_1953_ = lean_unbox(v_useDecide_1943_);
v_res_1954_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_1942_, v_useDecide_boxed_1953_, v_prop_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_);
lean_dec(v_a_1951_);
lean_dec_ref(v_a_1950_);
lean_dec(v_a_1949_);
lean_dec_ref(v_a_1948_);
lean_dec(v_a_1947_);
lean_dec_ref(v_a_1946_);
lean_dec(v_a_1945_);
lean_dec(v_numIndices_1942_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2(lean_object* v_cls_1955_, lean_object* v_msg_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v_cls_1955_, v_msg_1956_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___boxed(lean_object* v_cls_1966_, lean_object* v_msg_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2(v_cls_1966_, v_msg_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2(lean_object* v_a_1977_, lean_object* v_numIndices_1978_, lean_object* v_as_1979_, lean_object* v_i_1980_, lean_object* v_a_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v___x_1990_; 
v___x_1990_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_a_1977_, v_numIndices_1978_, v_as_1979_, v_i_1980_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_a_1991_, lean_object* v_numIndices_1992_, lean_object* v_as_1993_, lean_object* v_i_1994_, lean_object* v_a_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2(v_a_1991_, v_numIndices_1992_, v_as_1993_, v_i_1994_, v_a_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v_as_1993_);
lean_dec(v_numIndices_1992_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5(lean_object* v_a_2005_, lean_object* v_numIndices_2006_, lean_object* v_as_2007_, lean_object* v_i_2008_, lean_object* v_a_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_a_2005_, v_numIndices_2006_, v_as_2007_, v_i_2008_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_a_2019_, lean_object* v_numIndices_2020_, lean_object* v_as_2021_, lean_object* v_i_2022_, lean_object* v_a_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5(v_a_2019_, v_numIndices_2020_, v_as_2021_, v_i_2022_, v_a_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec_ref(v_as_2021_);
lean_dec(v_numIndices_2020_);
return v_res_2032_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3(void){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2038_ = lean_box(0);
v___x_2039_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__2));
v___x_2040_ = l_Lean_mkConst(v___x_2039_, v___x_2038_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27(lean_object* v_numIndices_2044_, uint8_t v_useDecideBool_2045_, lean_object* v_e_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_){
_start:
{
lean_object* v___x_2055_; 
lean_inc_ref(v_e_2046_);
v___x_2055_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2046_, v_a_2051_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2236_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2236_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2236_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2065_; uint8_t v___x_2066_; 
v___x_2065_ = l_Lean_Expr_cleanupAnnotations(v_a_2056_);
v___x_2066_ = l_Lean_Expr_isApp(v___x_2065_);
if (v___x_2066_ == 0)
{
lean_dec_ref(v___x_2065_);
lean_dec_ref(v_e_2046_);
goto v___jp_2060_;
}
else
{
lean_object* v_arg_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; 
v_arg_2067_ = lean_ctor_get(v___x_2065_, 1);
lean_inc_ref(v_arg_2067_);
v___x_2068_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2065_);
v___x_2069_ = l_Lean_Expr_isApp(v___x_2068_);
if (v___x_2069_ == 0)
{
lean_dec_ref(v___x_2068_);
lean_dec_ref(v_arg_2067_);
lean_dec_ref(v_e_2046_);
goto v___jp_2060_;
}
else
{
lean_object* v_arg_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; 
v_arg_2070_ = lean_ctor_get(v___x_2068_, 1);
lean_inc_ref(v_arg_2070_);
v___x_2071_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2068_);
v___x_2072_ = l_Lean_Expr_isApp(v___x_2071_);
if (v___x_2072_ == 0)
{
lean_dec_ref(v___x_2071_);
lean_dec_ref(v_arg_2070_);
lean_dec_ref(v_arg_2067_);
lean_dec_ref(v_e_2046_);
goto v___jp_2060_;
}
else
{
lean_object* v_arg_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
v_arg_2073_ = lean_ctor_get(v___x_2071_, 1);
lean_inc_ref(v_arg_2073_);
v___x_2074_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2071_);
v___x_2075_ = l_Lean_Expr_isApp(v___x_2074_);
if (v___x_2075_ == 0)
{
lean_dec_ref(v___x_2074_);
lean_dec_ref(v_arg_2073_);
lean_dec_ref(v_arg_2070_);
lean_dec_ref(v_arg_2067_);
lean_dec_ref(v_e_2046_);
goto v___jp_2060_;
}
else
{
lean_object* v_arg_2076_; lean_object* v___x_2077_; uint8_t v___x_2078_; 
v_arg_2076_ = lean_ctor_get(v___x_2074_, 1);
lean_inc_ref(v_arg_2076_);
v___x_2077_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2074_);
v___x_2078_ = l_Lean_Expr_isApp(v___x_2077_);
if (v___x_2078_ == 0)
{
lean_dec_ref(v___x_2077_);
lean_dec_ref(v_arg_2076_);
lean_dec_ref(v_arg_2073_);
lean_dec_ref(v_arg_2070_);
lean_dec_ref(v_arg_2067_);
lean_dec_ref(v_e_2046_);
goto v___jp_2060_;
}
else
{
lean_object* v_arg_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; 
v_arg_2079_ = lean_ctor_get(v___x_2077_, 1);
lean_inc_ref(v_arg_2079_);
v___x_2080_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2077_);
v___x_2081_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__2));
v___x_2082_ = l_Lean_Expr_isConstOf(v___x_2080_, v___x_2081_);
if (v___x_2082_ == 0)
{
lean_dec_ref(v___x_2080_);
lean_dec_ref(v_arg_2079_);
lean_dec_ref(v_arg_2076_);
lean_dec_ref(v_arg_2073_);
lean_dec_ref(v_arg_2070_);
lean_dec_ref(v_arg_2067_);
lean_dec_ref(v_e_2046_);
goto v___jp_2060_;
}
else
{
lean_object* v___x_2083_; 
lean_del_object(v___x_2058_);
lean_inc_ref(v_arg_2076_);
v___x_2083_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2044_, v_useDecideBool_2045_, v_arg_2076_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2227_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2086_ = v___x_2083_;
v_isShared_2087_ = v_isSharedCheck_2227_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_2083_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2227_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2088_; 
v___x_2088_ = l_Lean_Expr_constLevels_x21(v___x_2080_);
if (lean_obj_tag(v_a_2084_) == 1)
{
lean_object* v_val_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2104_; 
lean_dec_ref(v___x_2080_);
lean_dec_ref(v_e_2046_);
v_val_2089_ = lean_ctor_get(v_a_2084_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v_a_2084_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2091_ = v_a_2084_;
v_isShared_2092_ = v_isSharedCheck_2104_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_val_2089_);
lean_dec(v_a_2084_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2104_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2097_; 
v___x_2093_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__7));
v___x_2094_ = l_Lean_mkConst(v___x_2093_, v___x_2088_);
lean_inc_ref(v_arg_2070_);
v___x_2095_ = l_Lean_mkApp6(v___x_2094_, v_arg_2076_, v_arg_2073_, v_val_2089_, v_arg_2079_, v_arg_2070_, v_arg_2067_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 0, v___x_2095_);
v___x_2097_ = v___x_2091_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2098_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2098_, 0, v_arg_2070_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
lean_ctor_set_uint8(v___x_2098_, sizeof(void*)*2, v___x_2082_);
v___x_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 0, v___x_2099_);
v___x_2101_ = v___x_2086_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
else
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
lean_del_object(v___x_2086_);
lean_dec(v_a_2084_);
lean_inc_ref(v_arg_2076_);
v___x_2105_ = l_Lean_mkNot(v_arg_2076_);
v___x_2106_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2044_, v_useDecideBool_2045_, v___x_2105_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2218_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2109_ = v___x_2106_;
v_isShared_2110_ = v_isSharedCheck_2218_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2106_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2218_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
if (lean_obj_tag(v_a_2107_) == 1)
{
lean_object* v_val_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2126_; 
lean_dec_ref(v___x_2080_);
lean_dec_ref(v_e_2046_);
v_val_2111_ = lean_ctor_get(v_a_2107_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v_a_2107_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2113_ = v_a_2107_;
v_isShared_2114_ = v_isSharedCheck_2126_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_val_2111_);
lean_dec(v_a_2107_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2126_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2119_; 
v___x_2115_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__9));
v___x_2116_ = l_Lean_mkConst(v___x_2115_, v___x_2088_);
lean_inc_ref(v_arg_2067_);
v___x_2117_ = l_Lean_mkApp6(v___x_2116_, v_arg_2076_, v_arg_2073_, v_val_2111_, v_arg_2079_, v_arg_2070_, v_arg_2067_);
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 0, v___x_2117_);
v___x_2119_ = v___x_2113_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v___x_2117_);
v___x_2119_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2123_; 
v___x_2120_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2120_, 0, v_arg_2067_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
lean_ctor_set_uint8(v___x_2120_, sizeof(void*)*2, v___x_2082_);
v___x_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v___x_2121_);
v___x_2123_ = v___x_2109_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2121_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
else
{
lean_object* v___x_2127_; 
lean_del_object(v___x_2109_);
lean_dec(v_a_2107_);
lean_inc(v_a_2053_);
lean_inc_ref(v_a_2052_);
lean_inc(v_a_2051_);
lean_inc_ref(v_a_2050_);
lean_inc(v_a_2049_);
lean_inc_ref(v_a_2048_);
lean_inc(v_a_2047_);
lean_inc_ref(v_arg_2076_);
v___x_2127_ = lean_simp(v_arg_2076_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2209_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2130_ = v___x_2127_;
v_isShared_2131_ = v_isSharedCheck_2209_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2127_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2209_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v_expr_2132_; uint8_t v___x_2133_; 
v_expr_2132_ = lean_ctor_get(v_a_2128_, 0);
v___x_2133_ = lean_expr_eqv(v_expr_2132_, v_arg_2076_);
if (v___x_2133_ == 0)
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
lean_del_object(v___x_2130_);
v___x_2134_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3);
lean_inc_ref(v_expr_2132_);
v___x_2135_ = l_Lean_Expr_app___override(v___x_2134_, v_expr_2132_);
v___x_2136_ = lean_box(0);
v___x_2137_ = l_Lean_Meta_trySynthInstance(v___x_2135_, v___x_2136_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2186_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2140_ = v___x_2137_;
v_isShared_2141_ = v_isSharedCheck_2186_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2137_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2186_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
if (lean_obj_tag(v_a_2138_) == 1)
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2172_; 
lean_inc_ref(v_expr_2132_);
lean_del_object(v___x_2140_);
lean_dec_ref(v_e_2046_);
v_a_2142_ = lean_ctor_get(v_a_2138_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_a_2138_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2144_ = v_a_2138_;
v_isShared_2145_ = v_isSharedCheck_2172_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v_a_2138_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2172_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2146_; 
v___x_2146_ = l_Lean_Meta_Simp_Result_getProof(v_a_2128_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2163_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2149_ = v___x_2146_;
v_isShared_2150_ = v_isSharedCheck_2163_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2146_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2163_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2156_; 
v___x_2151_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__5));
v___x_2152_ = l_Lean_mkConst(v___x_2151_, v___x_2088_);
lean_inc_ref(v_arg_2067_);
lean_inc_ref(v_arg_2070_);
lean_inc(v_a_2142_);
lean_inc_ref(v_expr_2132_);
lean_inc_ref(v_arg_2079_);
v___x_2153_ = l_Lean_mkApp8(v___x_2152_, v_arg_2079_, v_arg_2076_, v_expr_2132_, v_arg_2073_, v_a_2142_, v_arg_2070_, v_arg_2067_, v_a_2147_);
v___x_2154_ = l_Lean_mkApp5(v___x_2080_, v_arg_2079_, v_expr_2132_, v_a_2142_, v_arg_2070_, v_arg_2067_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 0, v___x_2153_);
v___x_2156_ = v___x_2144_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2153_);
v___x_2156_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2160_; 
v___x_2157_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2157_, 0, v___x_2154_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
lean_ctor_set_uint8(v___x_2157_, sizeof(void*)*2, v___x_2082_);
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 0, v___x_2158_);
v___x_2160_ = v___x_2149_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2158_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_del_object(v___x_2144_);
lean_dec(v_a_2142_);
lean_dec_ref(v_expr_2132_);
lean_dec(v___x_2088_);
lean_dec_ref(v___x_2080_);
lean_dec_ref(v_arg_2079_);
lean_dec_ref(v_arg_2076_);
lean_dec_ref(v_arg_2073_);
lean_dec_ref(v_arg_2070_);
lean_dec_ref(v_arg_2067_);
v_a_2164_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2146_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2146_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
}
else
{
lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2183_; 
lean_dec(v_a_2138_);
lean_dec(v___x_2088_);
lean_dec_ref(v___x_2080_);
lean_dec_ref(v_arg_2079_);
lean_dec_ref(v_arg_2076_);
lean_dec_ref(v_arg_2073_);
lean_dec_ref(v_arg_2070_);
lean_dec_ref(v_arg_2067_);
v_isSharedCheck_2183_ = !lean_is_exclusive(v_a_2128_);
if (v_isSharedCheck_2183_ == 0)
{
lean_object* v_unused_2184_; lean_object* v_unused_2185_; 
v_unused_2184_ = lean_ctor_get(v_a_2128_, 1);
lean_dec(v_unused_2184_);
v_unused_2185_ = lean_ctor_get(v_a_2128_, 0);
lean_dec(v_unused_2185_);
v___x_2174_ = v_a_2128_;
v_isShared_2175_ = v_isSharedCheck_2183_;
goto v_resetjp_2173_;
}
else
{
lean_dec(v_a_2128_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2183_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 1, v___x_2136_);
lean_ctor_set(v___x_2174_, 0, v_e_2046_);
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_e_2046_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v___x_2136_);
v___x_2177_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
lean_object* v___x_2178_; lean_object* v___x_2180_; 
lean_ctor_set_uint8(v___x_2177_, sizeof(void*)*2, v___x_2082_);
v___x_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2177_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v___x_2178_);
v___x_2180_ = v___x_2140_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2178_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
}
}
else
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2194_; 
lean_dec(v_a_2128_);
lean_dec(v___x_2088_);
lean_dec_ref(v___x_2080_);
lean_dec_ref(v_arg_2079_);
lean_dec_ref(v_arg_2076_);
lean_dec_ref(v_arg_2073_);
lean_dec_ref(v_arg_2070_);
lean_dec_ref(v_arg_2067_);
lean_dec_ref(v_e_2046_);
v_a_2187_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2189_ = v___x_2137_;
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2137_);
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
lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2206_; 
lean_dec(v___x_2088_);
lean_dec_ref(v___x_2080_);
lean_dec_ref(v_arg_2079_);
lean_dec_ref(v_arg_2076_);
lean_dec_ref(v_arg_2073_);
lean_dec_ref(v_arg_2070_);
lean_dec_ref(v_arg_2067_);
v_isSharedCheck_2206_ = !lean_is_exclusive(v_a_2128_);
if (v_isSharedCheck_2206_ == 0)
{
lean_object* v_unused_2207_; lean_object* v_unused_2208_; 
v_unused_2207_ = lean_ctor_get(v_a_2128_, 1);
lean_dec(v_unused_2207_);
v_unused_2208_ = lean_ctor_get(v_a_2128_, 0);
lean_dec(v_unused_2208_);
v___x_2196_ = v_a_2128_;
v_isShared_2197_ = v_isSharedCheck_2206_;
goto v_resetjp_2195_;
}
else
{
lean_dec(v_a_2128_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2206_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2198_; lean_object* v___x_2200_; 
v___x_2198_ = lean_box(0);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 1, v___x_2198_);
lean_ctor_set(v___x_2196_, 0, v_e_2046_);
v___x_2200_ = v___x_2196_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_e_2046_);
lean_ctor_set(v_reuseFailAlloc_2205_, 1, v___x_2198_);
v___x_2200_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
lean_object* v___x_2201_; lean_object* v___x_2203_; 
lean_ctor_set_uint8(v___x_2200_, sizeof(void*)*2, v___x_2082_);
v___x_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 0, v___x_2201_);
v___x_2203_ = v___x_2130_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2201_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
}
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec(v___x_2088_);
lean_dec_ref(v___x_2080_);
lean_dec_ref(v_arg_2079_);
lean_dec_ref(v_arg_2076_);
lean_dec_ref(v_arg_2073_);
lean_dec_ref(v_arg_2070_);
lean_dec_ref(v_arg_2067_);
lean_dec_ref(v_e_2046_);
v_a_2210_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2127_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2127_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
}
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2226_; 
lean_dec(v___x_2088_);
lean_dec_ref(v___x_2080_);
lean_dec_ref(v_arg_2079_);
lean_dec_ref(v_arg_2076_);
lean_dec_ref(v_arg_2073_);
lean_dec_ref(v_arg_2070_);
lean_dec_ref(v_arg_2067_);
lean_dec_ref(v_e_2046_);
v_a_2219_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2221_ = v___x_2106_;
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2106_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2219_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
}
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
lean_dec_ref(v___x_2080_);
lean_dec_ref(v_arg_2079_);
lean_dec_ref(v_arg_2076_);
lean_dec_ref(v_arg_2073_);
lean_dec_ref(v_arg_2070_);
lean_dec_ref(v_arg_2067_);
lean_dec_ref(v_e_2046_);
v_a_2228_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2083_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2083_);
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
}
}
}
}
}
v___jp_2060_:
{
lean_object* v___x_2061_; lean_object* v___x_2063_; 
v___x_2061_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__0));
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v___x_2061_);
v___x_2063_ = v___x_2058_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2061_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
else
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
lean_dec_ref(v_e_2046_);
v_a_2237_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2239_ = v___x_2055_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2055_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___boxed(lean_object* v_numIndices_2245_, lean_object* v_useDecideBool_2246_, lean_object* v_e_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_){
_start:
{
uint8_t v_useDecideBool_boxed_2256_; lean_object* v_res_2257_; 
v_useDecideBool_boxed_2256_ = lean_unbox(v_useDecideBool_2246_);
v_res_2257_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27(v_numIndices_2245_, v_useDecideBool_boxed_2256_, v_e_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_);
lean_dec(v_a_2254_);
lean_dec_ref(v_a_2253_);
lean_dec(v_a_2252_);
lean_dec_ref(v_a_2251_);
lean_dec(v_a_2250_);
lean_dec_ref(v_a_2249_);
lean_dec(v_a_2248_);
lean_dec(v_numIndices_2245_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(lean_object* v_e_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_){
_start:
{
if (lean_obj_tag(v_e_2261_) == 6)
{
lean_object* v_binderName_2265_; lean_object* v___x_2266_; 
v_binderName_2265_ = lean_ctor_get(v_e_2261_, 0);
lean_inc(v_binderName_2265_);
v___x_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2266_, 0, v_binderName_2265_);
return v___x_2266_;
}
else
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2267_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__1));
v___x_2268_ = l_Lean_Core_mkFreshUserName(v___x_2267_, v_a_2262_, v_a_2263_);
return v___x_2268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___boxed(lean_object* v_e_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_e_2269_, v_a_2270_, v_a_2271_);
lean_dec(v_a_2271_);
lean_dec_ref(v_a_2270_);
lean_dec_ref(v_e_2269_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName(lean_object* v_e_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_e_2274_, v_a_2277_, v_a_2278_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___boxed(lean_object* v_e_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName(v_e_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_);
lean_dec(v_a_2285_);
lean_dec_ref(v_a_2284_);
lean_dec(v_a_2283_);
lean_dec_ref(v_a_2282_);
lean_dec_ref(v_e_2281_);
return v_res_2287_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2293_ = lean_box(0);
v___x_2294_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__2));
v___x_2295_ = l_Lean_mkConst(v___x_2294_, v___x_2293_);
return v___x_2295_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4(void){
_start:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2296_ = lean_unsigned_to_nat(0u);
v___x_2297_ = l_Lean_mkBVar(v___x_2296_);
return v___x_2297_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7(void){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2302_ = lean_box(0);
v___x_2303_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__6));
v___x_2304_ = l_Lean_mkConst(v___x_2303_, v___x_2302_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27(lean_object* v_numIndices_2308_, uint8_t v_useDecideBool_2309_, lean_object* v_e_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_){
_start:
{
lean_object* v___x_2319_; 
lean_inc_ref(v_e_2310_);
v___x_2319_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2310_, v_a_2315_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2529_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2322_ = v___x_2319_;
v_isShared_2323_ = v_isSharedCheck_2529_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2319_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2529_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2329_; uint8_t v___x_2330_; 
v___x_2329_ = l_Lean_Expr_cleanupAnnotations(v_a_2320_);
v___x_2330_ = l_Lean_Expr_isApp(v___x_2329_);
if (v___x_2330_ == 0)
{
lean_dec_ref(v___x_2329_);
lean_dec_ref(v_e_2310_);
goto v___jp_2324_;
}
else
{
lean_object* v_arg_2331_; lean_object* v___x_2332_; uint8_t v___x_2333_; 
v_arg_2331_ = lean_ctor_get(v___x_2329_, 1);
lean_inc_ref(v_arg_2331_);
v___x_2332_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2329_);
v___x_2333_ = l_Lean_Expr_isApp(v___x_2332_);
if (v___x_2333_ == 0)
{
lean_dec_ref(v___x_2332_);
lean_dec_ref(v_arg_2331_);
lean_dec_ref(v_e_2310_);
goto v___jp_2324_;
}
else
{
lean_object* v_arg_2334_; lean_object* v___x_2335_; uint8_t v___x_2336_; 
v_arg_2334_ = lean_ctor_get(v___x_2332_, 1);
lean_inc_ref(v_arg_2334_);
v___x_2335_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2332_);
v___x_2336_ = l_Lean_Expr_isApp(v___x_2335_);
if (v___x_2336_ == 0)
{
lean_dec_ref(v___x_2335_);
lean_dec_ref(v_arg_2334_);
lean_dec_ref(v_arg_2331_);
lean_dec_ref(v_e_2310_);
goto v___jp_2324_;
}
else
{
lean_object* v_arg_2337_; lean_object* v___x_2338_; uint8_t v___x_2339_; 
v_arg_2337_ = lean_ctor_get(v___x_2335_, 1);
lean_inc_ref(v_arg_2337_);
v___x_2338_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2335_);
v___x_2339_ = l_Lean_Expr_isApp(v___x_2338_);
if (v___x_2339_ == 0)
{
lean_dec_ref(v___x_2338_);
lean_dec_ref(v_arg_2337_);
lean_dec_ref(v_arg_2334_);
lean_dec_ref(v_arg_2331_);
lean_dec_ref(v_e_2310_);
goto v___jp_2324_;
}
else
{
lean_object* v_arg_2340_; lean_object* v___x_2341_; uint8_t v___x_2342_; 
v_arg_2340_ = lean_ctor_get(v___x_2338_, 1);
lean_inc_ref(v_arg_2340_);
v___x_2341_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2338_);
v___x_2342_ = l_Lean_Expr_isApp(v___x_2341_);
if (v___x_2342_ == 0)
{
lean_dec_ref(v___x_2341_);
lean_dec_ref(v_arg_2340_);
lean_dec_ref(v_arg_2337_);
lean_dec_ref(v_arg_2334_);
lean_dec_ref(v_arg_2331_);
lean_dec_ref(v_e_2310_);
goto v___jp_2324_;
}
else
{
lean_object* v_arg_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; uint8_t v___x_2346_; 
v_arg_2343_ = lean_ctor_get(v___x_2341_, 1);
lean_inc_ref(v_arg_2343_);
v___x_2344_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2341_);
v___x_2345_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__4));
v___x_2346_ = l_Lean_Expr_isConstOf(v___x_2344_, v___x_2345_);
if (v___x_2346_ == 0)
{
lean_dec_ref(v___x_2344_);
lean_dec_ref(v_arg_2343_);
lean_dec_ref(v_arg_2340_);
lean_dec_ref(v_arg_2337_);
lean_dec_ref(v_arg_2334_);
lean_dec_ref(v_arg_2331_);
lean_dec_ref(v_e_2310_);
goto v___jp_2324_;
}
else
{
lean_object* v___x_2347_; 
lean_del_object(v___x_2322_);
lean_inc_ref(v_arg_2340_);
v___x_2347_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2308_, v_useDecideBool_2309_, v_arg_2340_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2520_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2350_ = v___x_2347_;
v_isShared_2351_ = v_isSharedCheck_2520_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2347_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2520_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2352_; 
v___x_2352_ = l_Lean_Expr_constLevels_x21(v___x_2344_);
if (lean_obj_tag(v_a_2348_) == 1)
{
lean_object* v_val_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2370_; 
lean_dec_ref(v___x_2344_);
lean_dec_ref(v_e_2310_);
v_val_2353_ = lean_ctor_get(v_a_2348_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v_a_2348_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2355_ = v_a_2348_;
v_isShared_2356_ = v_isSharedCheck_2370_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_val_2353_);
lean_dec(v_a_2348_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2370_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2363_; 
lean_inc(v_val_2353_);
lean_inc_ref(v_arg_2334_);
v___x_2357_ = l_Lean_Expr_app___override(v_arg_2334_, v_val_2353_);
v___x_2358_ = l_Lean_Expr_headBeta(v___x_2357_);
v___x_2359_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__11));
v___x_2360_ = l_Lean_mkConst(v___x_2359_, v___x_2352_);
v___x_2361_ = l_Lean_mkApp6(v___x_2360_, v_arg_2340_, v_arg_2337_, v_val_2353_, v_arg_2343_, v_arg_2334_, v_arg_2331_);
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 0, v___x_2361_);
v___x_2363_ = v___x_2355_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2367_; 
v___x_2364_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2364_, 0, v___x_2358_);
lean_ctor_set(v___x_2364_, 1, v___x_2363_);
lean_ctor_set_uint8(v___x_2364_, sizeof(void*)*2, v___x_2346_);
v___x_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2364_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v___x_2365_);
v___x_2367_ = v___x_2350_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2365_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
else
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
lean_del_object(v___x_2350_);
lean_dec(v_a_2348_);
lean_inc_ref(v_arg_2340_);
v___x_2371_ = l_Lean_mkNot(v_arg_2340_);
v___x_2372_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2308_, v_useDecideBool_2309_, v___x_2371_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2511_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2375_ = v___x_2372_;
v_isShared_2376_ = v_isSharedCheck_2511_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2372_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2511_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
if (lean_obj_tag(v_a_2373_) == 1)
{
lean_object* v_val_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2394_; 
lean_dec_ref(v___x_2344_);
lean_dec_ref(v_e_2310_);
v_val_2377_ = lean_ctor_get(v_a_2373_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v_a_2373_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2379_ = v_a_2373_;
v_isShared_2380_ = v_isSharedCheck_2394_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_val_2377_);
lean_dec(v_a_2373_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2394_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2387_; 
lean_inc(v_val_2377_);
lean_inc_ref(v_arg_2331_);
v___x_2381_ = l_Lean_Expr_app___override(v_arg_2331_, v_val_2377_);
v___x_2382_ = l_Lean_Expr_headBeta(v___x_2381_);
v___x_2383_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__13));
v___x_2384_ = l_Lean_mkConst(v___x_2383_, v___x_2352_);
v___x_2385_ = l_Lean_mkApp6(v___x_2384_, v_arg_2340_, v_arg_2337_, v_val_2377_, v_arg_2343_, v_arg_2334_, v_arg_2331_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v___x_2385_);
v___x_2387_ = v___x_2379_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v___x_2385_);
v___x_2387_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2391_; 
v___x_2388_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2388_, 0, v___x_2382_);
lean_ctor_set(v___x_2388_, 1, v___x_2387_);
lean_ctor_set_uint8(v___x_2388_, sizeof(void*)*2, v___x_2346_);
v___x_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 0, v___x_2389_);
v___x_2391_ = v___x_2375_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2389_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
else
{
lean_object* v___x_2395_; 
lean_del_object(v___x_2375_);
lean_dec(v_a_2373_);
lean_inc(v_a_2317_);
lean_inc_ref(v_a_2316_);
lean_inc(v_a_2315_);
lean_inc_ref(v_a_2314_);
lean_inc(v_a_2313_);
lean_inc_ref(v_a_2312_);
lean_inc(v_a_2311_);
lean_inc_ref(v_arg_2340_);
v___x_2395_ = lean_simp(v_arg_2340_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2502_; 
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2398_ = v___x_2395_;
v_isShared_2399_ = v_isSharedCheck_2502_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2395_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2502_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v_expr_2400_; uint8_t v___x_2401_; 
v_expr_2400_ = lean_ctor_get(v_a_2396_, 0);
v___x_2401_ = lean_expr_eqv(v_expr_2400_, v_arg_2340_);
if (v___x_2401_ == 0)
{
lean_object* v___x_2402_; 
lean_inc_ref(v_expr_2400_);
lean_del_object(v___x_2398_);
v___x_2402_ = l_Lean_Meta_Simp_Result_getProof(v_a_2396_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_a_2403_);
lean_dec_ref(v___x_2402_);
v___x_2404_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3);
lean_inc_ref(v_expr_2400_);
v___x_2405_ = l_Lean_Expr_app___override(v___x_2404_, v_expr_2400_);
v___x_2406_ = lean_box(0);
v___x_2407_ = l_Lean_Meta_trySynthInstance(v___x_2405_, v___x_2406_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2471_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2410_ = v___x_2407_;
v_isShared_2411_ = v_isSharedCheck_2471_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2407_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2471_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
if (lean_obj_tag(v_a_2408_) == 1)
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2465_; 
lean_del_object(v___x_2410_);
lean_dec_ref(v_e_2310_);
v_a_2412_ = lean_ctor_get(v_a_2408_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v_a_2408_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2414_ = v_a_2408_;
v_isShared_2415_ = v_isSharedCheck_2465_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v_a_2408_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2465_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2416_; 
v___x_2416_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_arg_2334_, v_a_2316_, v_a_2317_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v_a_2417_; lean_object* v___x_2418_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
lean_inc(v_a_2417_);
lean_dec_ref(v___x_2416_);
v___x_2418_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_arg_2331_, v_a_2316_, v_a_2317_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2448_; 
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2421_ = v___x_2418_;
v_isShared_2422_ = v_isSharedCheck_2448_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2418_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2448_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; uint8_t v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2441_; 
v___x_2423_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3);
v___x_2424_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4);
lean_inc_n(v_a_2403_, 2);
lean_inc_ref_n(v_expr_2400_, 5);
lean_inc_ref_n(v_arg_2340_, 2);
v___x_2425_ = l_Lean_mkApp4(v___x_2423_, v_arg_2340_, v_expr_2400_, v_a_2403_, v___x_2424_);
lean_inc_ref(v_arg_2334_);
v___x_2426_ = l_Lean_Expr_app___override(v_arg_2334_, v___x_2425_);
v___x_2427_ = l_Lean_Expr_headBeta(v___x_2426_);
v___x_2428_ = 0;
v___x_2429_ = l_Lean_mkLambda(v_a_2417_, v___x_2428_, v_expr_2400_, v___x_2427_);
v___x_2430_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7);
v___x_2431_ = l_Lean_mkApp4(v___x_2430_, v_arg_2340_, v_expr_2400_, v_a_2403_, v___x_2424_);
lean_inc_ref(v_arg_2331_);
v___x_2432_ = l_Lean_Expr_app___override(v_arg_2331_, v___x_2431_);
v___x_2433_ = l_Lean_Expr_headBeta(v___x_2432_);
v___x_2434_ = l_Lean_mkNot(v_expr_2400_);
v___x_2435_ = l_Lean_mkLambda(v_a_2419_, v___x_2428_, v___x_2434_, v___x_2433_);
lean_inc(v_a_2412_);
lean_inc_ref(v_arg_2343_);
v___x_2436_ = l_Lean_mkApp5(v___x_2344_, v_arg_2343_, v_expr_2400_, v_a_2412_, v___x_2429_, v___x_2435_);
v___x_2437_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__9));
v___x_2438_ = l_Lean_mkConst(v___x_2437_, v___x_2352_);
v___x_2439_ = l_Lean_mkApp8(v___x_2438_, v_arg_2343_, v_arg_2340_, v_expr_2400_, v_arg_2337_, v_a_2412_, v_arg_2334_, v_arg_2331_, v_a_2403_);
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 0, v___x_2439_);
v___x_2441_ = v___x_2414_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v___x_2439_);
v___x_2441_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2445_; 
v___x_2442_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2442_, 0, v___x_2436_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
lean_ctor_set_uint8(v___x_2442_, sizeof(void*)*2, v___x_2346_);
v___x_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 0, v___x_2443_);
v___x_2445_ = v___x_2421_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v___x_2443_);
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
else
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2456_; 
lean_dec(v_a_2417_);
lean_del_object(v___x_2414_);
lean_dec(v_a_2412_);
lean_dec(v_a_2403_);
lean_dec_ref(v_expr_2400_);
lean_dec(v___x_2352_);
lean_dec_ref(v___x_2344_);
lean_dec_ref(v_arg_2343_);
lean_dec_ref(v_arg_2340_);
lean_dec_ref(v_arg_2337_);
lean_dec_ref(v_arg_2334_);
lean_dec_ref(v_arg_2331_);
v_a_2449_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2451_ = v___x_2418_;
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2418_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
else
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2464_; 
lean_del_object(v___x_2414_);
lean_dec(v_a_2412_);
lean_dec(v_a_2403_);
lean_dec_ref(v_expr_2400_);
lean_dec(v___x_2352_);
lean_dec_ref(v___x_2344_);
lean_dec_ref(v_arg_2343_);
lean_dec_ref(v_arg_2340_);
lean_dec_ref(v_arg_2337_);
lean_dec_ref(v_arg_2334_);
lean_dec_ref(v_arg_2331_);
v_a_2457_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2459_ = v___x_2416_;
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2416_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
if (v_isShared_2460_ == 0)
{
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2457_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
}
}
else
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2469_; 
lean_dec(v_a_2408_);
lean_dec(v_a_2403_);
lean_dec_ref(v_expr_2400_);
lean_dec(v___x_2352_);
lean_dec_ref(v___x_2344_);
lean_dec_ref(v_arg_2343_);
lean_dec_ref(v_arg_2340_);
lean_dec_ref(v_arg_2337_);
lean_dec_ref(v_arg_2334_);
lean_dec_ref(v_arg_2331_);
v___x_2466_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2466_, 0, v_e_2310_);
lean_ctor_set(v___x_2466_, 1, v___x_2406_);
lean_ctor_set_uint8(v___x_2466_, sizeof(void*)*2, v___x_2346_);
v___x_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2466_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 0, v___x_2467_);
v___x_2469_ = v___x_2410_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v___x_2467_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
else
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
lean_dec(v_a_2403_);
lean_dec_ref(v_expr_2400_);
lean_dec(v___x_2352_);
lean_dec_ref(v___x_2344_);
lean_dec_ref(v_arg_2343_);
lean_dec_ref(v_arg_2340_);
lean_dec_ref(v_arg_2337_);
lean_dec_ref(v_arg_2334_);
lean_dec_ref(v_arg_2331_);
lean_dec_ref(v_e_2310_);
v_a_2472_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2474_ = v___x_2407_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2407_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2472_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
else
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2487_; 
lean_dec_ref(v_expr_2400_);
lean_dec(v___x_2352_);
lean_dec_ref(v___x_2344_);
lean_dec_ref(v_arg_2343_);
lean_dec_ref(v_arg_2340_);
lean_dec_ref(v_arg_2337_);
lean_dec_ref(v_arg_2334_);
lean_dec_ref(v_arg_2331_);
lean_dec_ref(v_e_2310_);
v_a_2480_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2482_ = v___x_2402_;
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2402_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
}
else
{
lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2499_; 
lean_dec(v___x_2352_);
lean_dec_ref(v___x_2344_);
lean_dec_ref(v_arg_2343_);
lean_dec_ref(v_arg_2340_);
lean_dec_ref(v_arg_2337_);
lean_dec_ref(v_arg_2334_);
lean_dec_ref(v_arg_2331_);
v_isSharedCheck_2499_ = !lean_is_exclusive(v_a_2396_);
if (v_isSharedCheck_2499_ == 0)
{
lean_object* v_unused_2500_; lean_object* v_unused_2501_; 
v_unused_2500_ = lean_ctor_get(v_a_2396_, 1);
lean_dec(v_unused_2500_);
v_unused_2501_ = lean_ctor_get(v_a_2396_, 0);
lean_dec(v_unused_2501_);
v___x_2489_ = v_a_2396_;
v_isShared_2490_ = v_isSharedCheck_2499_;
goto v_resetjp_2488_;
}
else
{
lean_dec(v_a_2396_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2499_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2491_; lean_object* v___x_2493_; 
v___x_2491_ = lean_box(0);
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 1, v___x_2491_);
lean_ctor_set(v___x_2489_, 0, v_e_2310_);
v___x_2493_ = v___x_2489_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_e_2310_);
lean_ctor_set(v_reuseFailAlloc_2498_, 1, v___x_2491_);
v___x_2493_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
lean_object* v___x_2494_; lean_object* v___x_2496_; 
lean_ctor_set_uint8(v___x_2493_, sizeof(void*)*2, v___x_2346_);
v___x_2494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 0, v___x_2494_);
v___x_2496_ = v___x_2398_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v___x_2494_);
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
}
else
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2510_; 
lean_dec(v___x_2352_);
lean_dec_ref(v___x_2344_);
lean_dec_ref(v_arg_2343_);
lean_dec_ref(v_arg_2340_);
lean_dec_ref(v_arg_2337_);
lean_dec_ref(v_arg_2334_);
lean_dec_ref(v_arg_2331_);
lean_dec_ref(v_e_2310_);
v_a_2503_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2505_ = v___x_2395_;
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___x_2395_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_a_2503_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
}
}
else
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2519_; 
lean_dec(v___x_2352_);
lean_dec_ref(v___x_2344_);
lean_dec_ref(v_arg_2343_);
lean_dec_ref(v_arg_2340_);
lean_dec_ref(v_arg_2337_);
lean_dec_ref(v_arg_2334_);
lean_dec_ref(v_arg_2331_);
lean_dec_ref(v_e_2310_);
v_a_2512_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2514_ = v___x_2372_;
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2372_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2517_; 
if (v_isShared_2515_ == 0)
{
v___x_2517_ = v___x_2514_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2512_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
}
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
lean_dec_ref(v___x_2344_);
lean_dec_ref(v_arg_2343_);
lean_dec_ref(v_arg_2340_);
lean_dec_ref(v_arg_2337_);
lean_dec_ref(v_arg_2334_);
lean_dec_ref(v_arg_2331_);
lean_dec_ref(v_e_2310_);
v_a_2521_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2523_ = v___x_2347_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2347_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2524_ == 0)
{
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_a_2521_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
}
}
}
}
}
v___jp_2324_:
{
lean_object* v___x_2325_; lean_object* v___x_2327_; 
v___x_2325_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__0));
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 0, v___x_2325_);
v___x_2327_ = v___x_2322_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2325_);
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
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2537_; 
lean_dec_ref(v_e_2310_);
v_a_2530_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2532_ = v___x_2319_;
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2319_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2535_; 
if (v_isShared_2533_ == 0)
{
v___x_2535_ = v___x_2532_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2530_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___boxed(lean_object* v_numIndices_2538_, lean_object* v_useDecideBool_2539_, lean_object* v_e_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_){
_start:
{
uint8_t v_useDecideBool_boxed_2549_; lean_object* v_res_2550_; 
v_useDecideBool_boxed_2549_ = lean_unbox(v_useDecideBool_2539_);
v_res_2550_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27(v_numIndices_2538_, v_useDecideBool_boxed_2549_, v_e_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
lean_dec(v_a_2547_);
lean_dec_ref(v_a_2546_);
lean_dec(v_a_2545_);
lean_dec_ref(v_a_2544_);
lean_dec(v_a_2543_);
lean_dec_ref(v_a_2542_);
lean_dec(v_a_2541_);
lean_dec(v_numIndices_2538_);
return v_res_2550_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0(void){
_start:
{
lean_object* v___x_2551_; 
v___x_2551_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_2551_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1(void){
_start:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v_s_2554_; 
v___x_2552_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__2, &l_Lean_Meta_SplitIf_getSimpContext___closed__2_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__2);
v___x_2553_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0);
v_s_2554_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_s_2554_, 0, v___x_2553_);
lean_ctor_set(v_s_2554_, 1, v___x_2553_);
lean_ctor_set(v_s_2554_, 2, v___x_2552_);
lean_ctor_set(v_s_2554_, 3, v___x_2552_);
return v_s_2554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(lean_object* v_numIndices_2618_, uint8_t v_useDecide_2619_){
_start:
{
lean_object* v_s_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; uint8_t v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v_s_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v_s_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v_s_2621_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1);
v___x_2622_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__3));
v___x_2623_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__16));
v___x_2624_ = 0;
v___x_2625_ = lean_box(v_useDecide_2619_);
lean_inc(v_numIndices_2618_);
v___x_2626_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___boxed), 11, 2);
lean_closure_set(v___x_2626_, 0, v_numIndices_2618_);
lean_closure_set(v___x_2626_, 1, v___x_2625_);
v___x_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2626_);
v_s_2628_ = l_Lean_Meta_Simp_Simprocs_addCore(v_s_2621_, v___x_2622_, v___x_2623_, v___x_2624_, v___x_2627_);
v___x_2629_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__18));
v___x_2630_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__20));
v___x_2631_ = lean_box(v_useDecide_2619_);
v___x_2632_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___boxed), 11, 2);
lean_closure_set(v___x_2632_, 0, v_numIndices_2618_);
lean_closure_set(v___x_2632_, 1, v___x_2631_);
v___x_2633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2632_);
v_s_2634_ = l_Lean_Meta_Simp_Simprocs_addCore(v_s_2628_, v___x_2629_, v___x_2630_, v___x_2624_, v___x_2633_);
v___x_2635_ = lean_unsigned_to_nat(1u);
v___x_2636_ = lean_mk_empty_array_with_capacity(v___x_2635_);
v___x_2637_ = lean_array_push(v___x_2636_, v_s_2634_);
v___x_2638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2637_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___boxed(lean_object* v_numIndices_2639_, lean_object* v_useDecide_2640_, lean_object* v_a_2641_){
_start:
{
uint8_t v_useDecide_boxed_2642_; lean_object* v_res_2643_; 
v_useDecide_boxed_2642_ = lean_unbox(v_useDecide_2640_);
v_res_2643_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_numIndices_2639_, v_useDecide_boxed_2642_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs(lean_object* v_numIndices_2644_, uint8_t v_useDecide_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_){
_start:
{
lean_object* v___x_2651_; 
v___x_2651_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_numIndices_2644_, v_useDecide_2645_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___boxed(lean_object* v_numIndices_2652_, lean_object* v_useDecide_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
uint8_t v_useDecide_boxed_2659_; lean_object* v_res_2660_; 
v_useDecide_boxed_2659_ = lean_unbox(v_useDecide_2653_);
v_res_2660_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs(v_numIndices_2652_, v_useDecide_boxed_2659_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(uint8_t v_useDecide_2661_, lean_object* v_a_2662_){
_start:
{
lean_object* v_lctx_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
v_lctx_2664_ = lean_ctor_get(v_a_2662_, 2);
lean_inc_ref(v_lctx_2664_);
v___x_2665_ = lean_local_ctx_num_indices(v_lctx_2664_);
v___x_2666_ = lean_box(v_useDecide_2661_);
v___x_2667_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___boxed), 11, 2);
lean_closure_set(v___x_2667_, 0, v___x_2665_);
lean_closure_set(v___x_2667_, 1, v___x_2666_);
v___x_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2667_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg___boxed(lean_object* v_useDecide_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_){
_start:
{
uint8_t v_useDecide_boxed_2672_; lean_object* v_res_2673_; 
v_useDecide_boxed_2672_ = lean_unbox(v_useDecide_2669_);
v_res_2673_ = l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(v_useDecide_boxed_2672_, v_a_2670_);
lean_dec_ref(v_a_2670_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f(uint8_t v_useDecide_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_){
_start:
{
lean_object* v___x_2680_; 
v___x_2680_ = l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(v_useDecide_2674_, v_a_2675_);
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed(lean_object* v_useDecide_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_){
_start:
{
uint8_t v_useDecide_boxed_2687_; lean_object* v_res_2688_; 
v_useDecide_boxed_2687_ = lean_unbox(v_useDecide_2681_);
v_res_2688_ = l_Lean_Meta_SplitIf_mkDischarge_x3f(v_useDecide_boxed_2687_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_);
lean_dec(v_a_2685_);
lean_dec_ref(v_a_2684_);
lean_dec(v_a_2683_);
lean_dec_ref(v_a_2682_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(lean_object* v_mvarId_2689_, lean_object* v_x_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
lean_object* v___x_2696_; 
v___x_2696_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2689_, v_x_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2704_; 
v_a_2697_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2699_ = v___x_2696_;
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2696_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2702_; 
if (v_isShared_2700_ == 0)
{
v___x_2702_ = v___x_2699_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2697_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
else
{
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2712_; 
v_a_2705_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2707_ = v___x_2696_;
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___x_2696_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2710_; 
if (v_isShared_2708_ == 0)
{
v___x_2710_ = v___x_2707_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_a_2705_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_2713_, lean_object* v_x_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2713_, v_x_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0(lean_object* v_00_u03b1_2721_, lean_object* v_mvarId_2722_, lean_object* v_x_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2722_, v_x_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___boxed(lean_object* v_00_u03b1_2730_, lean_object* v_mvarId_2731_, lean_object* v_x_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0(v_00_u03b1_2730_, v_mvarId_2731_, v_x_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
return v_res_2738_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___x_2740_ = ((lean_object*)(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__0));
v___x_2741_ = l_Lean_stringToMessageData(v___x_2740_);
return v___x_2741_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2743_ = ((lean_object*)(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__2));
v___x_2744_ = l_Lean_stringToMessageData(v___x_2743_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0(lean_object* v_e_2745_, lean_object* v_mvarId_2746_, lean_object* v_hName_x3f_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v___x_2756_; lean_object* v_a_2757_; lean_object* v___x_2758_; 
v___x_2756_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_2745_, v___y_2749_);
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc_n(v_a_2757_, 2);
lean_dec_ref(v___x_2756_);
v___x_2758_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(v_a_2757_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; 
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_a_2759_);
lean_dec_ref(v___x_2758_);
if (lean_obj_tag(v_a_2759_) == 1)
{
lean_object* v_val_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2834_; 
lean_dec(v_a_2757_);
v_val_2760_ = lean_ctor_get(v_a_2759_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v_a_2759_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2762_ = v_a_2759_;
v_isShared_2763_ = v_isSharedCheck_2834_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_val_2760_);
lean_dec(v_a_2759_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2834_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v_fst_2764_; lean_object* v_snd_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2833_; 
v_fst_2764_ = lean_ctor_get(v_val_2760_, 0);
v_snd_2765_ = lean_ctor_get(v_val_2760_, 1);
v_isSharedCheck_2833_ = !lean_is_exclusive(v_val_2760_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2767_ = v_val_2760_;
v_isShared_2768_ = v_isSharedCheck_2833_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_snd_2765_);
lean_inc(v_fst_2764_);
lean_dec(v_val_2760_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2833_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v_hName_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; 
if (lean_obj_tag(v_hName_x3f_2747_) == 0)
{
lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2821_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__1));
v___x_2822_ = l_Lean_Core_mkFreshUserName(v___x_2821_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2823_);
lean_dec_ref(v___x_2822_);
v_hName_2796_ = v_a_2823_;
v___y_2797_ = v___y_2748_;
v___y_2798_ = v___y_2749_;
v___y_2799_ = v___y_2750_;
v___y_2800_ = v___y_2751_;
goto v___jp_2795_;
}
else
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2831_; 
lean_del_object(v___x_2767_);
lean_dec(v_snd_2765_);
lean_dec(v_fst_2764_);
lean_del_object(v___x_2762_);
lean_dec(v_mvarId_2746_);
v_a_2824_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2826_ = v___x_2822_;
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2822_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2829_; 
if (v_isShared_2827_ == 0)
{
v___x_2829_ = v___x_2826_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2824_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
}
else
{
lean_object* v_val_2832_; 
v_val_2832_ = lean_ctor_get(v_hName_x3f_2747_, 0);
lean_inc(v_val_2832_);
lean_dec_ref(v_hName_x3f_2747_);
v_hName_2796_ = v_val_2832_;
v___y_2797_ = v___y_2748_;
v___y_2798_ = v___y_2749_;
v___y_2799_ = v___y_2750_;
v___y_2800_ = v___y_2751_;
goto v___jp_2795_;
}
v___jp_2769_:
{
lean_object* v___x_2775_; 
v___x_2775_ = l_Lean_MVarId_byCasesDec(v_mvarId_2746_, v_fst_2764_, v_snd_2765_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2786_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2778_ = v___x_2775_;
v_isShared_2779_ = v_isSharedCheck_2786_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2775_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2786_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 0, v_a_2776_);
v___x_2781_ = v___x_2762_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2776_);
v___x_2781_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
lean_object* v___x_2783_; 
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 0, v___x_2781_);
v___x_2783_ = v___x_2778_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v___x_2781_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
else
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
lean_del_object(v___x_2762_);
v_a_2787_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v___x_2775_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___x_2775_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
v___jp_2795_:
{
lean_object* v_options_2801_; uint8_t v_hasTrace_2802_; 
v_options_2801_ = lean_ctor_get(v___y_2799_, 2);
v_hasTrace_2802_ = lean_ctor_get_uint8(v_options_2801_, sizeof(void*)*1);
if (v_hasTrace_2802_ == 0)
{
lean_del_object(v___x_2767_);
v___y_2770_ = v_hName_2796_;
v___y_2771_ = v___y_2797_;
v___y_2772_ = v___y_2798_;
v___y_2773_ = v___y_2799_;
v___y_2774_ = v___y_2800_;
goto v___jp_2769_;
}
else
{
lean_object* v_inheritedTraceOptions_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; uint8_t v___x_2806_; 
v_inheritedTraceOptions_2803_ = lean_ctor_get(v___y_2799_, 13);
v___x_2804_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10));
v___x_2805_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11);
v___x_2806_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2803_, v_options_2801_, v___x_2805_);
if (v___x_2806_ == 0)
{
lean_del_object(v___x_2767_);
v___y_2770_ = v_hName_2796_;
v___y_2771_ = v___y_2797_;
v___y_2772_ = v___y_2798_;
v___y_2773_ = v___y_2799_;
v___y_2774_ = v___y_2800_;
goto v___jp_2769_;
}
else
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2810_; 
v___x_2807_ = lean_obj_once(&l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1, &l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1_once, _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1);
lean_inc(v_snd_2765_);
v___x_2808_ = l_Lean_MessageData_ofExpr(v_snd_2765_);
if (v_isShared_2768_ == 0)
{
lean_ctor_set_tag(v___x_2767_, 7);
lean_ctor_set(v___x_2767_, 1, v___x_2808_);
lean_ctor_set(v___x_2767_, 0, v___x_2807_);
v___x_2810_ = v___x_2767_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v___x_2807_);
lean_ctor_set(v_reuseFailAlloc_2820_, 1, v___x_2808_);
v___x_2810_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
lean_object* v___x_2811_; 
v___x_2811_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_2804_, v___x_2810_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_dec_ref(v___x_2811_);
v___y_2770_ = v_hName_2796_;
v___y_2771_ = v___y_2797_;
v___y_2772_ = v___y_2798_;
v___y_2773_ = v___y_2799_;
v___y_2774_ = v___y_2800_;
goto v___jp_2769_;
}
else
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
lean_dec(v_hName_2796_);
lean_dec(v_snd_2765_);
lean_dec(v_fst_2764_);
lean_del_object(v___x_2762_);
lean_dec(v_mvarId_2746_);
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2811_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2811_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2817_; 
if (v_isShared_2815_ == 0)
{
v___x_2817_ = v___x_2814_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2812_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
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
lean_object* v_options_2835_; uint8_t v_hasTrace_2836_; 
lean_dec(v_a_2759_);
lean_dec(v_hName_x3f_2747_);
lean_dec(v_mvarId_2746_);
v_options_2835_ = lean_ctor_get(v___y_2750_, 2);
v_hasTrace_2836_ = lean_ctor_get_uint8(v_options_2835_, sizeof(void*)*1);
if (v_hasTrace_2836_ == 0)
{
lean_dec(v_a_2757_);
goto v___jp_2753_;
}
else
{
lean_object* v_inheritedTraceOptions_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; uint8_t v___x_2840_; 
v_inheritedTraceOptions_2837_ = lean_ctor_get(v___y_2750_, 13);
v___x_2838_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10));
v___x_2839_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11);
v___x_2840_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2837_, v_options_2835_, v___x_2839_);
if (v___x_2840_ == 0)
{
lean_dec(v_a_2757_);
goto v___jp_2753_;
}
else
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2841_ = lean_obj_once(&l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3, &l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3_once, _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3);
v___x_2842_ = l_Lean_indentExpr(v_a_2757_);
v___x_2843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2841_);
lean_ctor_set(v___x_2843_, 1, v___x_2842_);
v___x_2844_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_2838_, v___x_2843_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_dec_ref(v___x_2844_);
goto v___jp_2753_;
}
else
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2844_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2844_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2845_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2860_; 
lean_dec(v_a_2757_);
lean_dec(v_hName_x3f_2747_);
lean_dec(v_mvarId_2746_);
v_a_2853_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2855_ = v___x_2758_;
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2758_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2858_; 
if (v_isShared_2856_ == 0)
{
v___x_2858_ = v___x_2855_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2853_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
v___jp_2753_:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2754_ = lean_box(0);
v___x_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2754_);
return v___x_2755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___boxed(lean_object* v_e_2861_, lean_object* v_mvarId_2862_, lean_object* v_hName_x3f_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0(v_e_2861_, v_mvarId_2862_, v_hName_x3f_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f(lean_object* v_mvarId_2870_, lean_object* v_e_2871_, lean_object* v_hName_x3f_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_){
_start:
{
lean_object* v___f_2878_; lean_object* v___x_2879_; 
lean_inc(v_mvarId_2870_);
v___f_2878_ = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2878_, 0, v_e_2871_);
lean_closure_set(v___f_2878_, 1, v_mvarId_2870_);
lean_closure_set(v___f_2878_, 2, v_hName_x3f_2872_);
v___x_2879_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2870_, v___f_2878_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___boxed(lean_object* v_mvarId_2880_, lean_object* v_e_2881_, lean_object* v_hName_x3f_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(v_mvarId_2880_, v_e_2881_, v_hName_x3f_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_);
lean_dec(v_a_2886_);
lean_dec_ref(v_a_2885_);
lean_dec(v_a_2884_);
lean_dec_ref(v_a_2883_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0(lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
lean_object* v_lctx_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v_lctx_2894_ = lean_ctor_get(v___y_2889_, 2);
lean_inc_ref(v_lctx_2894_);
lean_dec_ref(v___y_2889_);
v___x_2895_ = lean_local_ctx_num_indices(v_lctx_2894_);
v___x_2896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2895_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0___boxed(lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0(v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
lean_dec(v___y_2900_);
lean_dec_ref(v___y_2899_);
lean_dec(v___y_2898_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(lean_object* v_mvarId_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_){
_start:
{
lean_object* v___f_2910_; lean_object* v___x_2911_; 
v___f_2910_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___closed__0));
v___x_2911_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2904_, v___f_2910_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___boxed(lean_object* v_mvarId_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(v_mvarId_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_);
lean_dec(v_a_2916_);
lean_dec_ref(v_a_2915_);
lean_dec(v_a_2914_);
lean_dec_ref(v_a_2913_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_simpIfTarget_spec__0(lean_object* v_msg_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
lean_object* v___f_2926_; lean_object* v___x_1955__overap_2927_; lean_object* v___x_2928_; 
v___f_2926_ = ((lean_object*)(l_panic___at___00Lean_Meta_simpIfTarget_spec__0___closed__0));
v___x_1955__overap_2927_ = lean_panic_fn_borrowed(v___f_2926_, v_msg_2920_);
lean_inc(v___y_2924_);
lean_inc_ref(v___y_2923_);
lean_inc(v___y_2922_);
lean_inc_ref(v___y_2921_);
v___x_2928_ = lean_apply_5(v___x_1955__overap_2927_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, lean_box(0));
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_simpIfTarget_spec__0___boxed(lean_object* v_msg_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v_msg_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
return v_res_2935_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(lean_object* v_opts_2936_, lean_object* v_opt_2937_){
_start:
{
lean_object* v_name_2938_; lean_object* v_defValue_2939_; lean_object* v_map_2940_; lean_object* v___x_2941_; 
v_name_2938_ = lean_ctor_get(v_opt_2937_, 0);
v_defValue_2939_ = lean_ctor_get(v_opt_2937_, 1);
v_map_2940_ = lean_ctor_get(v_opts_2936_, 0);
v___x_2941_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2940_, v_name_2938_);
if (lean_obj_tag(v___x_2941_) == 0)
{
uint8_t v___x_2942_; 
v___x_2942_ = lean_unbox(v_defValue_2939_);
return v___x_2942_;
}
else
{
lean_object* v_val_2943_; 
v_val_2943_ = lean_ctor_get(v___x_2941_, 0);
lean_inc(v_val_2943_);
lean_dec_ref(v___x_2941_);
if (lean_obj_tag(v_val_2943_) == 1)
{
uint8_t v_v_2944_; 
v_v_2944_ = lean_ctor_get_uint8(v_val_2943_, 0);
lean_dec_ref(v_val_2943_);
return v_v_2944_;
}
else
{
uint8_t v___x_2945_; 
lean_dec(v_val_2943_);
v___x_2945_ = lean_unbox(v_defValue_2939_);
return v___x_2945_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1___boxed(lean_object* v_opts_2946_, lean_object* v_opt_2947_){
_start:
{
uint8_t v_res_2948_; lean_object* v_r_2949_; 
v_res_2948_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v_opts_2946_, v_opt_2947_);
lean_dec_ref(v_opt_2947_);
lean_dec_ref(v_opts_2946_);
v_r_2949_ = lean_box(v_res_2948_);
return v_r_2949_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__0(void){
_start:
{
lean_object* v___x_2950_; 
v___x_2950_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2950_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__1(void){
_start:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2951_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__0, &l_Lean_Meta_simpIfTarget___closed__0_once, _init_l_Lean_Meta_simpIfTarget___closed__0);
v___x_2952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2951_);
return v___x_2952_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__2(void){
_start:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2953_ = lean_unsigned_to_nat(0u);
v___x_2954_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__1, &l_Lean_Meta_simpIfTarget___closed__1_once, _init_l_Lean_Meta_simpIfTarget___closed__1);
v___x_2955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2954_);
lean_ctor_set(v___x_2955_, 1, v___x_2953_);
return v___x_2955_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__3(void){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2956_ = lean_unsigned_to_nat(32u);
v___x_2957_ = lean_mk_empty_array_with_capacity(v___x_2956_);
v___x_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2957_);
return v___x_2958_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__4(void){
_start:
{
size_t v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2959_ = ((size_t)5ULL);
v___x_2960_ = lean_unsigned_to_nat(0u);
v___x_2961_ = lean_unsigned_to_nat(32u);
v___x_2962_ = lean_mk_empty_array_with_capacity(v___x_2961_);
v___x_2963_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__3, &l_Lean_Meta_simpIfTarget___closed__3_once, _init_l_Lean_Meta_simpIfTarget___closed__3);
v___x_2964_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2964_, 0, v___x_2963_);
lean_ctor_set(v___x_2964_, 1, v___x_2962_);
lean_ctor_set(v___x_2964_, 2, v___x_2960_);
lean_ctor_set(v___x_2964_, 3, v___x_2960_);
lean_ctor_set_usize(v___x_2964_, 4, v___x_2959_);
return v___x_2964_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__5(void){
_start:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2965_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__4, &l_Lean_Meta_simpIfTarget___closed__4_once, _init_l_Lean_Meta_simpIfTarget___closed__4);
v___x_2966_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__1, &l_Lean_Meta_simpIfTarget___closed__1_once, _init_l_Lean_Meta_simpIfTarget___closed__1);
v___x_2967_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2966_);
lean_ctor_set(v___x_2967_, 1, v___x_2966_);
lean_ctor_set(v___x_2967_, 2, v___x_2966_);
lean_ctor_set(v___x_2967_, 3, v___x_2965_);
return v___x_2967_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__6(void){
_start:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2968_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__5, &l_Lean_Meta_simpIfTarget___closed__5_once, _init_l_Lean_Meta_simpIfTarget___closed__5);
v___x_2969_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__2, &l_Lean_Meta_simpIfTarget___closed__2_once, _init_l_Lean_Meta_simpIfTarget___closed__2);
v___x_2970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2969_);
lean_ctor_set(v___x_2970_, 1, v___x_2968_);
return v___x_2970_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__10(void){
_start:
{
lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2974_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__9));
v___x_2975_ = lean_unsigned_to_nat(78u);
v___x_2976_ = lean_unsigned_to_nat(289u);
v___x_2977_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__8));
v___x_2978_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_2979_ = l_mkPanicMessageWithDecl(v___x_2978_, v___x_2977_, v___x_2976_, v___x_2975_, v___x_2974_);
return v___x_2979_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__12(void){
_start:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2982_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__9));
v___x_2983_ = lean_unsigned_to_nat(128u);
v___x_2984_ = lean_unsigned_to_nat(293u);
v___x_2985_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__8));
v___x_2986_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_2987_ = l_mkPanicMessageWithDecl(v___x_2986_, v___x_2985_, v___x_2984_, v___x_2983_, v___x_2982_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfTarget(lean_object* v_mvarId_2988_, uint8_t v_useDecide_2989_, uint8_t v_useNewSemantics_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_){
_start:
{
if (v_useNewSemantics_2990_ == 0)
{
lean_object* v_options_3043_; lean_object* v___x_3044_; uint8_t v___x_3045_; 
v_options_3043_ = lean_ctor_get(v_a_2993_, 2);
v___x_3044_ = l_Lean_Meta_backward_split;
v___x_3045_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v_options_3043_, v___x_3044_);
if (v___x_3045_ == 0)
{
goto v___jp_2996_;
}
else
{
lean_object* v___x_3046_; 
v___x_3046_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v_a_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
lean_inc(v_a_3047_);
lean_dec_ref(v___x_3046_);
v___x_3048_ = lean_box(v_useDecide_2989_);
v___x_3049_ = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed), 6, 1);
lean_closure_set(v___x_3049_, 0, v___x_3048_);
lean_inc(v_mvarId_2988_);
v___x_3050_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2988_, v___x_3049_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
lean_dec_ref(v___x_3050_);
v___x_3052_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__11));
v___x_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3053_, 0, v_a_3051_);
v___x_3054_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__6, &l_Lean_Meta_simpIfTarget___closed__6_once, _init_l_Lean_Meta_simpIfTarget___closed__6);
v___x_3055_ = l_Lean_Meta_simpTarget(v_mvarId_2988_, v_a_3047_, v___x_3052_, v___x_3053_, v_useNewSemantics_2990_, v___x_3054_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3067_; 
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3058_ = v___x_3055_;
v_isShared_3059_ = v_isSharedCheck_3067_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3055_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3067_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v_fst_3060_; 
v_fst_3060_ = lean_ctor_get(v_a_3056_, 0);
lean_inc(v_fst_3060_);
lean_dec(v_a_3056_);
if (lean_obj_tag(v_fst_3060_) == 1)
{
lean_object* v_val_3061_; lean_object* v___x_3063_; 
v_val_3061_ = lean_ctor_get(v_fst_3060_, 0);
lean_inc(v_val_3061_);
lean_dec_ref(v_fst_3060_);
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 0, v_val_3061_);
v___x_3063_ = v___x_3058_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_val_3061_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
else
{
lean_object* v___x_3065_; lean_object* v___x_3066_; 
lean_dec(v_fst_3060_);
lean_del_object(v___x_3058_);
v___x_3065_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__12, &l_Lean_Meta_simpIfTarget___closed__12_once, _init_l_Lean_Meta_simpIfTarget___closed__12);
v___x_3066_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3065_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
return v___x_3066_;
}
}
}
else
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
v_a_3068_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_3055_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_3055_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
else
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
lean_dec(v_a_3047_);
lean_dec(v_mvarId_2988_);
v_a_3076_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_3050_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3050_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec(v_mvarId_2988_);
v_a_3084_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3046_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3046_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
}
else
{
goto v___jp_2996_;
}
v___jp_2996_:
{
lean_object* v___x_2997_; 
v___x_2997_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_2991_, v_a_2993_, v_a_2994_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v___x_2999_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
lean_dec_ref(v___x_2997_);
lean_inc(v_mvarId_2988_);
v___x_2999_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(v_mvarId_2988_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; lean_object* v___x_3001_; lean_object* v_a_3002_; lean_object* v___x_3003_; uint8_t v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc(v_a_3000_);
lean_dec_ref(v___x_2999_);
v___x_3001_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_a_3000_, v_useDecide_2989_);
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_a_3002_);
lean_dec_ref(v___x_3001_);
v___x_3003_ = lean_box(0);
v___x_3004_ = 0;
v___x_3005_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__6, &l_Lean_Meta_simpIfTarget___closed__6_once, _init_l_Lean_Meta_simpIfTarget___closed__6);
v___x_3006_ = l_Lean_Meta_simpTarget(v_mvarId_2988_, v_a_2998_, v_a_3002_, v___x_3003_, v___x_3004_, v___x_3005_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3018_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3009_ = v___x_3006_;
v_isShared_3010_ = v_isSharedCheck_3018_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_3006_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3018_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v_fst_3011_; 
v_fst_3011_ = lean_ctor_get(v_a_3007_, 0);
lean_inc(v_fst_3011_);
lean_dec(v_a_3007_);
if (lean_obj_tag(v_fst_3011_) == 1)
{
lean_object* v_val_3012_; lean_object* v___x_3014_; 
v_val_3012_ = lean_ctor_get(v_fst_3011_, 0);
lean_inc(v_val_3012_);
lean_dec_ref(v_fst_3011_);
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 0, v_val_3012_);
v___x_3014_ = v___x_3009_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_val_3012_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
else
{
lean_object* v___x_3016_; lean_object* v___x_3017_; 
lean_dec(v_fst_3011_);
lean_del_object(v___x_3009_);
v___x_3016_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__10, &l_Lean_Meta_simpIfTarget___closed__10_once, _init_l_Lean_Meta_simpIfTarget___closed__10);
v___x_3017_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3016_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
return v___x_3017_;
}
}
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
v_a_3019_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_3006_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_3006_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_dec(v_a_2998_);
lean_dec(v_mvarId_2988_);
v_a_3027_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_2999_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_2999_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
else
{
lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3042_; 
lean_dec(v_mvarId_2988_);
v_a_3035_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3037_ = v___x_2997_;
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_2997_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3040_; 
if (v_isShared_3038_ == 0)
{
v___x_3040_ = v___x_3037_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfTarget___boxed(lean_object* v_mvarId_3092_, lean_object* v_useDecide_3093_, lean_object* v_useNewSemantics_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_){
_start:
{
uint8_t v_useDecide_boxed_3100_; uint8_t v_useNewSemantics_boxed_3101_; lean_object* v_res_3102_; 
v_useDecide_boxed_3100_ = lean_unbox(v_useDecide_3093_);
v_useNewSemantics_boxed_3101_ = lean_unbox(v_useNewSemantics_3094_);
v_res_3102_ = l_Lean_Meta_simpIfTarget(v_mvarId_3092_, v_useDecide_boxed_3100_, v_useNewSemantics_boxed_3101_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
lean_dec(v_a_3098_);
lean_dec_ref(v_a_3097_);
lean_dec(v_a_3096_);
lean_dec_ref(v_a_3095_);
return v_res_3102_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfLocalDecl___closed__1(void){
_start:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3104_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__9));
v___x_3105_ = lean_unsigned_to_nat(93u);
v___x_3106_ = lean_unsigned_to_nat(305u);
v___x_3107_ = ((lean_object*)(l_Lean_Meta_simpIfLocalDecl___closed__0));
v___x_3108_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_3109_ = l_mkPanicMessageWithDecl(v___x_3108_, v___x_3107_, v___x_3106_, v___x_3105_, v___x_3104_);
return v___x_3109_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfLocalDecl___closed__2(void){
_start:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3110_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__9));
v___x_3111_ = lean_unsigned_to_nat(133u);
v___x_3112_ = lean_unsigned_to_nat(309u);
v___x_3113_ = ((lean_object*)(l_Lean_Meta_simpIfLocalDecl___closed__0));
v___x_3114_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_3115_ = l_mkPanicMessageWithDecl(v___x_3114_, v___x_3113_, v___x_3112_, v___x_3111_, v___x_3110_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfLocalDecl(lean_object* v_mvarId_3116_, lean_object* v_fvarId_3117_, uint8_t v_useNewSemantics_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_){
_start:
{
if (v_useNewSemantics_3118_ == 0)
{
lean_object* v_options_3172_; lean_object* v___x_3173_; uint8_t v___x_3174_; 
v_options_3172_ = lean_ctor_get(v_a_3121_, 2);
v___x_3173_ = l_Lean_Meta_backward_split;
v___x_3174_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v_options_3172_, v___x_3173_);
if (v___x_3174_ == 0)
{
goto v___jp_3124_;
}
else
{
lean_object* v___x_3175_; 
v___x_3175_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_);
if (lean_obj_tag(v___x_3175_) == 0)
{
lean_object* v_a_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v_a_3176_ = lean_ctor_get(v___x_3175_, 0);
lean_inc(v_a_3176_);
lean_dec_ref(v___x_3175_);
v___x_3177_ = lean_box(v_useNewSemantics_3118_);
v___x_3178_ = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed), 6, 1);
lean_closure_set(v___x_3178_, 0, v___x_3177_);
lean_inc(v_mvarId_3116_);
v___x_3179_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_3116_, v___x_3178_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_object* v_a_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
lean_inc(v_a_3180_);
lean_dec_ref(v___x_3179_);
v___x_3181_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__11));
v___x_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3182_, 0, v_a_3180_);
v___x_3183_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__6, &l_Lean_Meta_simpIfTarget___closed__6_once, _init_l_Lean_Meta_simpIfTarget___closed__6);
v___x_3184_ = l_Lean_Meta_simpLocalDecl(v_mvarId_3116_, v_fvarId_3117_, v_a_3176_, v___x_3181_, v___x_3182_, v_useNewSemantics_3118_, v___x_3183_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3197_; 
v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3187_ = v___x_3184_;
v_isShared_3188_ = v_isSharedCheck_3197_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v___x_3184_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3197_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v_fst_3189_; 
v_fst_3189_ = lean_ctor_get(v_a_3185_, 0);
lean_inc(v_fst_3189_);
lean_dec(v_a_3185_);
if (lean_obj_tag(v_fst_3189_) == 1)
{
lean_object* v_val_3190_; lean_object* v_snd_3191_; lean_object* v___x_3193_; 
v_val_3190_ = lean_ctor_get(v_fst_3189_, 0);
lean_inc(v_val_3190_);
lean_dec_ref(v_fst_3189_);
v_snd_3191_ = lean_ctor_get(v_val_3190_, 1);
lean_inc(v_snd_3191_);
lean_dec(v_val_3190_);
if (v_isShared_3188_ == 0)
{
lean_ctor_set(v___x_3187_, 0, v_snd_3191_);
v___x_3193_ = v___x_3187_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_snd_3191_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
}
}
else
{
lean_object* v___x_3195_; lean_object* v___x_3196_; 
lean_dec(v_fst_3189_);
lean_del_object(v___x_3187_);
v___x_3195_ = lean_obj_once(&l_Lean_Meta_simpIfLocalDecl___closed__2, &l_Lean_Meta_simpIfLocalDecl___closed__2_once, _init_l_Lean_Meta_simpIfLocalDecl___closed__2);
v___x_3196_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3195_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_);
return v___x_3196_;
}
}
}
else
{
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
v_a_3198_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___x_3184_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3184_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
if (v_isShared_3201_ == 0)
{
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
else
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3213_; 
lean_dec(v_a_3176_);
lean_dec(v_fvarId_3117_);
lean_dec(v_mvarId_3116_);
v_a_3206_ = lean_ctor_get(v___x_3179_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3208_ = v___x_3179_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3179_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3211_; 
if (v_isShared_3209_ == 0)
{
v___x_3211_ = v___x_3208_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_a_3206_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
}
else
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3221_; 
lean_dec(v_fvarId_3117_);
lean_dec(v_mvarId_3116_);
v_a_3214_ = lean_ctor_get(v___x_3175_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3216_ = v___x_3175_;
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_3175_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3219_; 
if (v_isShared_3217_ == 0)
{
v___x_3219_ = v___x_3216_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_a_3214_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
}
else
{
goto v___jp_3124_;
}
v___jp_3124_:
{
lean_object* v___x_3125_; 
v___x_3125_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_3119_, v_a_3121_, v_a_3122_);
if (lean_obj_tag(v___x_3125_) == 0)
{
lean_object* v_a_3126_; lean_object* v___x_3127_; 
v_a_3126_ = lean_ctor_get(v___x_3125_, 0);
lean_inc(v_a_3126_);
lean_dec_ref(v___x_3125_);
lean_inc(v_mvarId_3116_);
v___x_3127_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(v_mvarId_3116_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; uint8_t v___x_3129_; lean_object* v___x_3130_; lean_object* v_a_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
lean_inc(v_a_3128_);
lean_dec_ref(v___x_3127_);
v___x_3129_ = 0;
v___x_3130_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_a_3128_, v___x_3129_);
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
lean_inc(v_a_3131_);
lean_dec_ref(v___x_3130_);
v___x_3132_ = lean_box(0);
v___x_3133_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__6, &l_Lean_Meta_simpIfTarget___closed__6_once, _init_l_Lean_Meta_simpIfTarget___closed__6);
v___x_3134_ = l_Lean_Meta_simpLocalDecl(v_mvarId_3116_, v_fvarId_3117_, v_a_3126_, v_a_3131_, v___x_3132_, v___x_3129_, v___x_3133_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v_a_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3147_; 
v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3137_ = v___x_3134_;
v_isShared_3138_ = v_isSharedCheck_3147_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_a_3135_);
lean_dec(v___x_3134_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3147_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v_fst_3139_; 
v_fst_3139_ = lean_ctor_get(v_a_3135_, 0);
lean_inc(v_fst_3139_);
lean_dec(v_a_3135_);
if (lean_obj_tag(v_fst_3139_) == 1)
{
lean_object* v_val_3140_; lean_object* v_snd_3141_; lean_object* v___x_3143_; 
v_val_3140_ = lean_ctor_get(v_fst_3139_, 0);
lean_inc(v_val_3140_);
lean_dec_ref(v_fst_3139_);
v_snd_3141_ = lean_ctor_get(v_val_3140_, 1);
lean_inc(v_snd_3141_);
lean_dec(v_val_3140_);
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 0, v_snd_3141_);
v___x_3143_ = v___x_3137_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_snd_3141_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
else
{
lean_object* v___x_3145_; lean_object* v___x_3146_; 
lean_dec(v_fst_3139_);
lean_del_object(v___x_3137_);
v___x_3145_ = lean_obj_once(&l_Lean_Meta_simpIfLocalDecl___closed__1, &l_Lean_Meta_simpIfLocalDecl___closed__1_once, _init_l_Lean_Meta_simpIfLocalDecl___closed__1);
v___x_3146_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3145_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_);
return v___x_3146_;
}
}
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
v_a_3148_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_3134_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3134_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3153_; 
if (v_isShared_3151_ == 0)
{
v___x_3153_ = v___x_3150_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3148_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
else
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_dec(v_a_3126_);
lean_dec(v_fvarId_3117_);
lean_dec(v_mvarId_3116_);
v_a_3156_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3127_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3127_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
else
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
lean_dec(v_fvarId_3117_);
lean_dec(v_mvarId_3116_);
v_a_3164_ = lean_ctor_get(v___x_3125_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___x_3125_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3125_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfLocalDecl___boxed(lean_object* v_mvarId_3222_, lean_object* v_fvarId_3223_, lean_object* v_useNewSemantics_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_){
_start:
{
uint8_t v_useNewSemantics_boxed_3230_; lean_object* v_res_3231_; 
v_useNewSemantics_boxed_3230_ = lean_unbox(v_useNewSemantics_3224_);
v_res_3231_ = l_Lean_Meta_simpIfLocalDecl(v_mvarId_3222_, v_fvarId_3223_, v_useNewSemantics_boxed_3230_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_);
lean_dec(v_a_3228_);
lean_dec_ref(v_a_3227_);
lean_dec(v_a_3226_);
lean_dec_ref(v_a_3225_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(lean_object* v_x_x3f_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
lean_object* v___x_3238_; 
v___x_3238_ = l_Lean_Meta_saveState___redArg(v___y_3234_, v___y_3236_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v_a_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3283_; 
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3241_ = v___x_3238_;
v_isShared_3242_ = v_isSharedCheck_3283_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_a_3239_);
lean_dec(v___x_3238_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3283_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___y_3244_; uint8_t v___y_3245_; lean_object* v_a_3267_; lean_object* v___x_3270_; 
lean_inc(v___y_3236_);
lean_inc_ref(v___y_3235_);
lean_inc(v___y_3234_);
lean_inc_ref(v___y_3233_);
v___x_3270_ = lean_apply_5(v_x_x3f_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, lean_box(0));
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3271_);
if (lean_obj_tag(v_a_3271_) == 0)
{
lean_object* v___x_3272_; 
lean_dec_ref(v___x_3270_);
v___x_3272_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3239_, v___y_3234_, v___y_3236_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3279_; 
lean_del_object(v___x_3241_);
lean_dec(v_a_3239_);
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3279_ == 0)
{
lean_object* v_unused_3280_; 
v_unused_3280_ = lean_ctor_get(v___x_3272_, 0);
lean_dec(v_unused_3280_);
v___x_3274_ = v___x_3272_;
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
else
{
lean_dec(v___x_3272_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3277_; 
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v_a_3271_);
v___x_3277_ = v___x_3274_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_a_3271_);
v___x_3277_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
return v___x_3277_;
}
}
}
else
{
lean_object* v_a_3281_; 
v_a_3281_ = lean_ctor_get(v___x_3272_, 0);
lean_inc(v_a_3281_);
lean_dec_ref(v___x_3272_);
v_a_3267_ = v_a_3281_;
goto v___jp_3266_;
}
}
else
{
lean_dec_ref(v_a_3271_);
lean_del_object(v___x_3241_);
lean_dec(v_a_3239_);
return v___x_3270_;
}
}
else
{
lean_object* v_a_3282_; 
v_a_3282_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3282_);
lean_dec_ref(v___x_3270_);
v_a_3267_ = v_a_3282_;
goto v___jp_3266_;
}
v___jp_3243_:
{
if (v___y_3245_ == 0)
{
lean_object* v___x_3246_; 
lean_del_object(v___x_3241_);
v___x_3246_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3239_, v___y_3234_, v___y_3236_);
lean_dec(v_a_3239_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3253_; 
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3253_ == 0)
{
lean_object* v_unused_3254_; 
v_unused_3254_ = lean_ctor_get(v___x_3246_, 0);
lean_dec(v_unused_3254_);
v___x_3248_ = v___x_3246_;
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
else
{
lean_dec(v___x_3246_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3251_; 
if (v_isShared_3249_ == 0)
{
lean_ctor_set_tag(v___x_3248_, 1);
lean_ctor_set(v___x_3248_, 0, v___y_3244_);
v___x_3251_ = v___x_3248_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v___y_3244_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
}
else
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3262_; 
lean_dec_ref(v___y_3244_);
v_a_3255_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3257_ = v___x_3246_;
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3246_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3258_ == 0)
{
v___x_3260_ = v___x_3257_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3255_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
else
{
lean_object* v___x_3264_; 
lean_dec(v_a_3239_);
if (v_isShared_3242_ == 0)
{
lean_ctor_set_tag(v___x_3241_, 1);
lean_ctor_set(v___x_3241_, 0, v___y_3244_);
v___x_3264_ = v___x_3241_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v___y_3244_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
v___jp_3266_:
{
uint8_t v___x_3268_; 
v___x_3268_ = l_Lean_Exception_isInterrupt(v_a_3267_);
if (v___x_3268_ == 0)
{
uint8_t v___x_3269_; 
lean_inc_ref(v_a_3267_);
v___x_3269_ = l_Lean_Exception_isRuntime(v_a_3267_);
v___y_3244_ = v_a_3267_;
v___y_3245_ = v___x_3269_;
goto v___jp_3243_;
}
else
{
v___y_3244_ = v_a_3267_;
v___y_3245_ = v___x_3268_;
goto v___jp_3243_;
}
}
}
}
else
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3291_; 
lean_dec_ref(v_x_x3f_3232_);
v_a_3284_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3286_ = v___x_3238_;
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___x_3238_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3289_; 
if (v_isShared_3287_ == 0)
{
v___x_3289_ = v___x_3286_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_a_3284_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg___boxed(lean_object* v_x_x3f_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v_x_x3f_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0(lean_object* v_00_u03b1_3299_, lean_object* v_x_x3f_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_){
_start:
{
lean_object* v___x_3306_; 
v___x_3306_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v_x_x3f_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___boxed(lean_object* v_00_u03b1_3307_, lean_object* v_x_x3f_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0(v_00_u03b1_3307_, v_x_x3f_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3309_);
return v_res_3314_;
}
}
static lean_object* _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v___x_3319_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1));
v___x_3320_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4));
v___x_3321_ = l_Lean_Name_append(v___x_3320_, v___x_3319_);
return v___x_3321_;
}
}
static lean_object* _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3323_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__3));
v___x_3324_ = l_Lean_stringToMessageData(v___x_3323_);
return v___x_3324_;
}
}
static lean_object* _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3326_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__5));
v___x_3327_ = l_Lean_stringToMessageData(v___x_3326_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0(lean_object* v_mvarId_3328_, lean_object* v_hName_x3f_3329_, uint8_t v_useNewSemantics_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
lean_object* v___x_3339_; 
lean_inc(v_mvarId_3328_);
v___x_3339_ = l_Lean_MVarId_getType(v_mvarId_3328_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v_a_3340_; lean_object* v___x_3341_; 
v_a_3340_ = lean_ctor_get(v___x_3339_, 0);
lean_inc(v_a_3340_);
lean_dec_ref(v___x_3339_);
v___x_3341_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(v_mvarId_3328_, v_a_3340_, v_hName_x3f_3329_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3438_; 
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3344_ = v___x_3341_;
v_isShared_3345_ = v_isSharedCheck_3438_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_a_3342_);
lean_dec(v___x_3341_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3438_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
if (lean_obj_tag(v_a_3342_) == 1)
{
lean_object* v_val_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3433_; 
lean_del_object(v___x_3344_);
v_val_3346_ = lean_ctor_get(v_a_3342_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v_a_3342_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3348_ = v_a_3342_;
v_isShared_3349_ = v_isSharedCheck_3433_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_val_3346_);
lean_dec(v_a_3342_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3433_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v_fst_3350_; lean_object* v_snd_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3432_; 
v_fst_3350_ = lean_ctor_get(v_val_3346_, 0);
v_snd_3351_ = lean_ctor_get(v_val_3346_, 1);
v_isSharedCheck_3432_ = !lean_is_exclusive(v_val_3346_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3353_ = v_val_3346_;
v_isShared_3354_ = v_isSharedCheck_3432_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_snd_3351_);
lean_inc(v_fst_3350_);
lean_dec(v_val_3346_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3432_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v_mvarId_3355_; lean_object* v_fvarId_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3431_; 
v_mvarId_3355_ = lean_ctor_get(v_fst_3350_, 0);
v_fvarId_3356_ = lean_ctor_get(v_fst_3350_, 1);
v_isSharedCheck_3431_ = !lean_is_exclusive(v_fst_3350_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3358_ = v_fst_3350_;
v_isShared_3359_ = v_isSharedCheck_3431_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_fvarId_3356_);
lean_inc(v_mvarId_3355_);
lean_dec(v_fst_3350_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3431_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
uint8_t v___x_3360_; lean_object* v___x_3361_; 
v___x_3360_ = 0;
lean_inc(v_mvarId_3355_);
v___x_3361_ = l_Lean_Meta_simpIfTarget(v_mvarId_3355_, v___x_3360_, v_useNewSemantics_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v_mvarId_3363_; lean_object* v_fvarId_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3422_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3362_);
lean_dec_ref(v___x_3361_);
v_mvarId_3363_ = lean_ctor_get(v_snd_3351_, 0);
v_fvarId_3364_ = lean_ctor_get(v_snd_3351_, 1);
v_isSharedCheck_3422_ = !lean_is_exclusive(v_snd_3351_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3366_ = v_snd_3351_;
v_isShared_3367_ = v_isSharedCheck_3422_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_fvarId_3364_);
lean_inc(v_mvarId_3363_);
lean_dec(v_snd_3351_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3422_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3368_; 
lean_inc(v_mvarId_3363_);
v___x_3368_ = l_Lean_Meta_simpIfTarget(v_mvarId_3363_, v___x_3360_, v_useNewSemantics_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3413_; 
v_a_3369_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3371_ = v___x_3368_;
v_isShared_3372_ = v_isSharedCheck_3413_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3368_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3413_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
uint8_t v___x_3389_; 
v___x_3389_ = l_Lean_instBEqMVarId_beq(v_mvarId_3355_, v_a_3362_);
lean_dec(v_mvarId_3355_);
if (v___x_3389_ == 0)
{
lean_dec(v_mvarId_3363_);
goto v___jp_3373_;
}
else
{
uint8_t v___x_3390_; 
v___x_3390_ = l_Lean_instBEqMVarId_beq(v_mvarId_3363_, v_a_3369_);
lean_dec(v_mvarId_3363_);
if (v___x_3390_ == 0)
{
goto v___jp_3373_;
}
else
{
lean_object* v_options_3391_; uint8_t v_hasTrace_3392_; 
lean_del_object(v___x_3371_);
lean_del_object(v___x_3366_);
lean_dec(v_fvarId_3364_);
lean_del_object(v___x_3358_);
lean_dec(v_fvarId_3356_);
lean_del_object(v___x_3353_);
lean_del_object(v___x_3348_);
v_options_3391_ = lean_ctor_get(v___y_3333_, 2);
v_hasTrace_3392_ = lean_ctor_get_uint8(v_options_3391_, sizeof(void*)*1);
if (v_hasTrace_3392_ == 0)
{
lean_dec(v_a_3369_);
lean_dec(v_a_3362_);
goto v___jp_3336_;
}
else
{
lean_object* v_inheritedTraceOptions_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; uint8_t v___x_3396_; 
v_inheritedTraceOptions_3393_ = lean_ctor_get(v___y_3333_, 13);
v___x_3394_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1));
v___x_3395_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2);
v___x_3396_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3393_, v_options_3391_, v___x_3395_);
if (v___x_3396_ == 0)
{
lean_dec(v_a_3369_);
lean_dec(v_a_3362_);
goto v___jp_3336_;
}
else
{
lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3397_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4);
v___x_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3398_, 0, v_a_3362_);
v___x_3399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3397_);
lean_ctor_set(v___x_3399_, 1, v___x_3398_);
v___x_3400_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6);
v___x_3401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3399_);
lean_ctor_set(v___x_3401_, 1, v___x_3400_);
v___x_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3402_, 0, v_a_3369_);
v___x_3403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3401_);
lean_ctor_set(v___x_3403_, 1, v___x_3402_);
v___x_3404_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_3394_, v___x_3403_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_dec_ref(v___x_3404_);
goto v___jp_3336_;
}
else
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3412_; 
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3412_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3407_ = v___x_3404_;
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___x_3404_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3410_; 
if (v_isShared_3408_ == 0)
{
v___x_3410_ = v___x_3407_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_a_3405_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
}
}
}
}
}
v___jp_3373_:
{
lean_object* v___x_3375_; 
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 1, v_fvarId_3356_);
lean_ctor_set(v___x_3366_, 0, v_a_3362_);
v___x_3375_ = v___x_3366_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3362_);
lean_ctor_set(v_reuseFailAlloc_3388_, 1, v_fvarId_3356_);
v___x_3375_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
lean_object* v___x_3377_; 
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 1, v_fvarId_3364_);
lean_ctor_set(v___x_3358_, 0, v_a_3369_);
v___x_3377_ = v___x_3358_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_a_3369_);
lean_ctor_set(v_reuseFailAlloc_3387_, 1, v_fvarId_3364_);
v___x_3377_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
lean_object* v___x_3379_; 
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 1, v___x_3377_);
lean_ctor_set(v___x_3353_, 0, v___x_3375_);
v___x_3379_ = v___x_3353_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v___x_3375_);
lean_ctor_set(v_reuseFailAlloc_3386_, 1, v___x_3377_);
v___x_3379_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
lean_object* v___x_3381_; 
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 0, v___x_3379_);
v___x_3381_ = v___x_3348_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3379_);
v___x_3381_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
lean_object* v___x_3383_; 
if (v_isShared_3372_ == 0)
{
lean_ctor_set(v___x_3371_, 0, v___x_3381_);
v___x_3383_ = v___x_3371_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v___x_3381_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
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
lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3421_; 
lean_del_object(v___x_3366_);
lean_dec(v_fvarId_3364_);
lean_dec(v_mvarId_3363_);
lean_dec(v_a_3362_);
lean_del_object(v___x_3358_);
lean_dec(v_fvarId_3356_);
lean_dec(v_mvarId_3355_);
lean_del_object(v___x_3353_);
lean_del_object(v___x_3348_);
v_a_3414_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3416_ = v___x_3368_;
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3368_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3419_; 
if (v_isShared_3417_ == 0)
{
v___x_3419_ = v___x_3416_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_a_3414_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
}
else
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3430_; 
lean_del_object(v___x_3358_);
lean_dec(v_fvarId_3356_);
lean_dec(v_mvarId_3355_);
lean_del_object(v___x_3353_);
lean_dec(v_snd_3351_);
lean_del_object(v___x_3348_);
v_a_3423_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3425_ = v___x_3361_;
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3361_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3428_; 
if (v_isShared_3426_ == 0)
{
v___x_3428_ = v___x_3425_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_a_3423_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3434_; lean_object* v___x_3436_; 
lean_dec(v_a_3342_);
v___x_3434_ = lean_box(0);
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 0, v___x_3434_);
v___x_3436_ = v___x_3344_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3434_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
}
else
{
return v___x_3341_;
}
}
else
{
lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3446_; 
lean_dec(v_hName_x3f_3329_);
lean_dec(v_mvarId_3328_);
v_a_3439_ = lean_ctor_get(v___x_3339_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3339_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3441_ = v___x_3339_;
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v___x_3339_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3444_; 
if (v_isShared_3442_ == 0)
{
v___x_3444_ = v___x_3441_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_a_3439_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
v___jp_3336_:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3337_ = lean_box(0);
v___x_3338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3337_);
return v___x_3338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0___boxed(lean_object* v_mvarId_3447_, lean_object* v_hName_x3f_3448_, lean_object* v_useNewSemantics_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_){
_start:
{
uint8_t v_useNewSemantics_boxed_3455_; lean_object* v_res_3456_; 
v_useNewSemantics_boxed_3455_ = lean_unbox(v_useNewSemantics_3449_);
v_res_3456_ = l_Lean_Meta_splitIfTarget_x3f___lam__0(v_mvarId_3447_, v_hName_x3f_3448_, v_useNewSemantics_boxed_3455_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f(lean_object* v_mvarId_3457_, lean_object* v_hName_x3f_3458_, uint8_t v_useNewSemantics_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_){
_start:
{
lean_object* v___x_3465_; lean_object* v___f_3466_; lean_object* v___x_3467_; 
v___x_3465_ = lean_box(v_useNewSemantics_3459_);
v___f_3466_ = lean_alloc_closure((void*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3466_, 0, v_mvarId_3457_);
lean_closure_set(v___f_3466_, 1, v_hName_x3f_3458_);
lean_closure_set(v___f_3466_, 2, v___x_3465_);
v___x_3467_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v___f_3466_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_);
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___boxed(lean_object* v_mvarId_3468_, lean_object* v_hName_x3f_3469_, lean_object* v_useNewSemantics_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_){
_start:
{
uint8_t v_useNewSemantics_boxed_3476_; lean_object* v_res_3477_; 
v_useNewSemantics_boxed_3476_ = lean_unbox(v_useNewSemantics_3470_);
v_res_3477_ = l_Lean_Meta_splitIfTarget_x3f(v_mvarId_3468_, v_hName_x3f_3469_, v_useNewSemantics_boxed_3476_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_);
lean_dec(v_a_3474_);
lean_dec_ref(v_a_3473_);
lean_dec(v_a_3472_);
lean_dec_ref(v_a_3471_);
return v_res_3477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___lam__0(lean_object* v___x_3478_, lean_object* v_mvarId_3479_, lean_object* v_hName_x3f_3480_, lean_object* v_fvarId_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_){
_start:
{
lean_object* v___x_3490_; 
lean_inc(v___y_3485_);
lean_inc_ref(v___y_3484_);
lean_inc(v___y_3483_);
lean_inc_ref(v___y_3482_);
v___x_3490_ = lean_infer_type(v___x_3478_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v_a_3491_; lean_object* v___x_3492_; 
v_a_3491_ = lean_ctor_get(v___x_3490_, 0);
lean_inc(v_a_3491_);
lean_dec_ref(v___x_3490_);
v___x_3492_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(v_mvarId_3479_, v_a_3491_, v_hName_x3f_3480_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3587_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3495_ = v___x_3492_;
v_isShared_3496_ = v_isSharedCheck_3587_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3492_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3587_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
if (lean_obj_tag(v_a_3493_) == 1)
{
lean_object* v_val_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3582_; 
lean_del_object(v___x_3495_);
v_val_3497_ = lean_ctor_get(v_a_3493_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v_a_3493_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3499_ = v_a_3493_;
v_isShared_3500_ = v_isSharedCheck_3582_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_val_3497_);
lean_dec(v_a_3493_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3582_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v_fst_3501_; lean_object* v_snd_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3581_; 
v_fst_3501_ = lean_ctor_get(v_val_3497_, 0);
v_snd_3502_ = lean_ctor_get(v_val_3497_, 1);
v_isSharedCheck_3581_ = !lean_is_exclusive(v_val_3497_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3504_ = v_val_3497_;
v_isShared_3505_ = v_isSharedCheck_3581_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_snd_3502_);
lean_inc(v_fst_3501_);
lean_dec(v_val_3497_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3581_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v_mvarId_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3579_; 
v_mvarId_3506_ = lean_ctor_get(v_fst_3501_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v_fst_3501_);
if (v_isSharedCheck_3579_ == 0)
{
lean_object* v_unused_3580_; 
v_unused_3580_ = lean_ctor_get(v_fst_3501_, 1);
lean_dec(v_unused_3580_);
v___x_3508_ = v_fst_3501_;
v_isShared_3509_ = v_isSharedCheck_3579_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_mvarId_3506_);
lean_dec(v_fst_3501_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3579_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
uint8_t v___x_3510_; lean_object* v___x_3511_; 
v___x_3510_ = 0;
lean_inc(v_fvarId_3481_);
lean_inc(v_mvarId_3506_);
v___x_3511_ = l_Lean_Meta_simpIfLocalDecl(v_mvarId_3506_, v_fvarId_3481_, v___x_3510_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; lean_object* v_mvarId_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3569_; 
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_a_3512_);
lean_dec_ref(v___x_3511_);
v_mvarId_3513_ = lean_ctor_get(v_snd_3502_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v_snd_3502_);
if (v_isSharedCheck_3569_ == 0)
{
lean_object* v_unused_3570_; 
v_unused_3570_ = lean_ctor_get(v_snd_3502_, 1);
lean_dec(v_unused_3570_);
v___x_3515_ = v_snd_3502_;
v_isShared_3516_ = v_isSharedCheck_3569_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_mvarId_3513_);
lean_dec(v_snd_3502_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3569_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3517_; 
lean_inc(v_mvarId_3513_);
v___x_3517_ = l_Lean_Meta_simpIfLocalDecl(v_mvarId_3513_, v_fvarId_3481_, v___x_3510_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3560_; 
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3520_ = v___x_3517_;
v_isShared_3521_ = v_isSharedCheck_3560_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3517_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3560_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
uint8_t v___x_3532_; 
v___x_3532_ = l_Lean_instBEqMVarId_beq(v_mvarId_3506_, v_a_3512_);
lean_dec(v_mvarId_3506_);
if (v___x_3532_ == 0)
{
lean_del_object(v___x_3515_);
lean_dec(v_mvarId_3513_);
lean_del_object(v___x_3508_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
goto v___jp_3522_;
}
else
{
uint8_t v___x_3533_; 
v___x_3533_ = l_Lean_instBEqMVarId_beq(v_mvarId_3513_, v_a_3518_);
lean_dec(v_mvarId_3513_);
if (v___x_3533_ == 0)
{
lean_del_object(v___x_3515_);
lean_del_object(v___x_3508_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
goto v___jp_3522_;
}
else
{
lean_object* v_options_3534_; uint8_t v_hasTrace_3535_; 
lean_del_object(v___x_3520_);
lean_del_object(v___x_3504_);
lean_del_object(v___x_3499_);
v_options_3534_ = lean_ctor_get(v___y_3484_, 2);
v_hasTrace_3535_ = lean_ctor_get_uint8(v_options_3534_, sizeof(void*)*1);
if (v_hasTrace_3535_ == 0)
{
lean_dec(v_a_3518_);
lean_del_object(v___x_3515_);
lean_dec(v_a_3512_);
lean_del_object(v___x_3508_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
goto v___jp_3487_;
}
else
{
lean_object* v_inheritedTraceOptions_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; uint8_t v___x_3539_; 
v_inheritedTraceOptions_3536_ = lean_ctor_get(v___y_3484_, 13);
v___x_3537_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1));
v___x_3538_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2);
v___x_3539_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3536_, v_options_3534_, v___x_3538_);
if (v___x_3539_ == 0)
{
lean_dec(v_a_3518_);
lean_del_object(v___x_3515_);
lean_dec(v_a_3512_);
lean_del_object(v___x_3508_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
goto v___jp_3487_;
}
else
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3543_; 
v___x_3540_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4);
v___x_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3541_, 0, v_a_3512_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set_tag(v___x_3515_, 7);
lean_ctor_set(v___x_3515_, 1, v___x_3541_);
lean_ctor_set(v___x_3515_, 0, v___x_3540_);
v___x_3543_ = v___x_3515_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3540_);
lean_ctor_set(v_reuseFailAlloc_3559_, 1, v___x_3541_);
v___x_3543_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
lean_object* v___x_3544_; lean_object* v___x_3546_; 
v___x_3544_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6);
if (v_isShared_3509_ == 0)
{
lean_ctor_set_tag(v___x_3508_, 7);
lean_ctor_set(v___x_3508_, 1, v___x_3544_);
lean_ctor_set(v___x_3508_, 0, v___x_3543_);
v___x_3546_ = v___x_3508_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v___x_3543_);
lean_ctor_set(v_reuseFailAlloc_3558_, 1, v___x_3544_);
v___x_3546_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3547_, 0, v_a_3518_);
v___x_3548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3546_);
lean_ctor_set(v___x_3548_, 1, v___x_3547_);
v___x_3549_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_3537_, v___x_3548_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_dec_ref(v___x_3549_);
goto v___jp_3487_;
}
else
{
lean_object* v_a_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3557_; 
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3552_ = v___x_3549_;
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_a_3550_);
lean_dec(v___x_3549_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3555_; 
if (v_isShared_3553_ == 0)
{
v___x_3555_ = v___x_3552_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v_a_3550_);
v___x_3555_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
return v___x_3555_;
}
}
}
}
}
}
}
}
}
v___jp_3522_:
{
lean_object* v___x_3524_; 
if (v_isShared_3505_ == 0)
{
lean_ctor_set(v___x_3504_, 1, v_a_3518_);
lean_ctor_set(v___x_3504_, 0, v_a_3512_);
v___x_3524_ = v___x_3504_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3512_);
lean_ctor_set(v_reuseFailAlloc_3531_, 1, v_a_3518_);
v___x_3524_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
lean_object* v___x_3526_; 
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 0, v___x_3524_);
v___x_3526_ = v___x_3499_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v___x_3524_);
v___x_3526_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
lean_object* v___x_3528_; 
if (v_isShared_3521_ == 0)
{
lean_ctor_set(v___x_3520_, 0, v___x_3526_);
v___x_3528_ = v___x_3520_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3526_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
}
}
}
else
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
lean_del_object(v___x_3515_);
lean_dec(v_mvarId_3513_);
lean_dec(v_a_3512_);
lean_del_object(v___x_3508_);
lean_dec(v_mvarId_3506_);
lean_del_object(v___x_3504_);
lean_del_object(v___x_3499_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
v_a_3561_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3563_ = v___x_3517_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_3517_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3561_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
}
else
{
lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3578_; 
lean_del_object(v___x_3508_);
lean_dec(v_mvarId_3506_);
lean_del_object(v___x_3504_);
lean_dec(v_snd_3502_);
lean_del_object(v___x_3499_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v_fvarId_3481_);
v_a_3571_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3573_ = v___x_3511_;
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v___x_3511_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3576_; 
if (v_isShared_3574_ == 0)
{
v___x_3576_ = v___x_3573_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_a_3571_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3583_; lean_object* v___x_3585_; 
lean_dec(v_a_3493_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v_fvarId_3481_);
v___x_3583_ = lean_box(0);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 0, v___x_3583_);
v___x_3585_ = v___x_3495_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v___x_3583_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
}
else
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v_fvarId_3481_);
v_a_3588_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3590_ = v___x_3492_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3492_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3593_; 
if (v_isShared_3591_ == 0)
{
v___x_3593_ = v___x_3590_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_a_3588_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
else
{
lean_object* v_a_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3603_; 
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v_fvarId_3481_);
lean_dec(v_hName_x3f_3480_);
lean_dec(v_mvarId_3479_);
v_a_3596_ = lean_ctor_get(v___x_3490_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3598_ = v___x_3490_;
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_a_3596_);
lean_dec(v___x_3490_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3601_; 
if (v_isShared_3599_ == 0)
{
v___x_3601_ = v___x_3598_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_a_3596_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
return v___x_3601_;
}
}
}
v___jp_3487_:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; 
v___x_3488_ = lean_box(0);
v___x_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3488_);
return v___x_3489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___lam__0___boxed(lean_object* v___x_3604_, lean_object* v_mvarId_3605_, lean_object* v_hName_x3f_3606_, lean_object* v_fvarId_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_){
_start:
{
lean_object* v_res_3613_; 
v_res_3613_ = l_Lean_Meta_splitIfLocalDecl_x3f___lam__0(v___x_3604_, v_mvarId_3605_, v_hName_x3f_3606_, v_fvarId_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f(lean_object* v_mvarId_3614_, lean_object* v_fvarId_3615_, lean_object* v_hName_x3f_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_){
_start:
{
lean_object* v___x_3622_; lean_object* v___f_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; 
lean_inc(v_fvarId_3615_);
v___x_3622_ = l_Lean_mkFVar(v_fvarId_3615_);
lean_inc(v_mvarId_3614_);
v___f_3623_ = lean_alloc_closure((void*)(l_Lean_Meta_splitIfLocalDecl_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3623_, 0, v___x_3622_);
lean_closure_set(v___f_3623_, 1, v_mvarId_3614_);
lean_closure_set(v___f_3623_, 2, v_hName_x3f_3616_);
lean_closure_set(v___f_3623_, 3, v_fvarId_3615_);
v___x_3624_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3624_, 0, lean_box(0));
lean_closure_set(v___x_3624_, 1, v_mvarId_3614_);
lean_closure_set(v___x_3624_, 2, v___f_3623_);
v___x_3625_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v___x_3624_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_);
return v___x_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___boxed(lean_object* v_mvarId_3626_, lean_object* v_fvarId_3627_, lean_object* v_hName_x3f_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_){
_start:
{
lean_object* v_res_3634_; 
v_res_3634_ = l_Lean_Meta_splitIfLocalDecl_x3f(v_mvarId_3626_, v_fvarId_3627_, v_hName_x3f_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_);
lean_dec(v_a_3632_);
lean_dec_ref(v_a_3631_);
lean_dec(v_a_3630_);
lean_dec_ref(v_a_3629_);
return v_res_3634_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3655_ = lean_unsigned_to_nat(3526097586u);
v___x_3656_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_));
v___x_3657_ = l_Lean_Name_num___override(v___x_3656_, v___x_3655_);
return v___x_3657_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3659_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_));
v___x_3660_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3661_ = l_Lean_Name_str___override(v___x_3660_, v___x_3659_);
return v___x_3661_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3663_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_));
v___x_3664_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3665_ = l_Lean_Name_str___override(v___x_3664_, v___x_3663_);
return v___x_3665_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3666_ = lean_unsigned_to_nat(2u);
v___x_3667_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3668_ = l_Lean_Name_num___override(v___x_3667_, v___x_3666_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3670_; uint8_t v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3670_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10));
v___x_3671_ = 0;
v___x_3672_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3673_ = l_Lean_registerTraceClass(v___x_3670_, v___x_3671_, v___x_3672_);
return v___x_3673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2____boxed(lean_object* v_a_3674_){
_start:
{
lean_object* v_res_3675_; 
v_res_3675_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_();
return v_res_3675_;
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
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_();
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
