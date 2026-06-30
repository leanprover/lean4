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
lean_dec_ref_known(v_e_424_, 3);
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
lean_dec_ref_known(v_e_424_, 3);
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
lean_dec_ref_known(v_e_424_, 2);
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
lean_dec_ref_known(v_e_424_, 3);
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
lean_dec_ref_known(v___x_447_, 1);
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
lean_dec_ref_known(v_e_424_, 4);
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
lean_dec_ref_known(v___x_454_, 1);
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
lean_dec_ref_known(v___x_527_, 1);
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
lean_dec_ref_known(v___x_552_, 1);
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
lean_dec_ref_known(v_x_578_, 2);
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
lean_dec_ref_known(v___x_638_, 1);
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
lean_dec_ref_known(v_fst_605_, 1);
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
lean_dec_ref_known(v___x_782_, 1);
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
lean_dec_ref_known(v_a_924_, 1);
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
lean_dec_ref_known(v_a_924_, 1);
return v___x_923_;
}
else
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
lean_dec_ref_known(v___x_923_, 1);
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
lean_dec_ref_known(v_a_924_, 1);
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
lean_dec_ref_known(v_a_984_, 1);
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
lean_dec_ref_known(v___x_983_, 1);
v___x_988_ = lean_unsigned_to_nat(3u);
v___x_989_ = l_Lean_Expr_getRevArg_x21(v_val_985_, v___x_988_);
v___x_990_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(v_kind_971_, v_exceptionSet_972_, v___x_989_, v_a_974_, v_a_975_, v_a_976_, v_a_977_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
lean_dec_ref_known(v___x_990_, 1);
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
lean_dec_ref_known(v_a_991_, 1);
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
lean_dec_ref_known(v___x_1233_, 1);
v___x_1235_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__9));
v___x_1236_ = l_Lean_Meta_SimpTheorems_addConst(v_a_1234_, v___x_1235_, v___x_1230_, v___x_1231_, v___x_1232_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_a_1237_);
lean_dec_ref_known(v___x_1236_, 1);
v___x_1238_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__11));
v___x_1239_ = l_Lean_Meta_SimpTheorems_addConst(v_a_1237_, v___x_1238_, v___x_1230_, v___x_1231_, v___x_1232_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_a_1240_);
lean_dec_ref_known(v___x_1239_, 1);
v___x_1241_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__13));
v___x_1242_ = l_Lean_Meta_SimpTheorems_addConst(v_a_1240_, v___x_1241_, v___x_1230_, v___x_1231_, v___x_1232_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v___x_1244_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_a_1243_);
lean_dec_ref_known(v___x_1242_, 1);
v___x_1244_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_1226_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1246_; lean_object* v_maxSteps_1247_; lean_object* v_maxDischargeDepth_1248_; uint8_t v_contextual_1249_; uint8_t v_memoize_1250_; uint8_t v_singlePass_1251_; uint8_t v_zeta_1252_; uint8_t v_beta_1253_; uint8_t v_eta_1254_; uint8_t v_etaStruct_1255_; uint8_t v_iota_1256_; uint8_t v_proj_1257_; uint8_t v_decide_1258_; uint8_t v_arith_1259_; uint8_t v_autoUnfold_1260_; uint8_t v_failIfUnchanged_1261_; uint8_t v_ground_1262_; uint8_t v_unfoldPartialApp_1263_; uint8_t v_zetaDelta_1264_; uint8_t v_index_1265_; uint8_t v_implicitDefEqProofs_1266_; uint8_t v_zetaUnused_1267_; uint8_t v_catchRuntime_1268_; uint8_t v_zetaHave_1269_; uint8_t v_congrConsts_1270_; uint8_t v_bitVecOfNat_1271_; uint8_t v_warnExponents_1272_; uint8_t v_suggestions_1273_; lean_object* v_maxSuggestions_1274_; uint8_t v_locals_1275_; uint8_t v_instances_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref_known(v___x_1244_, 1);
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
v___x_1281_ = l_Lean_Options_empty;
v___x_1282_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1277_, v___x_1280_, v_a_1245_, v___x_1281_, v_a_1223_, v_a_1225_, v_a_1226_);
return v___x_1282_;
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_dec(v_a_1243_);
v_a_1283_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1244_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1244_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
v_a_1291_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1242_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1242_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
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
else
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
v_a_1299_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1239_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1239_);
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
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
v_a_1307_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1236_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1236_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
v_a_1315_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1233_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1233_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_getSimpContext___boxed(lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
lean_dec(v_a_1326_);
lean_dec_ref(v_a_1325_);
lean_dec(v_a_1324_);
lean_dec_ref(v_a_1323_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_1333_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1337_; lean_object* v_maxSteps_1338_; lean_object* v_maxDischargeDepth_1339_; uint8_t v_contextual_1340_; uint8_t v_memoize_1341_; uint8_t v_singlePass_1342_; uint8_t v_zeta_1343_; uint8_t v_beta_1344_; uint8_t v_eta_1345_; uint8_t v_etaStruct_1346_; uint8_t v_iota_1347_; uint8_t v_proj_1348_; uint8_t v_decide_1349_; uint8_t v_arith_1350_; uint8_t v_autoUnfold_1351_; uint8_t v_failIfUnchanged_1352_; uint8_t v_ground_1353_; uint8_t v_unfoldPartialApp_1354_; uint8_t v_zetaDelta_1355_; uint8_t v_index_1356_; uint8_t v_implicitDefEqProofs_1357_; uint8_t v_zetaUnused_1358_; uint8_t v_catchRuntime_1359_; uint8_t v_zetaHave_1360_; uint8_t v_congrConsts_1361_; uint8_t v_bitVecOfNat_1362_; uint8_t v_warnExponents_1363_; uint8_t v_suggestions_1364_; lean_object* v_maxSuggestions_1365_; uint8_t v_locals_1366_; uint8_t v_instances_1367_; uint8_t v___x_1368_; uint8_t v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1335_, 1);
v___x_1337_ = l_Lean_Meta_Simp_neutralConfig;
v_maxSteps_1338_ = lean_ctor_get(v___x_1337_, 0);
v_maxDischargeDepth_1339_ = lean_ctor_get(v___x_1337_, 1);
v_contextual_1340_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*3);
v_memoize_1341_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*3 + 1);
v_singlePass_1342_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*3 + 2);
v_zeta_1343_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*3 + 3);
v_beta_1344_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*3 + 4);
v_eta_1345_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*3 + 5);
v_etaStruct_1346_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*3 + 6);
v_iota_1347_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*3 + 7);
v_proj_1348_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*3 + 8);
v_decide_1349_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*3 + 9);
v_arith_1350_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*3 + 10);
v_autoUnfold_1351_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*3 + 11);
v_failIfUnchanged_1352_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*3 + 13);
v_ground_1353_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_1354_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*3 + 15);
v_zetaDelta_1355_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*3 + 16);
v_index_1356_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_1357_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*3 + 18);
v_zetaUnused_1358_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*3 + 19);
v_catchRuntime_1359_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*3 + 20);
v_zetaHave_1360_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*3 + 21);
v_congrConsts_1361_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*3 + 23);
v_bitVecOfNat_1362_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*3 + 24);
v_warnExponents_1363_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*3 + 25);
v_suggestions_1364_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*3 + 26);
v_maxSuggestions_1365_ = lean_ctor_get(v___x_1337_, 2);
v_locals_1366_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*3 + 27);
v_instances_1367_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*3 + 28);
v___x_1368_ = 0;
v___x_1369_ = 1;
lean_inc(v_maxSuggestions_1365_);
lean_inc(v_maxDischargeDepth_1339_);
lean_inc(v_maxSteps_1338_);
v___x_1370_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1370_, 0, v_maxSteps_1338_);
lean_ctor_set(v___x_1370_, 1, v_maxDischargeDepth_1339_);
lean_ctor_set(v___x_1370_, 2, v_maxSuggestions_1365_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3, v_contextual_1340_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 1, v_memoize_1341_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 2, v_singlePass_1342_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 3, v_zeta_1343_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 4, v_beta_1344_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 5, v_eta_1345_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 6, v_etaStruct_1346_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 7, v_iota_1347_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 8, v_proj_1348_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 9, v_decide_1349_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 10, v_arith_1350_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 11, v_autoUnfold_1351_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 12, v___x_1368_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 13, v_failIfUnchanged_1352_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 14, v_ground_1353_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 15, v_unfoldPartialApp_1354_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 16, v_zetaDelta_1355_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 17, v_index_1356_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_1357_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 19, v_zetaUnused_1358_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 20, v_catchRuntime_1359_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 21, v_zetaHave_1360_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 22, v___x_1369_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 23, v_congrConsts_1361_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 24, v_bitVecOfNat_1362_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 25, v_warnExponents_1363_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 26, v_suggestions_1364_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 27, v_locals_1366_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 28, v_instances_1367_);
v___x_1371_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg___closed__0));
v___x_1372_ = l_Lean_Options_empty;
v___x_1373_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1370_, v___x_1371_, v_a_1336_, v___x_1372_, v_a_1331_, v_a_1332_, v_a_1333_);
return v___x_1373_;
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
v_a_1374_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1335_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1335_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg___boxed(lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_1382_, v_a_1383_, v_a_1384_);
lean_dec(v_a_1384_);
lean_dec_ref(v_a_1383_);
lean_dec_ref(v_a_1382_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27(lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_1387_, v_a_1389_, v_a_1390_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___boxed(lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27(v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
lean_dec(v_a_1394_);
lean_dec_ref(v_a_1393_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(lean_object* v_e_1399_, lean_object* v___y_1400_){
_start:
{
uint8_t v___x_1402_; 
v___x_1402_ = l_Lean_Expr_hasMVar(v_e_1399_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1403_; 
v___x_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1403_, 0, v_e_1399_);
return v___x_1403_;
}
else
{
lean_object* v___x_1404_; lean_object* v_mctx_1405_; lean_object* v___x_1406_; lean_object* v_fst_1407_; lean_object* v_snd_1408_; lean_object* v___x_1409_; lean_object* v_cache_1410_; lean_object* v_zetaDeltaFVarIds_1411_; lean_object* v_postponed_1412_; lean_object* v_diag_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1422_; 
v___x_1404_ = lean_st_ref_get(v___y_1400_);
v_mctx_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc_ref(v_mctx_1405_);
lean_dec(v___x_1404_);
v___x_1406_ = l_Lean_instantiateMVarsCore(v_mctx_1405_, v_e_1399_);
v_fst_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_fst_1407_);
v_snd_1408_ = lean_ctor_get(v___x_1406_, 1);
lean_inc(v_snd_1408_);
lean_dec_ref(v___x_1406_);
v___x_1409_ = lean_st_ref_take(v___y_1400_);
v_cache_1410_ = lean_ctor_get(v___x_1409_, 1);
v_zetaDeltaFVarIds_1411_ = lean_ctor_get(v___x_1409_, 2);
v_postponed_1412_ = lean_ctor_get(v___x_1409_, 3);
v_diag_1413_ = lean_ctor_get(v___x_1409_, 4);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1422_ == 0)
{
lean_object* v_unused_1423_; 
v_unused_1423_ = lean_ctor_get(v___x_1409_, 0);
lean_dec(v_unused_1423_);
v___x_1415_ = v___x_1409_;
v_isShared_1416_ = v_isSharedCheck_1422_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_diag_1413_);
lean_inc(v_postponed_1412_);
lean_inc(v_zetaDeltaFVarIds_1411_);
lean_inc(v_cache_1410_);
lean_dec(v___x_1409_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1422_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 0, v_snd_1408_);
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_snd_1408_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_cache_1410_);
lean_ctor_set(v_reuseFailAlloc_1421_, 2, v_zetaDeltaFVarIds_1411_);
lean_ctor_set(v_reuseFailAlloc_1421_, 3, v_postponed_1412_);
lean_ctor_set(v_reuseFailAlloc_1421_, 4, v_diag_1413_);
v___x_1418_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = lean_st_ref_set(v___y_1400_, v___x_1418_);
v___x_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1420_, 0, v_fst_1407_);
return v___x_1420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg___boxed(lean_object* v_e_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_e_1424_, v___y_1425_);
lean_dec(v___y_1425_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0(lean_object* v_e_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_e_1428_, v___y_1433_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___boxed(lean_object* v_e_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0(v_e_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(lean_object* v_cls_1448_, lean_object* v_msg_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v_ref_1455_; lean_object* v___x_1456_; lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1501_; 
v_ref_1455_ = lean_ctor_get(v___y_1452_, 5);
v___x_1456_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(v_msg_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1459_ = v___x_1456_;
v_isShared_1460_ = v_isSharedCheck_1501_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1456_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1501_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1461_; lean_object* v_traceState_1462_; lean_object* v_env_1463_; lean_object* v_nextMacroScope_1464_; lean_object* v_ngen_1465_; lean_object* v_auxDeclNGen_1466_; lean_object* v_cache_1467_; lean_object* v_messages_1468_; lean_object* v_infoState_1469_; lean_object* v_snapshotTasks_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1500_; 
v___x_1461_ = lean_st_ref_take(v___y_1453_);
v_traceState_1462_ = lean_ctor_get(v___x_1461_, 4);
v_env_1463_ = lean_ctor_get(v___x_1461_, 0);
v_nextMacroScope_1464_ = lean_ctor_get(v___x_1461_, 1);
v_ngen_1465_ = lean_ctor_get(v___x_1461_, 2);
v_auxDeclNGen_1466_ = lean_ctor_get(v___x_1461_, 3);
v_cache_1467_ = lean_ctor_get(v___x_1461_, 5);
v_messages_1468_ = lean_ctor_get(v___x_1461_, 6);
v_infoState_1469_ = lean_ctor_get(v___x_1461_, 7);
v_snapshotTasks_1470_ = lean_ctor_get(v___x_1461_, 8);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1472_ = v___x_1461_;
v_isShared_1473_ = v_isSharedCheck_1500_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_snapshotTasks_1470_);
lean_inc(v_infoState_1469_);
lean_inc(v_messages_1468_);
lean_inc(v_cache_1467_);
lean_inc(v_traceState_1462_);
lean_inc(v_auxDeclNGen_1466_);
lean_inc(v_ngen_1465_);
lean_inc(v_nextMacroScope_1464_);
lean_inc(v_env_1463_);
lean_dec(v___x_1461_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1500_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
uint64_t v_tid_1474_; lean_object* v_traces_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1499_; 
v_tid_1474_ = lean_ctor_get_uint64(v_traceState_1462_, sizeof(void*)*1);
v_traces_1475_ = lean_ctor_get(v_traceState_1462_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_traceState_1462_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1477_ = v_traceState_1462_;
v_isShared_1478_ = v_isSharedCheck_1499_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_traces_1475_);
lean_dec(v_traceState_1462_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1499_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1479_; double v___x_1480_; uint8_t v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1489_; 
v___x_1479_ = lean_box(0);
v___x_1480_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0);
v___x_1481_ = 0;
v___x_1482_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__1));
v___x_1483_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1483_, 0, v_cls_1448_);
lean_ctor_set(v___x_1483_, 1, v___x_1479_);
lean_ctor_set(v___x_1483_, 2, v___x_1482_);
lean_ctor_set_float(v___x_1483_, sizeof(void*)*3, v___x_1480_);
lean_ctor_set_float(v___x_1483_, sizeof(void*)*3 + 8, v___x_1480_);
lean_ctor_set_uint8(v___x_1483_, sizeof(void*)*3 + 16, v___x_1481_);
v___x_1484_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__2));
v___x_1485_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1483_);
lean_ctor_set(v___x_1485_, 1, v_a_1457_);
lean_ctor_set(v___x_1485_, 2, v___x_1484_);
lean_inc(v_ref_1455_);
v___x_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1486_, 0, v_ref_1455_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
v___x_1487_ = l_Lean_PersistentArray_push___redArg(v_traces_1475_, v___x_1486_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 0, v___x_1487_);
v___x_1489_ = v___x_1477_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1487_);
lean_ctor_set_uint64(v_reuseFailAlloc_1498_, sizeof(void*)*1, v_tid_1474_);
v___x_1489_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v___x_1491_; 
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 4, v___x_1489_);
v___x_1491_ = v___x_1472_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_env_1463_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v_nextMacroScope_1464_);
lean_ctor_set(v_reuseFailAlloc_1497_, 2, v_ngen_1465_);
lean_ctor_set(v_reuseFailAlloc_1497_, 3, v_auxDeclNGen_1466_);
lean_ctor_set(v_reuseFailAlloc_1497_, 4, v___x_1489_);
lean_ctor_set(v_reuseFailAlloc_1497_, 5, v_cache_1467_);
lean_ctor_set(v_reuseFailAlloc_1497_, 6, v_messages_1468_);
lean_ctor_set(v_reuseFailAlloc_1497_, 7, v_infoState_1469_);
lean_ctor_set(v_reuseFailAlloc_1497_, 8, v_snapshotTasks_1470_);
v___x_1491_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1495_; 
v___x_1492_ = lean_st_ref_set(v___y_1453_, v___x_1491_);
v___x_1493_ = lean_box(0);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 0, v___x_1493_);
v___x_1495_ = v___x_1459_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg___boxed(lean_object* v_cls_1502_, lean_object* v_msg_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v_cls_1502_, v_msg_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
return v_res_1509_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1516_ = lean_box(0);
v___x_1517_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__3));
v___x_1518_ = l_Lean_mkConst(v___x_1517_, v___x_1516_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(lean_object* v_a_1519_, lean_object* v_numIndices_1520_, lean_object* v_as_1521_, lean_object* v_i_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v_zero_1528_; uint8_t v_isZero_1529_; 
v_zero_1528_ = lean_unsigned_to_nat(0u);
v_isZero_1529_ = lean_nat_dec_eq(v_i_1522_, v_zero_1528_);
if (v_isZero_1529_ == 1)
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
lean_dec(v_i_1522_);
lean_dec_ref(v_a_1519_);
v___x_1530_ = lean_box(0);
v___x_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
return v___x_1531_;
}
else
{
lean_object* v_one_1532_; lean_object* v_n_1533_; lean_object* v___x_1534_; 
v_one_1532_ = lean_unsigned_to_nat(1u);
v_n_1533_ = lean_nat_sub(v_i_1522_, v_one_1532_);
lean_dec(v_i_1522_);
v___x_1534_ = lean_array_fget(v_as_1521_, v_n_1533_);
if (lean_obj_tag(v___x_1534_) == 0)
{
v_i_1522_ = v_n_1533_;
goto _start;
}
else
{
lean_object* v_val_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1601_; 
v_val_1536_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1538_ = v___x_1534_;
v_isShared_1539_ = v_isSharedCheck_1601_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_val_1536_);
lean_dec(v___x_1534_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1601_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
uint8_t v___y_1541_; lean_object* v___x_1598_; uint8_t v___x_1599_; 
v___x_1598_ = l_Lean_LocalDecl_index(v_val_1536_);
v___x_1599_ = lean_nat_dec_le(v_numIndices_1520_, v___x_1598_);
lean_dec(v___x_1598_);
if (v___x_1599_ == 0)
{
uint8_t v___x_1600_; 
v___x_1600_ = l_Lean_LocalDecl_isAuxDecl(v_val_1536_);
v___y_1541_ = v___x_1600_;
goto v___jp_1540_;
}
else
{
v___y_1541_ = v___x_1599_;
goto v___jp_1540_;
}
v___jp_1540_:
{
if (v___y_1541_ == 0)
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = l_Lean_LocalDecl_type(v_val_1536_);
lean_inc_ref(v___x_1542_);
lean_inc_ref(v_a_1519_);
v___x_1543_ = l_Lean_Meta_isExprDefEq(v_a_1519_, v___x_1542_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1588_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1546_ = v___x_1543_;
v_isShared_1547_ = v_isSharedCheck_1588_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1543_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1588_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
uint8_t v___x_1548_; 
v___x_1548_ = lean_unbox(v_a_1544_);
lean_dec(v_a_1544_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; uint8_t v___x_1550_; 
lean_del_object(v___x_1546_);
v___x_1549_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__1));
v___x_1550_ = l_Lean_Expr_isAppOfArity(v_a_1519_, v___x_1549_, v_one_1532_);
if (v___x_1550_ == 0)
{
lean_dec_ref(v___x_1542_);
lean_del_object(v___x_1538_);
lean_dec(v_val_1536_);
v_i_1522_ = v_n_1533_;
goto _start;
}
else
{
lean_object* v___x_1552_; uint8_t v___x_1553_; 
v___x_1552_ = l_Lean_Expr_appArg_x21(v_a_1519_);
v___x_1553_ = l_Lean_Expr_isAppOfArity(v___x_1552_, v___x_1549_, v_one_1532_);
if (v___x_1553_ == 0)
{
lean_dec_ref(v___x_1552_);
lean_dec_ref(v___x_1542_);
lean_del_object(v___x_1538_);
lean_dec(v_val_1536_);
v_i_1522_ = v_n_1533_;
goto _start;
}
else
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = l_Lean_Expr_appArg_x21(v___x_1552_);
lean_dec_ref(v___x_1552_);
lean_inc_ref(v___x_1555_);
v___x_1556_ = l_Lean_Meta_isExprDefEq(v___x_1555_, v___x_1542_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1572_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1559_ = v___x_1556_;
v_isShared_1560_ = v_isSharedCheck_1572_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1556_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1572_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
uint8_t v___x_1561_; 
v___x_1561_ = lean_unbox(v_a_1557_);
lean_dec(v_a_1557_);
if (v___x_1561_ == 0)
{
lean_del_object(v___x_1559_);
lean_dec_ref(v___x_1555_);
lean_del_object(v___x_1538_);
lean_dec(v_val_1536_);
v_i_1522_ = v_n_1533_;
goto _start;
}
else
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1567_; 
lean_dec(v_n_1533_);
lean_dec_ref(v_a_1519_);
v___x_1563_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4);
v___x_1564_ = l_Lean_LocalDecl_toExpr(v_val_1536_);
v___x_1565_ = l_Lean_mkAppB(v___x_1563_, v___x_1555_, v___x_1564_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 0, v___x_1565_);
v___x_1567_ = v___x_1538_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1565_);
v___x_1567_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
lean_object* v___x_1569_; 
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 0, v___x_1567_);
v___x_1569_ = v___x_1559_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec_ref(v___x_1555_);
lean_del_object(v___x_1538_);
lean_dec(v_val_1536_);
lean_dec(v_n_1533_);
lean_dec_ref(v_a_1519_);
v_a_1573_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1556_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1556_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
}
}
else
{
lean_object* v___x_1581_; lean_object* v___x_1583_; 
lean_dec_ref(v___x_1542_);
lean_dec(v_n_1533_);
lean_dec_ref(v_a_1519_);
v___x_1581_ = l_Lean_LocalDecl_toExpr(v_val_1536_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 0, v___x_1581_);
v___x_1583_ = v___x_1538_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
lean_object* v___x_1585_; 
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 0, v___x_1583_);
v___x_1585_ = v___x_1546_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_dec_ref(v___x_1542_);
lean_del_object(v___x_1538_);
lean_dec(v_val_1536_);
lean_dec(v_n_1533_);
lean_dec_ref(v_a_1519_);
v_a_1589_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1543_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1543_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
else
{
lean_del_object(v___x_1538_);
lean_dec(v_val_1536_);
v_i_1522_ = v_n_1533_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_a_1602_, lean_object* v_numIndices_1603_, lean_object* v_as_1604_, lean_object* v_i_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_a_1602_, v_numIndices_1603_, v_as_1604_, v_i_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec_ref(v_as_1604_);
lean_dec(v_numIndices_1603_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(lean_object* v_a_1612_, lean_object* v_numIndices_1613_, lean_object* v_as_1614_, lean_object* v_i_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v_zero_1624_; uint8_t v_isZero_1625_; 
v_zero_1624_ = lean_unsigned_to_nat(0u);
v_isZero_1625_ = lean_nat_dec_eq(v_i_1615_, v_zero_1624_);
if (v_isZero_1625_ == 1)
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
lean_dec(v_i_1615_);
lean_dec_ref(v_a_1612_);
v___x_1626_ = lean_box(0);
v___x_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
return v___x_1627_;
}
else
{
lean_object* v_one_1628_; lean_object* v_n_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v_one_1628_ = lean_unsigned_to_nat(1u);
v_n_1629_ = lean_nat_sub(v_i_1615_, v_one_1628_);
lean_dec(v_i_1615_);
v___x_1630_ = lean_array_fget_borrowed(v_as_1614_, v_n_1629_);
lean_inc_ref(v_a_1612_);
v___x_1631_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_a_1612_, v_numIndices_1613_, v___x_1630_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_a_1632_);
if (lean_obj_tag(v_a_1632_) == 0)
{
lean_dec_ref_known(v___x_1631_, 1);
v_i_1615_ = v_n_1629_;
goto _start;
}
else
{
lean_dec_ref_known(v_a_1632_, 1);
lean_dec(v_n_1629_);
lean_dec_ref(v_a_1612_);
return v___x_1631_;
}
}
else
{
lean_dec(v_n_1629_);
lean_dec_ref(v_a_1612_);
return v___x_1631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(lean_object* v_a_1634_, lean_object* v_numIndices_1635_, lean_object* v_x_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
if (lean_obj_tag(v_x_1636_) == 0)
{
lean_object* v_cs_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v_cs_1645_ = lean_ctor_get(v_x_1636_, 0);
v___x_1646_ = lean_array_get_size(v_cs_1645_);
v___x_1647_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_a_1634_, v_numIndices_1635_, v_cs_1645_, v___x_1646_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
return v___x_1647_;
}
else
{
lean_object* v_vs_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v_vs_1648_ = lean_ctor_get(v_x_1636_, 0);
v___x_1649_ = lean_array_get_size(v_vs_1648_);
v___x_1650_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_a_1634_, v_numIndices_1635_, v_vs_1648_, v___x_1649_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
return v___x_1650_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3___boxed(lean_object* v_a_1651_, lean_object* v_numIndices_1652_, lean_object* v_x_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_a_1651_, v_numIndices_1652_, v_x_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec_ref(v_x_1653_);
lean_dec(v_numIndices_1652_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_a_1663_, lean_object* v_numIndices_1664_, lean_object* v_as_1665_, lean_object* v_i_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_a_1663_, v_numIndices_1664_, v_as_1665_, v_i_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v_as_1665_);
lean_dec(v_numIndices_1664_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(lean_object* v_a_1676_, lean_object* v_numIndices_1677_, lean_object* v_t_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v_root_1687_; lean_object* v_tail_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v_root_1687_ = lean_ctor_get(v_t_1678_, 0);
v_tail_1688_ = lean_ctor_get(v_t_1678_, 1);
v___x_1689_ = lean_array_get_size(v_tail_1688_);
lean_inc_ref(v_a_1676_);
v___x_1690_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_a_1676_, v_numIndices_1677_, v_tail_1688_, v___x_1689_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_a_1691_);
if (lean_obj_tag(v_a_1691_) == 0)
{
lean_object* v___x_1692_; 
lean_dec_ref_known(v___x_1690_, 1);
v___x_1692_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_a_1676_, v_numIndices_1677_, v_root_1687_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
return v___x_1692_;
}
else
{
lean_dec_ref_known(v_a_1691_, 1);
lean_dec_ref(v_a_1676_);
return v___x_1690_;
}
}
else
{
lean_dec_ref(v_a_1676_);
return v___x_1690_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1___boxed(lean_object* v_a_1693_, lean_object* v_numIndices_1694_, lean_object* v_t_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(v_a_1693_, v_numIndices_1694_, v_t_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v_t_1695_);
lean_dec(v_numIndices_1694_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(lean_object* v_a_1705_, lean_object* v_numIndices_1706_, lean_object* v_lctx_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v_decls_1716_; lean_object* v___x_1717_; 
v_decls_1716_ = lean_ctor_get(v_lctx_1707_, 1);
v___x_1717_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(v_a_1705_, v_numIndices_1706_, v_decls_1716_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1___boxed(lean_object* v_a_1718_, lean_object* v_numIndices_1719_, lean_object* v_lctx_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(v_a_1718_, v_numIndices_1719_, v_lctx_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v_lctx_1720_);
lean_dec(v_numIndices_1719_);
return v_res_1729_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3(void){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1735_ = lean_box(0);
v___x_1736_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2));
v___x_1737_ = l_Lean_mkConst(v___x_1736_, v___x_1735_);
return v___x_1737_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6(void){
_start:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1741_ = lean_box(0);
v___x_1742_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__5));
v___x_1743_ = l_Lean_mkConst(v___x_1742_, v___x_1741_);
return v___x_1743_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7(void){
_start:
{
uint8_t v___x_1744_; uint64_t v___x_1745_; 
v___x_1744_ = 1;
v___x_1745_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1744_);
return v___x_1745_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11(void){
_start:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1752_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10));
v___x_1753_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4));
v___x_1754_ = l_Lean_Name_append(v___x_1753_, v___x_1752_);
return v___x_1754_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13(void){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1756_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12));
v___x_1757_ = l_Lean_stringToMessageData(v___x_1756_);
return v___x_1757_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__15(void){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14));
v___x_1760_ = l_Lean_stringToMessageData(v___x_1759_);
return v___x_1760_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__18(void){
_start:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17));
v___x_1765_ = l_Lean_MessageData_ofFormat(v___x_1764_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(lean_object* v_numIndices_1766_, uint8_t v_useDecide_1767_, lean_object* v_prop_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v___x_1777_; lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1939_; 
v___x_1777_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_prop_1768_, v_a_1773_);
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1780_ = v___x_1777_;
v_isShared_1781_ = v_isSharedCheck_1939_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1939_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v_a_1802_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v_options_1907_; uint8_t v_hasTrace_1908_; 
v_options_1907_ = lean_ctor_get(v_a_1774_, 2);
v_hasTrace_1908_ = lean_ctor_get_uint8(v_options_1907_, sizeof(void*)*1);
if (v_hasTrace_1908_ == 0)
{
v___y_1830_ = v_a_1769_;
v___y_1831_ = v_a_1770_;
v___y_1832_ = v_a_1771_;
v___y_1833_ = v_a_1772_;
v___y_1834_ = v_a_1773_;
v___y_1835_ = v_a_1774_;
v___y_1836_ = v_a_1775_;
goto v___jp_1829_;
}
else
{
lean_object* v_inheritedTraceOptions_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; uint8_t v___x_1912_; 
v_inheritedTraceOptions_1909_ = lean_ctor_get(v_a_1774_, 13);
v___x_1910_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10));
v___x_1911_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11);
v___x_1912_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1909_, v_options_1907_, v___x_1911_);
if (v___x_1912_ == 0)
{
v___y_1830_ = v_a_1769_;
v___y_1831_ = v_a_1770_;
v___y_1832_ = v_a_1771_;
v___y_1833_ = v_a_1772_;
v___y_1834_ = v_a_1773_;
v___y_1835_ = v_a_1774_;
v___y_1836_ = v_a_1775_;
goto v___jp_1829_;
}
else
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___y_1919_; lean_object* v___x_1932_; lean_object* v___x_1933_; uint8_t v___x_1934_; 
v___x_1913_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13);
lean_inc(v_a_1778_);
v___x_1914_ = l_Lean_MessageData_ofExpr(v_a_1778_);
v___x_1915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1913_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__15, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__15_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__15);
v___x_1917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1915_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1932_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__1));
v___x_1933_ = lean_unsigned_to_nat(1u);
v___x_1934_ = l_Lean_Expr_isAppOfArity(v_a_1778_, v___x_1932_, v___x_1933_);
if (v___x_1934_ == 0)
{
goto v___jp_1930_;
}
else
{
lean_object* v___x_1935_; uint8_t v___x_1936_; 
v___x_1935_ = l_Lean_Expr_appArg_x21(v_a_1778_);
v___x_1936_ = l_Lean_Expr_isAppOfArity(v___x_1935_, v___x_1932_, v___x_1933_);
if (v___x_1936_ == 0)
{
lean_dec_ref(v___x_1935_);
goto v___jp_1930_;
}
else
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1937_ = l_Lean_Expr_appArg_x21(v___x_1935_);
lean_dec_ref(v___x_1935_);
v___x_1938_ = l_Lean_MessageData_ofExpr(v___x_1937_);
v___y_1919_ = v___x_1938_;
goto v___jp_1918_;
}
}
v___jp_1918_:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1917_);
lean_ctor_set(v___x_1920_, 1, v___y_1919_);
v___x_1921_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v___x_1910_, v___x_1920_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_dec_ref_known(v___x_1921_, 1);
v___y_1830_ = v_a_1769_;
v___y_1831_ = v_a_1770_;
v___y_1832_ = v_a_1771_;
v___y_1833_ = v_a_1772_;
v___y_1834_ = v_a_1773_;
v___y_1835_ = v_a_1774_;
v___y_1836_ = v_a_1775_;
goto v___jp_1829_;
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
lean_del_object(v___x_1780_);
lean_dec(v_a_1778_);
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1921_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1921_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
v___jp_1930_:
{
lean_object* v___x_1931_; 
v___x_1931_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__18, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__18_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__18);
v___y_1919_ = v___x_1931_;
goto v___jp_1918_;
}
}
}
v___jp_1782_:
{
lean_object* v_lctx_1790_; lean_object* v___x_1791_; 
v_lctx_1790_ = lean_ctor_get(v___y_1786_, 2);
v___x_1791_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(v_a_1778_, v_numIndices_1766_, v_lctx_1790_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
return v___x_1791_;
}
v___jp_1792_:
{
lean_object* v___x_1803_; uint8_t v___x_1804_; 
v___x_1803_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2));
v___x_1804_ = l_Lean_Expr_isConstOf(v_a_1802_, v___x_1803_);
lean_dec_ref(v_a_1802_);
if (v___x_1804_ == 0)
{
lean_dec_ref(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_del_object(v___x_1780_);
v___y_1783_ = v___y_1793_;
v___y_1784_ = v___y_1801_;
v___y_1785_ = v___y_1800_;
v___y_1786_ = v___y_1794_;
v___y_1787_ = v___y_1799_;
v___y_1788_ = v___y_1798_;
v___y_1789_ = v___y_1795_;
goto v___jp_1782_;
}
else
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
lean_dec(v_a_1778_);
v___x_1805_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3);
v___x_1806_ = l_Lean_Meta_mkEqRefl(v___x_1805_, v___y_1794_, v___y_1799_, v___y_1798_, v___y_1795_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1820_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1809_ = v___x_1806_;
v_isShared_1810_ = v_isSharedCheck_1820_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1806_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1820_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1815_; 
v___x_1811_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6);
v___x_1812_ = l_Lean_Expr_appArg_x21(v___y_1796_);
lean_dec_ref(v___y_1796_);
v___x_1813_ = l_Lean_mkApp3(v___x_1811_, v___y_1797_, v___x_1812_, v_a_1807_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set_tag(v___x_1780_, 1);
lean_ctor_set(v___x_1780_, 0, v___x_1813_);
v___x_1815_ = v___x_1780_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
lean_object* v___x_1817_; 
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v___x_1815_);
v___x_1817_ = v___x_1809_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1815_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
else
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
lean_dec_ref(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_del_object(v___x_1780_);
v_a_1821_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1806_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1806_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
}
v___jp_1829_:
{
if (v_useDecide_1767_ == 0)
{
lean_del_object(v___x_1780_);
v___y_1783_ = v___y_1830_;
v___y_1784_ = v___y_1831_;
v___y_1785_ = v___y_1832_;
v___y_1786_ = v___y_1833_;
v___y_1787_ = v___y_1834_;
v___y_1788_ = v___y_1835_;
v___y_1789_ = v___y_1836_;
goto v___jp_1782_;
}
else
{
lean_object* v___x_1837_; lean_object* v_a_1838_; uint8_t v___x_1839_; 
lean_inc(v_a_1778_);
v___x_1837_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_a_1778_, v___y_1834_);
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_a_1838_);
lean_dec_ref(v___x_1837_);
v___x_1839_ = l_Lean_Expr_hasFVar(v_a_1838_);
if (v___x_1839_ == 0)
{
uint8_t v___x_1840_; 
v___x_1840_ = l_Lean_Expr_hasMVar(v_a_1838_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; 
lean_inc(v_a_1838_);
v___x_1841_ = l_Lean_Meta_mkDecide(v_a_1838_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1843_; uint8_t v_foApprox_1844_; uint8_t v_ctxApprox_1845_; uint8_t v_quasiPatternApprox_1846_; uint8_t v_constApprox_1847_; uint8_t v_isDefEqStuckEx_1848_; uint8_t v_unificationHints_1849_; uint8_t v_proofIrrelevance_1850_; uint8_t v_assignSyntheticOpaque_1851_; uint8_t v_offsetCnstrs_1852_; uint8_t v_etaStruct_1853_; uint8_t v_univApprox_1854_; uint8_t v_iota_1855_; uint8_t v_beta_1856_; uint8_t v_proj_1857_; uint8_t v_zeta_1858_; uint8_t v_zetaDelta_1859_; uint8_t v_zetaUnused_1860_; uint8_t v_zetaHave_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1898_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
lean_dec_ref_known(v___x_1841_, 1);
v___x_1843_ = l_Lean_Meta_Context_config(v___y_1833_);
v_foApprox_1844_ = lean_ctor_get_uint8(v___x_1843_, 0);
v_ctxApprox_1845_ = lean_ctor_get_uint8(v___x_1843_, 1);
v_quasiPatternApprox_1846_ = lean_ctor_get_uint8(v___x_1843_, 2);
v_constApprox_1847_ = lean_ctor_get_uint8(v___x_1843_, 3);
v_isDefEqStuckEx_1848_ = lean_ctor_get_uint8(v___x_1843_, 4);
v_unificationHints_1849_ = lean_ctor_get_uint8(v___x_1843_, 5);
v_proofIrrelevance_1850_ = lean_ctor_get_uint8(v___x_1843_, 6);
v_assignSyntheticOpaque_1851_ = lean_ctor_get_uint8(v___x_1843_, 7);
v_offsetCnstrs_1852_ = lean_ctor_get_uint8(v___x_1843_, 8);
v_etaStruct_1853_ = lean_ctor_get_uint8(v___x_1843_, 10);
v_univApprox_1854_ = lean_ctor_get_uint8(v___x_1843_, 11);
v_iota_1855_ = lean_ctor_get_uint8(v___x_1843_, 12);
v_beta_1856_ = lean_ctor_get_uint8(v___x_1843_, 13);
v_proj_1857_ = lean_ctor_get_uint8(v___x_1843_, 14);
v_zeta_1858_ = lean_ctor_get_uint8(v___x_1843_, 15);
v_zetaDelta_1859_ = lean_ctor_get_uint8(v___x_1843_, 16);
v_zetaUnused_1860_ = lean_ctor_get_uint8(v___x_1843_, 17);
v_zetaHave_1861_ = lean_ctor_get_uint8(v___x_1843_, 18);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1863_ = v___x_1843_;
v_isShared_1864_ = v_isSharedCheck_1898_;
goto v_resetjp_1862_;
}
else
{
lean_dec(v___x_1843_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1898_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
uint8_t v_trackZetaDelta_1865_; lean_object* v_zetaDeltaSet_1866_; lean_object* v_lctx_1867_; lean_object* v_localInstances_1868_; lean_object* v_defEqCtx_x3f_1869_; lean_object* v_synthPendingDepth_1870_; lean_object* v_canUnfold_x3f_1871_; uint8_t v_univApprox_1872_; uint8_t v_inTypeClassResolution_1873_; uint8_t v_cacheInferType_1874_; uint8_t v___x_1875_; lean_object* v_config_1877_; 
v_trackZetaDelta_1865_ = lean_ctor_get_uint8(v___y_1833_, sizeof(void*)*7);
v_zetaDeltaSet_1866_ = lean_ctor_get(v___y_1833_, 1);
v_lctx_1867_ = lean_ctor_get(v___y_1833_, 2);
v_localInstances_1868_ = lean_ctor_get(v___y_1833_, 3);
v_defEqCtx_x3f_1869_ = lean_ctor_get(v___y_1833_, 4);
v_synthPendingDepth_1870_ = lean_ctor_get(v___y_1833_, 5);
v_canUnfold_x3f_1871_ = lean_ctor_get(v___y_1833_, 6);
v_univApprox_1872_ = lean_ctor_get_uint8(v___y_1833_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1873_ = lean_ctor_get_uint8(v___y_1833_, sizeof(void*)*7 + 2);
v_cacheInferType_1874_ = lean_ctor_get_uint8(v___y_1833_, sizeof(void*)*7 + 3);
v___x_1875_ = 1;
if (v_isShared_1864_ == 0)
{
v_config_1877_ = v___x_1863_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, 0, v_foApprox_1844_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, 1, v_ctxApprox_1845_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, 2, v_quasiPatternApprox_1846_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, 3, v_constApprox_1847_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, 4, v_isDefEqStuckEx_1848_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, 5, v_unificationHints_1849_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, 6, v_proofIrrelevance_1850_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, 7, v_assignSyntheticOpaque_1851_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, 8, v_offsetCnstrs_1852_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, 10, v_etaStruct_1853_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, 11, v_univApprox_1854_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, 12, v_iota_1855_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, 13, v_beta_1856_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, 14, v_proj_1857_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, 15, v_zeta_1858_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, 16, v_zetaDelta_1859_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, 17, v_zetaUnused_1860_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, 18, v_zetaHave_1861_);
v_config_1877_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
uint64_t v___x_1878_; uint64_t v___x_1879_; uint64_t v___x_1880_; uint64_t v___x_1881_; uint64_t v___x_1882_; uint64_t v_key_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
lean_ctor_set_uint8(v_config_1877_, 9, v___x_1875_);
v___x_1878_ = l_Lean_Meta_Context_configKey(v___y_1833_);
v___x_1879_ = 3ULL;
v___x_1880_ = lean_uint64_shift_right(v___x_1878_, v___x_1879_);
v___x_1881_ = lean_uint64_shift_left(v___x_1880_, v___x_1879_);
v___x_1882_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7);
v_key_1883_ = lean_uint64_lor(v___x_1881_, v___x_1882_);
v___x_1884_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1884_, 0, v_config_1877_);
lean_ctor_set_uint64(v___x_1884_, sizeof(void*)*1, v_key_1883_);
lean_inc(v_canUnfold_x3f_1871_);
lean_inc(v_synthPendingDepth_1870_);
lean_inc(v_defEqCtx_x3f_1869_);
lean_inc_ref(v_localInstances_1868_);
lean_inc_ref(v_lctx_1867_);
lean_inc(v_zetaDeltaSet_1866_);
v___x_1885_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
lean_ctor_set(v___x_1885_, 1, v_zetaDeltaSet_1866_);
lean_ctor_set(v___x_1885_, 2, v_lctx_1867_);
lean_ctor_set(v___x_1885_, 3, v_localInstances_1868_);
lean_ctor_set(v___x_1885_, 4, v_defEqCtx_x3f_1869_);
lean_ctor_set(v___x_1885_, 5, v_synthPendingDepth_1870_);
lean_ctor_set(v___x_1885_, 6, v_canUnfold_x3f_1871_);
lean_ctor_set_uint8(v___x_1885_, sizeof(void*)*7, v_trackZetaDelta_1865_);
lean_ctor_set_uint8(v___x_1885_, sizeof(void*)*7 + 1, v_univApprox_1872_);
lean_ctor_set_uint8(v___x_1885_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1873_);
lean_ctor_set_uint8(v___x_1885_, sizeof(void*)*7 + 3, v_cacheInferType_1874_);
lean_inc(v___y_1836_);
lean_inc_ref(v___y_1835_);
lean_inc(v___y_1834_);
lean_inc(v_a_1842_);
v___x_1886_ = lean_whnf(v_a_1842_, v___x_1885_, v___y_1834_, v___y_1835_, v___y_1836_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_a_1887_);
lean_dec_ref_known(v___x_1886_, 1);
v___y_1793_ = v___y_1830_;
v___y_1794_ = v___y_1833_;
v___y_1795_ = v___y_1836_;
v___y_1796_ = v_a_1842_;
v___y_1797_ = v_a_1838_;
v___y_1798_ = v___y_1835_;
v___y_1799_ = v___y_1834_;
v___y_1800_ = v___y_1832_;
v___y_1801_ = v___y_1831_;
v_a_1802_ = v_a_1887_;
goto v___jp_1792_;
}
else
{
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1888_; 
v_a_1888_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_a_1888_);
lean_dec_ref_known(v___x_1886_, 1);
v___y_1793_ = v___y_1830_;
v___y_1794_ = v___y_1833_;
v___y_1795_ = v___y_1836_;
v___y_1796_ = v_a_1842_;
v___y_1797_ = v_a_1838_;
v___y_1798_ = v___y_1835_;
v___y_1799_ = v___y_1834_;
v___y_1800_ = v___y_1832_;
v___y_1801_ = v___y_1831_;
v_a_1802_ = v_a_1888_;
goto v___jp_1792_;
}
else
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
lean_dec(v_a_1842_);
lean_dec(v_a_1838_);
lean_del_object(v___x_1780_);
lean_dec(v_a_1778_);
v_a_1889_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1891_ = v___x_1886_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1886_);
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
}
}
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_dec(v_a_1838_);
lean_del_object(v___x_1780_);
lean_dec(v_a_1778_);
v_a_1899_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1841_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1841_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
else
{
lean_dec(v_a_1838_);
lean_del_object(v___x_1780_);
v___y_1783_ = v___y_1830_;
v___y_1784_ = v___y_1831_;
v___y_1785_ = v___y_1832_;
v___y_1786_ = v___y_1833_;
v___y_1787_ = v___y_1834_;
v___y_1788_ = v___y_1835_;
v___y_1789_ = v___y_1836_;
goto v___jp_1782_;
}
}
else
{
lean_dec(v_a_1838_);
lean_del_object(v___x_1780_);
v___y_1783_ = v___y_1830_;
v___y_1784_ = v___y_1831_;
v___y_1785_ = v___y_1832_;
v___y_1786_ = v___y_1833_;
v___y_1787_ = v___y_1834_;
v___y_1788_ = v___y_1835_;
v___y_1789_ = v___y_1836_;
goto v___jp_1782_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___boxed(lean_object* v_numIndices_1940_, lean_object* v_useDecide_1941_, lean_object* v_prop_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_){
_start:
{
uint8_t v_useDecide_boxed_1951_; lean_object* v_res_1952_; 
v_useDecide_boxed_1951_ = lean_unbox(v_useDecide_1941_);
v_res_1952_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_1940_, v_useDecide_boxed_1951_, v_prop_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_);
lean_dec(v_a_1949_);
lean_dec_ref(v_a_1948_);
lean_dec(v_a_1947_);
lean_dec_ref(v_a_1946_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
lean_dec(v_a_1943_);
lean_dec(v_numIndices_1940_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2(lean_object* v_cls_1953_, lean_object* v_msg_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v_cls_1953_, v_msg_1954_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___boxed(lean_object* v_cls_1964_, lean_object* v_msg_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2(v_cls_1964_, v_msg_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2(lean_object* v_a_1975_, lean_object* v_numIndices_1976_, lean_object* v_as_1977_, lean_object* v_i_1978_, lean_object* v_a_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_a_1975_, v_numIndices_1976_, v_as_1977_, v_i_1978_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_a_1989_, lean_object* v_numIndices_1990_, lean_object* v_as_1991_, lean_object* v_i_1992_, lean_object* v_a_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2(v_a_1989_, v_numIndices_1990_, v_as_1991_, v_i_1992_, v_a_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v_as_1991_);
lean_dec(v_numIndices_1990_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5(lean_object* v_a_2003_, lean_object* v_numIndices_2004_, lean_object* v_as_2005_, lean_object* v_i_2006_, lean_object* v_a_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
lean_object* v___x_2016_; 
v___x_2016_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_a_2003_, v_numIndices_2004_, v_as_2005_, v_i_2006_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_a_2017_, lean_object* v_numIndices_2018_, lean_object* v_as_2019_, lean_object* v_i_2020_, lean_object* v_a_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5(v_a_2017_, v_numIndices_2018_, v_as_2019_, v_i_2020_, v_a_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v_as_2019_);
lean_dec(v_numIndices_2018_);
return v_res_2030_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3(void){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2036_ = lean_box(0);
v___x_2037_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__2));
v___x_2038_ = l_Lean_mkConst(v___x_2037_, v___x_2036_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27(lean_object* v_numIndices_2042_, uint8_t v_useDecideBool_2043_, lean_object* v_e_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_){
_start:
{
lean_object* v___x_2053_; 
lean_inc_ref(v_e_2044_);
v___x_2053_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2044_, v_a_2049_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2234_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2056_ = v___x_2053_;
v_isShared_2057_ = v_isSharedCheck_2234_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2053_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2234_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2063_; uint8_t v___x_2064_; 
v___x_2063_ = l_Lean_Expr_cleanupAnnotations(v_a_2054_);
v___x_2064_ = l_Lean_Expr_isApp(v___x_2063_);
if (v___x_2064_ == 0)
{
lean_dec_ref(v___x_2063_);
lean_dec_ref(v_e_2044_);
goto v___jp_2058_;
}
else
{
lean_object* v_arg_2065_; lean_object* v___x_2066_; uint8_t v___x_2067_; 
v_arg_2065_ = lean_ctor_get(v___x_2063_, 1);
lean_inc_ref(v_arg_2065_);
v___x_2066_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2063_);
v___x_2067_ = l_Lean_Expr_isApp(v___x_2066_);
if (v___x_2067_ == 0)
{
lean_dec_ref(v___x_2066_);
lean_dec_ref(v_arg_2065_);
lean_dec_ref(v_e_2044_);
goto v___jp_2058_;
}
else
{
lean_object* v_arg_2068_; lean_object* v___x_2069_; uint8_t v___x_2070_; 
v_arg_2068_ = lean_ctor_get(v___x_2066_, 1);
lean_inc_ref(v_arg_2068_);
v___x_2069_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2066_);
v___x_2070_ = l_Lean_Expr_isApp(v___x_2069_);
if (v___x_2070_ == 0)
{
lean_dec_ref(v___x_2069_);
lean_dec_ref(v_arg_2068_);
lean_dec_ref(v_arg_2065_);
lean_dec_ref(v_e_2044_);
goto v___jp_2058_;
}
else
{
lean_object* v_arg_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; 
v_arg_2071_ = lean_ctor_get(v___x_2069_, 1);
lean_inc_ref(v_arg_2071_);
v___x_2072_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2069_);
v___x_2073_ = l_Lean_Expr_isApp(v___x_2072_);
if (v___x_2073_ == 0)
{
lean_dec_ref(v___x_2072_);
lean_dec_ref(v_arg_2071_);
lean_dec_ref(v_arg_2068_);
lean_dec_ref(v_arg_2065_);
lean_dec_ref(v_e_2044_);
goto v___jp_2058_;
}
else
{
lean_object* v_arg_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; 
v_arg_2074_ = lean_ctor_get(v___x_2072_, 1);
lean_inc_ref(v_arg_2074_);
v___x_2075_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2072_);
v___x_2076_ = l_Lean_Expr_isApp(v___x_2075_);
if (v___x_2076_ == 0)
{
lean_dec_ref(v___x_2075_);
lean_dec_ref(v_arg_2074_);
lean_dec_ref(v_arg_2071_);
lean_dec_ref(v_arg_2068_);
lean_dec_ref(v_arg_2065_);
lean_dec_ref(v_e_2044_);
goto v___jp_2058_;
}
else
{
lean_object* v_arg_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; 
v_arg_2077_ = lean_ctor_get(v___x_2075_, 1);
lean_inc_ref(v_arg_2077_);
v___x_2078_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2075_);
v___x_2079_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__2));
v___x_2080_ = l_Lean_Expr_isConstOf(v___x_2078_, v___x_2079_);
if (v___x_2080_ == 0)
{
lean_dec_ref(v___x_2078_);
lean_dec_ref(v_arg_2077_);
lean_dec_ref(v_arg_2074_);
lean_dec_ref(v_arg_2071_);
lean_dec_ref(v_arg_2068_);
lean_dec_ref(v_arg_2065_);
lean_dec_ref(v_e_2044_);
goto v___jp_2058_;
}
else
{
lean_object* v___x_2081_; 
lean_del_object(v___x_2056_);
lean_inc_ref(v_arg_2074_);
v___x_2081_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2042_, v_useDecideBool_2043_, v_arg_2074_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2225_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2084_ = v___x_2081_;
v_isShared_2085_ = v_isSharedCheck_2225_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2081_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2225_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2086_; 
v___x_2086_ = l_Lean_Expr_constLevels_x21(v___x_2078_);
if (lean_obj_tag(v_a_2082_) == 1)
{
lean_object* v_val_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2102_; 
lean_dec_ref(v___x_2078_);
lean_dec_ref(v_e_2044_);
v_val_2087_ = lean_ctor_get(v_a_2082_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v_a_2082_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2089_ = v_a_2082_;
v_isShared_2090_ = v_isSharedCheck_2102_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_val_2087_);
lean_dec(v_a_2082_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2102_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2095_; 
v___x_2091_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__7));
v___x_2092_ = l_Lean_mkConst(v___x_2091_, v___x_2086_);
lean_inc_ref(v_arg_2068_);
v___x_2093_ = l_Lean_mkApp6(v___x_2092_, v_arg_2074_, v_arg_2071_, v_val_2087_, v_arg_2077_, v_arg_2068_, v_arg_2065_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 0, v___x_2093_);
v___x_2095_ = v___x_2089_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_2093_);
v___x_2095_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2099_; 
v___x_2096_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2096_, 0, v_arg_2068_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
lean_ctor_set_uint8(v___x_2096_, sizeof(void*)*2, v___x_2080_);
v___x_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 0, v___x_2097_);
v___x_2099_ = v___x_2084_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2097_);
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
else
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
lean_del_object(v___x_2084_);
lean_dec(v_a_2082_);
lean_inc_ref(v_arg_2074_);
v___x_2103_ = l_Lean_mkNot(v_arg_2074_);
v___x_2104_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2042_, v_useDecideBool_2043_, v___x_2103_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2216_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2107_ = v___x_2104_;
v_isShared_2108_ = v_isSharedCheck_2216_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2104_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2216_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
if (lean_obj_tag(v_a_2105_) == 1)
{
lean_object* v_val_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2124_; 
lean_dec_ref(v___x_2078_);
lean_dec_ref(v_e_2044_);
v_val_2109_ = lean_ctor_get(v_a_2105_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v_a_2105_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2111_ = v_a_2105_;
v_isShared_2112_ = v_isSharedCheck_2124_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_val_2109_);
lean_dec(v_a_2105_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2124_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2117_; 
v___x_2113_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__9));
v___x_2114_ = l_Lean_mkConst(v___x_2113_, v___x_2086_);
lean_inc_ref(v_arg_2065_);
v___x_2115_ = l_Lean_mkApp6(v___x_2114_, v_arg_2074_, v_arg_2071_, v_val_2109_, v_arg_2077_, v_arg_2068_, v_arg_2065_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 0, v___x_2115_);
v___x_2117_ = v___x_2111_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2115_);
v___x_2117_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2121_; 
v___x_2118_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2118_, 0, v_arg_2065_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
lean_ctor_set_uint8(v___x_2118_, sizeof(void*)*2, v___x_2080_);
v___x_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 0, v___x_2119_);
v___x_2121_ = v___x_2107_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2119_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
else
{
lean_object* v___x_2125_; 
lean_del_object(v___x_2107_);
lean_dec(v_a_2105_);
lean_inc(v_a_2051_);
lean_inc_ref(v_a_2050_);
lean_inc(v_a_2049_);
lean_inc_ref(v_a_2048_);
lean_inc(v_a_2047_);
lean_inc_ref(v_a_2046_);
lean_inc(v_a_2045_);
lean_inc_ref(v_arg_2074_);
v___x_2125_ = lean_simp(v_arg_2074_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2207_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2128_ = v___x_2125_;
v_isShared_2129_ = v_isSharedCheck_2207_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2125_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2207_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v_expr_2130_; uint8_t v___x_2131_; 
v_expr_2130_ = lean_ctor_get(v_a_2126_, 0);
v___x_2131_ = lean_expr_eqv(v_expr_2130_, v_arg_2074_);
if (v___x_2131_ == 0)
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
lean_del_object(v___x_2128_);
v___x_2132_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3);
lean_inc_ref(v_expr_2130_);
v___x_2133_ = l_Lean_Expr_app___override(v___x_2132_, v_expr_2130_);
v___x_2134_ = lean_box(0);
v___x_2135_ = l_Lean_Meta_trySynthInstance(v___x_2133_, v___x_2134_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2184_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2184_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2184_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
if (lean_obj_tag(v_a_2136_) == 1)
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2170_; 
lean_inc_ref(v_expr_2130_);
lean_del_object(v___x_2138_);
lean_dec_ref(v_e_2044_);
v_a_2140_ = lean_ctor_get(v_a_2136_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v_a_2136_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2142_ = v_a_2136_;
v_isShared_2143_ = v_isSharedCheck_2170_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v_a_2136_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2170_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Lean_Meta_Simp_Result_getProof(v_a_2126_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2161_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2147_ = v___x_2144_;
v_isShared_2148_ = v_isSharedCheck_2161_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2144_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2161_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2154_; 
v___x_2149_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__5));
v___x_2150_ = l_Lean_mkConst(v___x_2149_, v___x_2086_);
lean_inc_ref(v_arg_2065_);
lean_inc_ref(v_arg_2068_);
lean_inc(v_a_2140_);
lean_inc_ref(v_expr_2130_);
lean_inc_ref(v_arg_2077_);
v___x_2151_ = l_Lean_mkApp8(v___x_2150_, v_arg_2077_, v_arg_2074_, v_expr_2130_, v_arg_2071_, v_a_2140_, v_arg_2068_, v_arg_2065_, v_a_2145_);
v___x_2152_ = l_Lean_mkApp5(v___x_2078_, v_arg_2077_, v_expr_2130_, v_a_2140_, v_arg_2068_, v_arg_2065_);
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 0, v___x_2151_);
v___x_2154_ = v___x_2142_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2151_);
v___x_2154_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2158_; 
v___x_2155_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2155_, 0, v___x_2152_);
lean_ctor_set(v___x_2155_, 1, v___x_2154_);
lean_ctor_set_uint8(v___x_2155_, sizeof(void*)*2, v___x_2080_);
v___x_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2155_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 0, v___x_2156_);
v___x_2158_ = v___x_2147_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_del_object(v___x_2142_);
lean_dec(v_a_2140_);
lean_dec_ref(v_expr_2130_);
lean_dec(v___x_2086_);
lean_dec_ref(v___x_2078_);
lean_dec_ref(v_arg_2077_);
lean_dec_ref(v_arg_2074_);
lean_dec_ref(v_arg_2071_);
lean_dec_ref(v_arg_2068_);
lean_dec_ref(v_arg_2065_);
v_a_2162_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2144_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2144_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
}
else
{
lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2181_; 
lean_dec(v_a_2136_);
lean_dec(v___x_2086_);
lean_dec_ref(v___x_2078_);
lean_dec_ref(v_arg_2077_);
lean_dec_ref(v_arg_2074_);
lean_dec_ref(v_arg_2071_);
lean_dec_ref(v_arg_2068_);
lean_dec_ref(v_arg_2065_);
v_isSharedCheck_2181_ = !lean_is_exclusive(v_a_2126_);
if (v_isSharedCheck_2181_ == 0)
{
lean_object* v_unused_2182_; lean_object* v_unused_2183_; 
v_unused_2182_ = lean_ctor_get(v_a_2126_, 1);
lean_dec(v_unused_2182_);
v_unused_2183_ = lean_ctor_get(v_a_2126_, 0);
lean_dec(v_unused_2183_);
v___x_2172_ = v_a_2126_;
v_isShared_2173_ = v_isSharedCheck_2181_;
goto v_resetjp_2171_;
}
else
{
lean_dec(v_a_2126_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2181_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 1, v___x_2134_);
lean_ctor_set(v___x_2172_, 0, v_e_2044_);
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_e_2044_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v___x_2134_);
v___x_2175_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
lean_object* v___x_2176_; lean_object* v___x_2178_; 
lean_ctor_set_uint8(v___x_2175_, sizeof(void*)*2, v___x_2080_);
v___x_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2175_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2176_);
v___x_2178_ = v___x_2138_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2176_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_dec(v_a_2126_);
lean_dec(v___x_2086_);
lean_dec_ref(v___x_2078_);
lean_dec_ref(v_arg_2077_);
lean_dec_ref(v_arg_2074_);
lean_dec_ref(v_arg_2071_);
lean_dec_ref(v_arg_2068_);
lean_dec_ref(v_arg_2065_);
lean_dec_ref(v_e_2044_);
v_a_2185_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2135_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2135_);
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
else
{
lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2204_; 
lean_dec(v___x_2086_);
lean_dec_ref(v___x_2078_);
lean_dec_ref(v_arg_2077_);
lean_dec_ref(v_arg_2074_);
lean_dec_ref(v_arg_2071_);
lean_dec_ref(v_arg_2068_);
lean_dec_ref(v_arg_2065_);
v_isSharedCheck_2204_ = !lean_is_exclusive(v_a_2126_);
if (v_isSharedCheck_2204_ == 0)
{
lean_object* v_unused_2205_; lean_object* v_unused_2206_; 
v_unused_2205_ = lean_ctor_get(v_a_2126_, 1);
lean_dec(v_unused_2205_);
v_unused_2206_ = lean_ctor_get(v_a_2126_, 0);
lean_dec(v_unused_2206_);
v___x_2194_ = v_a_2126_;
v_isShared_2195_ = v_isSharedCheck_2204_;
goto v_resetjp_2193_;
}
else
{
lean_dec(v_a_2126_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2204_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2196_; lean_object* v___x_2198_; 
v___x_2196_ = lean_box(0);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 1, v___x_2196_);
lean_ctor_set(v___x_2194_, 0, v_e_2044_);
v___x_2198_ = v___x_2194_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_e_2044_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v___x_2196_);
v___x_2198_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
lean_object* v___x_2199_; lean_object* v___x_2201_; 
lean_ctor_set_uint8(v___x_2198_, sizeof(void*)*2, v___x_2080_);
v___x_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2198_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 0, v___x_2199_);
v___x_2201_ = v___x_2128_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2199_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
}
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
lean_dec(v___x_2086_);
lean_dec_ref(v___x_2078_);
lean_dec_ref(v_arg_2077_);
lean_dec_ref(v_arg_2074_);
lean_dec_ref(v_arg_2071_);
lean_dec_ref(v_arg_2068_);
lean_dec_ref(v_arg_2065_);
lean_dec_ref(v_e_2044_);
v_a_2208_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2125_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2125_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
}
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec(v___x_2086_);
lean_dec_ref(v___x_2078_);
lean_dec_ref(v_arg_2077_);
lean_dec_ref(v_arg_2074_);
lean_dec_ref(v_arg_2071_);
lean_dec_ref(v_arg_2068_);
lean_dec_ref(v_arg_2065_);
lean_dec_ref(v_e_2044_);
v_a_2217_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2104_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2104_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
}
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
lean_dec_ref(v___x_2078_);
lean_dec_ref(v_arg_2077_);
lean_dec_ref(v_arg_2074_);
lean_dec_ref(v_arg_2071_);
lean_dec_ref(v_arg_2068_);
lean_dec_ref(v_arg_2065_);
lean_dec_ref(v_e_2044_);
v_a_2226_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2081_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2081_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
}
}
}
}
}
v___jp_2058_:
{
lean_object* v___x_2059_; lean_object* v___x_2061_; 
v___x_2059_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__0));
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 0, v___x_2059_);
v___x_2061_ = v___x_2056_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2059_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
else
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
lean_dec_ref(v_e_2044_);
v_a_2235_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v___x_2053_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2053_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___boxed(lean_object* v_numIndices_2243_, lean_object* v_useDecideBool_2244_, lean_object* v_e_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_){
_start:
{
uint8_t v_useDecideBool_boxed_2254_; lean_object* v_res_2255_; 
v_useDecideBool_boxed_2254_ = lean_unbox(v_useDecideBool_2244_);
v_res_2255_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27(v_numIndices_2243_, v_useDecideBool_boxed_2254_, v_e_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_);
lean_dec(v_a_2252_);
lean_dec_ref(v_a_2251_);
lean_dec(v_a_2250_);
lean_dec_ref(v_a_2249_);
lean_dec(v_a_2248_);
lean_dec_ref(v_a_2247_);
lean_dec(v_a_2246_);
lean_dec(v_numIndices_2243_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(lean_object* v_e_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_){
_start:
{
if (lean_obj_tag(v_e_2259_) == 6)
{
lean_object* v_binderName_2263_; lean_object* v___x_2264_; 
v_binderName_2263_ = lean_ctor_get(v_e_2259_, 0);
lean_inc(v_binderName_2263_);
v___x_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2264_, 0, v_binderName_2263_);
return v___x_2264_;
}
else
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2265_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__1));
v___x_2266_ = l_Lean_Core_mkFreshUserName(v___x_2265_, v_a_2260_, v_a_2261_);
return v___x_2266_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___boxed(lean_object* v_e_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_e_2267_, v_a_2268_, v_a_2269_);
lean_dec(v_a_2269_);
lean_dec_ref(v_a_2268_);
lean_dec_ref(v_e_2267_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName(lean_object* v_e_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_){
_start:
{
lean_object* v___x_2278_; 
v___x_2278_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_e_2272_, v_a_2275_, v_a_2276_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___boxed(lean_object* v_e_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName(v_e_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v_a_2283_);
lean_dec_ref(v_a_2282_);
lean_dec(v_a_2281_);
lean_dec_ref(v_a_2280_);
lean_dec_ref(v_e_2279_);
return v_res_2285_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3(void){
_start:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2291_ = lean_box(0);
v___x_2292_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__2));
v___x_2293_ = l_Lean_mkConst(v___x_2292_, v___x_2291_);
return v___x_2293_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4(void){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2294_ = lean_unsigned_to_nat(0u);
v___x_2295_ = l_Lean_mkBVar(v___x_2294_);
return v___x_2295_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7(void){
_start:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2300_ = lean_box(0);
v___x_2301_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__6));
v___x_2302_ = l_Lean_mkConst(v___x_2301_, v___x_2300_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27(lean_object* v_numIndices_2306_, uint8_t v_useDecideBool_2307_, lean_object* v_e_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_){
_start:
{
lean_object* v___x_2317_; 
lean_inc_ref(v_e_2308_);
v___x_2317_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2308_, v_a_2313_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2527_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2320_ = v___x_2317_;
v_isShared_2321_ = v_isSharedCheck_2527_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2317_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2527_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2327_; uint8_t v___x_2328_; 
v___x_2327_ = l_Lean_Expr_cleanupAnnotations(v_a_2318_);
v___x_2328_ = l_Lean_Expr_isApp(v___x_2327_);
if (v___x_2328_ == 0)
{
lean_dec_ref(v___x_2327_);
lean_dec_ref(v_e_2308_);
goto v___jp_2322_;
}
else
{
lean_object* v_arg_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; 
v_arg_2329_ = lean_ctor_get(v___x_2327_, 1);
lean_inc_ref(v_arg_2329_);
v___x_2330_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2327_);
v___x_2331_ = l_Lean_Expr_isApp(v___x_2330_);
if (v___x_2331_ == 0)
{
lean_dec_ref(v___x_2330_);
lean_dec_ref(v_arg_2329_);
lean_dec_ref(v_e_2308_);
goto v___jp_2322_;
}
else
{
lean_object* v_arg_2332_; lean_object* v___x_2333_; uint8_t v___x_2334_; 
v_arg_2332_ = lean_ctor_get(v___x_2330_, 1);
lean_inc_ref(v_arg_2332_);
v___x_2333_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2330_);
v___x_2334_ = l_Lean_Expr_isApp(v___x_2333_);
if (v___x_2334_ == 0)
{
lean_dec_ref(v___x_2333_);
lean_dec_ref(v_arg_2332_);
lean_dec_ref(v_arg_2329_);
lean_dec_ref(v_e_2308_);
goto v___jp_2322_;
}
else
{
lean_object* v_arg_2335_; lean_object* v___x_2336_; uint8_t v___x_2337_; 
v_arg_2335_ = lean_ctor_get(v___x_2333_, 1);
lean_inc_ref(v_arg_2335_);
v___x_2336_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2333_);
v___x_2337_ = l_Lean_Expr_isApp(v___x_2336_);
if (v___x_2337_ == 0)
{
lean_dec_ref(v___x_2336_);
lean_dec_ref(v_arg_2335_);
lean_dec_ref(v_arg_2332_);
lean_dec_ref(v_arg_2329_);
lean_dec_ref(v_e_2308_);
goto v___jp_2322_;
}
else
{
lean_object* v_arg_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; 
v_arg_2338_ = lean_ctor_get(v___x_2336_, 1);
lean_inc_ref(v_arg_2338_);
v___x_2339_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2336_);
v___x_2340_ = l_Lean_Expr_isApp(v___x_2339_);
if (v___x_2340_ == 0)
{
lean_dec_ref(v___x_2339_);
lean_dec_ref(v_arg_2338_);
lean_dec_ref(v_arg_2335_);
lean_dec_ref(v_arg_2332_);
lean_dec_ref(v_arg_2329_);
lean_dec_ref(v_e_2308_);
goto v___jp_2322_;
}
else
{
lean_object* v_arg_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; uint8_t v___x_2344_; 
v_arg_2341_ = lean_ctor_get(v___x_2339_, 1);
lean_inc_ref(v_arg_2341_);
v___x_2342_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2339_);
v___x_2343_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__4));
v___x_2344_ = l_Lean_Expr_isConstOf(v___x_2342_, v___x_2343_);
if (v___x_2344_ == 0)
{
lean_dec_ref(v___x_2342_);
lean_dec_ref(v_arg_2341_);
lean_dec_ref(v_arg_2338_);
lean_dec_ref(v_arg_2335_);
lean_dec_ref(v_arg_2332_);
lean_dec_ref(v_arg_2329_);
lean_dec_ref(v_e_2308_);
goto v___jp_2322_;
}
else
{
lean_object* v___x_2345_; 
lean_del_object(v___x_2320_);
lean_inc_ref(v_arg_2338_);
v___x_2345_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2306_, v_useDecideBool_2307_, v_arg_2338_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2518_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2348_ = v___x_2345_;
v_isShared_2349_ = v_isSharedCheck_2518_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2345_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2518_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2350_; 
v___x_2350_ = l_Lean_Expr_constLevels_x21(v___x_2342_);
if (lean_obj_tag(v_a_2346_) == 1)
{
lean_object* v_val_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2368_; 
lean_dec_ref(v___x_2342_);
lean_dec_ref(v_e_2308_);
v_val_2351_ = lean_ctor_get(v_a_2346_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v_a_2346_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2353_ = v_a_2346_;
v_isShared_2354_ = v_isSharedCheck_2368_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_val_2351_);
lean_dec(v_a_2346_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2368_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2361_; 
lean_inc(v_val_2351_);
lean_inc_ref(v_arg_2332_);
v___x_2355_ = l_Lean_Expr_app___override(v_arg_2332_, v_val_2351_);
v___x_2356_ = l_Lean_Expr_headBeta(v___x_2355_);
v___x_2357_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__11));
v___x_2358_ = l_Lean_mkConst(v___x_2357_, v___x_2350_);
v___x_2359_ = l_Lean_mkApp6(v___x_2358_, v_arg_2338_, v_arg_2335_, v_val_2351_, v_arg_2341_, v_arg_2332_, v_arg_2329_);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v___x_2359_);
v___x_2361_ = v___x_2353_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v___x_2359_);
v___x_2361_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2365_; 
v___x_2362_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2362_, 0, v___x_2356_);
lean_ctor_set(v___x_2362_, 1, v___x_2361_);
lean_ctor_set_uint8(v___x_2362_, sizeof(void*)*2, v___x_2344_);
v___x_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2362_);
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 0, v___x_2363_);
v___x_2365_ = v___x_2348_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2363_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
else
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
lean_del_object(v___x_2348_);
lean_dec(v_a_2346_);
lean_inc_ref(v_arg_2338_);
v___x_2369_ = l_Lean_mkNot(v_arg_2338_);
v___x_2370_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2306_, v_useDecideBool_2307_, v___x_2369_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2509_; 
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2373_ = v___x_2370_;
v_isShared_2374_ = v_isSharedCheck_2509_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2370_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2509_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
if (lean_obj_tag(v_a_2371_) == 1)
{
lean_object* v_val_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2392_; 
lean_dec_ref(v___x_2342_);
lean_dec_ref(v_e_2308_);
v_val_2375_ = lean_ctor_get(v_a_2371_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v_a_2371_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2377_ = v_a_2371_;
v_isShared_2378_ = v_isSharedCheck_2392_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_val_2375_);
lean_dec(v_a_2371_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2392_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2385_; 
lean_inc(v_val_2375_);
lean_inc_ref(v_arg_2329_);
v___x_2379_ = l_Lean_Expr_app___override(v_arg_2329_, v_val_2375_);
v___x_2380_ = l_Lean_Expr_headBeta(v___x_2379_);
v___x_2381_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__13));
v___x_2382_ = l_Lean_mkConst(v___x_2381_, v___x_2350_);
v___x_2383_ = l_Lean_mkApp6(v___x_2382_, v_arg_2338_, v_arg_2335_, v_val_2375_, v_arg_2341_, v_arg_2332_, v_arg_2329_);
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 0, v___x_2383_);
v___x_2385_ = v___x_2377_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2383_);
v___x_2385_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2389_; 
v___x_2386_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2386_, 0, v___x_2380_);
lean_ctor_set(v___x_2386_, 1, v___x_2385_);
lean_ctor_set_uint8(v___x_2386_, sizeof(void*)*2, v___x_2344_);
v___x_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 0, v___x_2387_);
v___x_2389_ = v___x_2373_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v___x_2387_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
else
{
lean_object* v___x_2393_; 
lean_del_object(v___x_2373_);
lean_dec(v_a_2371_);
lean_inc(v_a_2315_);
lean_inc_ref(v_a_2314_);
lean_inc(v_a_2313_);
lean_inc_ref(v_a_2312_);
lean_inc(v_a_2311_);
lean_inc_ref(v_a_2310_);
lean_inc(v_a_2309_);
lean_inc_ref(v_arg_2338_);
v___x_2393_ = lean_simp(v_arg_2338_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2500_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2396_ = v___x_2393_;
v_isShared_2397_ = v_isSharedCheck_2500_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2393_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2500_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v_expr_2398_; uint8_t v___x_2399_; 
v_expr_2398_ = lean_ctor_get(v_a_2394_, 0);
v___x_2399_ = lean_expr_eqv(v_expr_2398_, v_arg_2338_);
if (v___x_2399_ == 0)
{
lean_object* v___x_2400_; 
lean_inc_ref(v_expr_2398_);
lean_del_object(v___x_2396_);
v___x_2400_ = l_Lean_Meta_Simp_Result_getProof(v_a_2394_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_a_2401_);
lean_dec_ref_known(v___x_2400_, 1);
v___x_2402_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3);
lean_inc_ref(v_expr_2398_);
v___x_2403_ = l_Lean_Expr_app___override(v___x_2402_, v_expr_2398_);
v___x_2404_ = lean_box(0);
v___x_2405_ = l_Lean_Meta_trySynthInstance(v___x_2403_, v___x_2404_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2469_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2408_ = v___x_2405_;
v_isShared_2409_ = v_isSharedCheck_2469_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2405_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2469_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
if (lean_obj_tag(v_a_2406_) == 1)
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2463_; 
lean_del_object(v___x_2408_);
lean_dec_ref(v_e_2308_);
v_a_2410_ = lean_ctor_get(v_a_2406_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v_a_2406_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2412_ = v_a_2406_;
v_isShared_2413_ = v_isSharedCheck_2463_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v_a_2406_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2463_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2414_; 
v___x_2414_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_arg_2332_, v_a_2314_, v_a_2315_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; lean_object* v___x_2416_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_a_2415_);
lean_dec_ref_known(v___x_2414_, 1);
v___x_2416_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_arg_2329_, v_a_2314_, v_a_2315_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2446_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2419_ = v___x_2416_;
v_isShared_2420_ = v_isSharedCheck_2446_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2416_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2446_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; uint8_t v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2439_; 
v___x_2421_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3);
v___x_2422_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4);
lean_inc_n(v_a_2401_, 2);
lean_inc_ref_n(v_expr_2398_, 5);
lean_inc_ref_n(v_arg_2338_, 2);
v___x_2423_ = l_Lean_mkApp4(v___x_2421_, v_arg_2338_, v_expr_2398_, v_a_2401_, v___x_2422_);
lean_inc_ref(v_arg_2332_);
v___x_2424_ = l_Lean_Expr_app___override(v_arg_2332_, v___x_2423_);
v___x_2425_ = l_Lean_Expr_headBeta(v___x_2424_);
v___x_2426_ = 0;
v___x_2427_ = l_Lean_mkLambda(v_a_2415_, v___x_2426_, v_expr_2398_, v___x_2425_);
v___x_2428_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7);
v___x_2429_ = l_Lean_mkApp4(v___x_2428_, v_arg_2338_, v_expr_2398_, v_a_2401_, v___x_2422_);
lean_inc_ref(v_arg_2329_);
v___x_2430_ = l_Lean_Expr_app___override(v_arg_2329_, v___x_2429_);
v___x_2431_ = l_Lean_Expr_headBeta(v___x_2430_);
v___x_2432_ = l_Lean_mkNot(v_expr_2398_);
v___x_2433_ = l_Lean_mkLambda(v_a_2417_, v___x_2426_, v___x_2432_, v___x_2431_);
lean_inc(v_a_2410_);
lean_inc_ref(v_arg_2341_);
v___x_2434_ = l_Lean_mkApp5(v___x_2342_, v_arg_2341_, v_expr_2398_, v_a_2410_, v___x_2427_, v___x_2433_);
v___x_2435_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__9));
v___x_2436_ = l_Lean_mkConst(v___x_2435_, v___x_2350_);
v___x_2437_ = l_Lean_mkApp8(v___x_2436_, v_arg_2341_, v_arg_2338_, v_expr_2398_, v_arg_2335_, v_a_2410_, v_arg_2332_, v_arg_2329_, v_a_2401_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 0, v___x_2437_);
v___x_2439_ = v___x_2412_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2437_);
v___x_2439_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2443_; 
v___x_2440_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2440_, 0, v___x_2434_);
lean_ctor_set(v___x_2440_, 1, v___x_2439_);
lean_ctor_set_uint8(v___x_2440_, sizeof(void*)*2, v___x_2344_);
v___x_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2440_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 0, v___x_2441_);
v___x_2443_ = v___x_2419_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v___x_2441_);
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
else
{
lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2454_; 
lean_dec(v_a_2415_);
lean_del_object(v___x_2412_);
lean_dec(v_a_2410_);
lean_dec(v_a_2401_);
lean_dec_ref(v_expr_2398_);
lean_dec(v___x_2350_);
lean_dec_ref(v___x_2342_);
lean_dec_ref(v_arg_2341_);
lean_dec_ref(v_arg_2338_);
lean_dec_ref(v_arg_2335_);
lean_dec_ref(v_arg_2332_);
lean_dec_ref(v_arg_2329_);
v_a_2447_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2449_ = v___x_2416_;
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_dec(v___x_2416_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2452_; 
if (v_isShared_2450_ == 0)
{
v___x_2452_ = v___x_2449_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2447_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
else
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
lean_del_object(v___x_2412_);
lean_dec(v_a_2410_);
lean_dec(v_a_2401_);
lean_dec_ref(v_expr_2398_);
lean_dec(v___x_2350_);
lean_dec_ref(v___x_2342_);
lean_dec_ref(v_arg_2341_);
lean_dec_ref(v_arg_2338_);
lean_dec_ref(v_arg_2335_);
lean_dec_ref(v_arg_2332_);
lean_dec_ref(v_arg_2329_);
v_a_2455_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2457_ = v___x_2414_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2414_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
if (v_isShared_2458_ == 0)
{
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2455_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
}
else
{
lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2467_; 
lean_dec(v_a_2406_);
lean_dec(v_a_2401_);
lean_dec_ref(v_expr_2398_);
lean_dec(v___x_2350_);
lean_dec_ref(v___x_2342_);
lean_dec_ref(v_arg_2341_);
lean_dec_ref(v_arg_2338_);
lean_dec_ref(v_arg_2335_);
lean_dec_ref(v_arg_2332_);
lean_dec_ref(v_arg_2329_);
v___x_2464_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2464_, 0, v_e_2308_);
lean_ctor_set(v___x_2464_, 1, v___x_2404_);
lean_ctor_set_uint8(v___x_2464_, sizeof(void*)*2, v___x_2344_);
v___x_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2464_);
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 0, v___x_2465_);
v___x_2467_ = v___x_2408_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v___x_2465_);
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
lean_dec(v_a_2401_);
lean_dec_ref(v_expr_2398_);
lean_dec(v___x_2350_);
lean_dec_ref(v___x_2342_);
lean_dec_ref(v_arg_2341_);
lean_dec_ref(v_arg_2338_);
lean_dec_ref(v_arg_2335_);
lean_dec_ref(v_arg_2332_);
lean_dec_ref(v_arg_2329_);
lean_dec_ref(v_e_2308_);
v_a_2470_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2405_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2405_);
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
else
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_dec_ref(v_expr_2398_);
lean_dec(v___x_2350_);
lean_dec_ref(v___x_2342_);
lean_dec_ref(v_arg_2341_);
lean_dec_ref(v_arg_2338_);
lean_dec_ref(v_arg_2335_);
lean_dec_ref(v_arg_2332_);
lean_dec_ref(v_arg_2329_);
lean_dec_ref(v_e_2308_);
v_a_2478_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___x_2400_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2400_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2478_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
else
{
lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2497_; 
lean_dec(v___x_2350_);
lean_dec_ref(v___x_2342_);
lean_dec_ref(v_arg_2341_);
lean_dec_ref(v_arg_2338_);
lean_dec_ref(v_arg_2335_);
lean_dec_ref(v_arg_2332_);
lean_dec_ref(v_arg_2329_);
v_isSharedCheck_2497_ = !lean_is_exclusive(v_a_2394_);
if (v_isSharedCheck_2497_ == 0)
{
lean_object* v_unused_2498_; lean_object* v_unused_2499_; 
v_unused_2498_ = lean_ctor_get(v_a_2394_, 1);
lean_dec(v_unused_2498_);
v_unused_2499_ = lean_ctor_get(v_a_2394_, 0);
lean_dec(v_unused_2499_);
v___x_2487_ = v_a_2394_;
v_isShared_2488_ = v_isSharedCheck_2497_;
goto v_resetjp_2486_;
}
else
{
lean_dec(v_a_2394_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2497_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2489_; lean_object* v___x_2491_; 
v___x_2489_ = lean_box(0);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 1, v___x_2489_);
lean_ctor_set(v___x_2487_, 0, v_e_2308_);
v___x_2491_ = v___x_2487_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_e_2308_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v___x_2489_);
v___x_2491_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
lean_object* v___x_2492_; lean_object* v___x_2494_; 
lean_ctor_set_uint8(v___x_2491_, sizeof(void*)*2, v___x_2344_);
v___x_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2491_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 0, v___x_2492_);
v___x_2494_ = v___x_2396_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2492_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
}
}
}
else
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2508_; 
lean_dec(v___x_2350_);
lean_dec_ref(v___x_2342_);
lean_dec_ref(v_arg_2341_);
lean_dec_ref(v_arg_2338_);
lean_dec_ref(v_arg_2335_);
lean_dec_ref(v_arg_2332_);
lean_dec_ref(v_arg_2329_);
lean_dec_ref(v_e_2308_);
v_a_2501_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2503_ = v___x_2393_;
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2393_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2506_; 
if (v_isShared_2504_ == 0)
{
v___x_2506_ = v___x_2503_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2501_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
}
}
else
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2517_; 
lean_dec(v___x_2350_);
lean_dec_ref(v___x_2342_);
lean_dec_ref(v_arg_2341_);
lean_dec_ref(v_arg_2338_);
lean_dec_ref(v_arg_2335_);
lean_dec_ref(v_arg_2332_);
lean_dec_ref(v_arg_2329_);
lean_dec_ref(v_e_2308_);
v_a_2510_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2512_ = v___x_2370_;
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2370_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2515_; 
if (v_isShared_2513_ == 0)
{
v___x_2515_ = v___x_2512_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_a_2510_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
}
}
}
else
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2526_; 
lean_dec_ref(v___x_2342_);
lean_dec_ref(v_arg_2341_);
lean_dec_ref(v_arg_2338_);
lean_dec_ref(v_arg_2335_);
lean_dec_ref(v_arg_2332_);
lean_dec_ref(v_arg_2329_);
lean_dec_ref(v_e_2308_);
v_a_2519_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2521_ = v___x_2345_;
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2345_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2524_; 
if (v_isShared_2522_ == 0)
{
v___x_2524_ = v___x_2521_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2519_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
}
}
}
}
}
}
v___jp_2322_:
{
lean_object* v___x_2323_; lean_object* v___x_2325_; 
v___x_2323_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__0));
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 0, v___x_2323_);
v___x_2325_ = v___x_2320_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2323_);
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
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
lean_dec_ref(v_e_2308_);
v_a_2528_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2317_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2317_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2528_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___boxed(lean_object* v_numIndices_2536_, lean_object* v_useDecideBool_2537_, lean_object* v_e_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_){
_start:
{
uint8_t v_useDecideBool_boxed_2547_; lean_object* v_res_2548_; 
v_useDecideBool_boxed_2547_ = lean_unbox(v_useDecideBool_2537_);
v_res_2548_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27(v_numIndices_2536_, v_useDecideBool_boxed_2547_, v_e_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_);
lean_dec(v_a_2545_);
lean_dec_ref(v_a_2544_);
lean_dec(v_a_2543_);
lean_dec_ref(v_a_2542_);
lean_dec(v_a_2541_);
lean_dec_ref(v_a_2540_);
lean_dec(v_a_2539_);
lean_dec(v_numIndices_2536_);
return v_res_2548_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0(void){
_start:
{
lean_object* v___x_2549_; 
v___x_2549_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_2549_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1(void){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v_s_2552_; 
v___x_2550_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__2, &l_Lean_Meta_SplitIf_getSimpContext___closed__2_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__2);
v___x_2551_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0);
v_s_2552_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_s_2552_, 0, v___x_2551_);
lean_ctor_set(v_s_2552_, 1, v___x_2551_);
lean_ctor_set(v_s_2552_, 2, v___x_2550_);
lean_ctor_set(v_s_2552_, 3, v___x_2550_);
return v_s_2552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(lean_object* v_numIndices_2616_, uint8_t v_useDecide_2617_){
_start:
{
lean_object* v_s_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v_s_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v_s_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v_s_2619_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1);
v___x_2620_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__3));
v___x_2621_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__16));
v___x_2622_ = 0;
v___x_2623_ = lean_box(v_useDecide_2617_);
lean_inc(v_numIndices_2616_);
v___x_2624_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___boxed), 11, 2);
lean_closure_set(v___x_2624_, 0, v_numIndices_2616_);
lean_closure_set(v___x_2624_, 1, v___x_2623_);
v___x_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2624_);
v_s_2626_ = l_Lean_Meta_Simp_Simprocs_addCore(v_s_2619_, v___x_2620_, v___x_2621_, v___x_2622_, v___x_2625_);
v___x_2627_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__18));
v___x_2628_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__20));
v___x_2629_ = lean_box(v_useDecide_2617_);
v___x_2630_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___boxed), 11, 2);
lean_closure_set(v___x_2630_, 0, v_numIndices_2616_);
lean_closure_set(v___x_2630_, 1, v___x_2629_);
v___x_2631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2630_);
v_s_2632_ = l_Lean_Meta_Simp_Simprocs_addCore(v_s_2626_, v___x_2627_, v___x_2628_, v___x_2622_, v___x_2631_);
v___x_2633_ = lean_unsigned_to_nat(1u);
v___x_2634_ = lean_mk_empty_array_with_capacity(v___x_2633_);
v___x_2635_ = lean_array_push(v___x_2634_, v_s_2632_);
v___x_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___boxed(lean_object* v_numIndices_2637_, lean_object* v_useDecide_2638_, lean_object* v_a_2639_){
_start:
{
uint8_t v_useDecide_boxed_2640_; lean_object* v_res_2641_; 
v_useDecide_boxed_2640_ = lean_unbox(v_useDecide_2638_);
v_res_2641_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_numIndices_2637_, v_useDecide_boxed_2640_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs(lean_object* v_numIndices_2642_, uint8_t v_useDecide_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_){
_start:
{
lean_object* v___x_2649_; 
v___x_2649_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_numIndices_2642_, v_useDecide_2643_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___boxed(lean_object* v_numIndices_2650_, lean_object* v_useDecide_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_){
_start:
{
uint8_t v_useDecide_boxed_2657_; lean_object* v_res_2658_; 
v_useDecide_boxed_2657_ = lean_unbox(v_useDecide_2651_);
v_res_2658_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs(v_numIndices_2650_, v_useDecide_boxed_2657_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(uint8_t v_useDecide_2659_, lean_object* v_a_2660_){
_start:
{
lean_object* v_lctx_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v_lctx_2662_ = lean_ctor_get(v_a_2660_, 2);
lean_inc_ref(v_lctx_2662_);
v___x_2663_ = lean_local_ctx_num_indices(v_lctx_2662_);
v___x_2664_ = lean_box(v_useDecide_2659_);
v___x_2665_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___boxed), 11, 2);
lean_closure_set(v___x_2665_, 0, v___x_2663_);
lean_closure_set(v___x_2665_, 1, v___x_2664_);
v___x_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2665_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg___boxed(lean_object* v_useDecide_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_){
_start:
{
uint8_t v_useDecide_boxed_2670_; lean_object* v_res_2671_; 
v_useDecide_boxed_2670_ = lean_unbox(v_useDecide_2667_);
v_res_2671_ = l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(v_useDecide_boxed_2670_, v_a_2668_);
lean_dec_ref(v_a_2668_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f(uint8_t v_useDecide_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_){
_start:
{
lean_object* v___x_2678_; 
v___x_2678_ = l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(v_useDecide_2672_, v_a_2673_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed(lean_object* v_useDecide_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_){
_start:
{
uint8_t v_useDecide_boxed_2685_; lean_object* v_res_2686_; 
v_useDecide_boxed_2685_ = lean_unbox(v_useDecide_2679_);
v_res_2686_ = l_Lean_Meta_SplitIf_mkDischarge_x3f(v_useDecide_boxed_2685_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_);
lean_dec(v_a_2683_);
lean_dec_ref(v_a_2682_);
lean_dec(v_a_2681_);
lean_dec_ref(v_a_2680_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(lean_object* v_mvarId_2687_, lean_object* v_x_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v___x_2694_; 
v___x_2694_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2687_, v_x_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___x_2694_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2694_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
else
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
v_a_2703_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v___x_2694_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2694_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2703_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_2711_, lean_object* v_x_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_){
_start:
{
lean_object* v_res_2718_; 
v_res_2718_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2711_, v_x_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0(lean_object* v_00_u03b1_2719_, lean_object* v_mvarId_2720_, lean_object* v_x_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2720_, v_x_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___boxed(lean_object* v_00_u03b1_2728_, lean_object* v_mvarId_2729_, lean_object* v_x_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0(v_00_u03b1_2728_, v_mvarId_2729_, v_x_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
return v_res_2736_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2738_ = ((lean_object*)(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__0));
v___x_2739_ = l_Lean_stringToMessageData(v___x_2738_);
return v___x_2739_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2741_ = ((lean_object*)(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__2));
v___x_2742_ = l_Lean_stringToMessageData(v___x_2741_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0(lean_object* v_e_2743_, lean_object* v_mvarId_2744_, lean_object* v_hName_x3f_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
lean_object* v___x_2754_; lean_object* v_a_2755_; lean_object* v___x_2756_; 
v___x_2754_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_2743_, v___y_2747_);
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc_n(v_a_2755_, 2);
lean_dec_ref(v___x_2754_);
v___x_2756_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(v_a_2755_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_a_2757_);
lean_dec_ref_known(v___x_2756_, 1);
if (lean_obj_tag(v_a_2757_) == 1)
{
lean_object* v_val_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2832_; 
lean_dec(v_a_2755_);
v_val_2758_ = lean_ctor_get(v_a_2757_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v_a_2757_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2760_ = v_a_2757_;
v_isShared_2761_ = v_isSharedCheck_2832_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_val_2758_);
lean_dec(v_a_2757_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2832_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v_fst_2762_; lean_object* v_snd_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2831_; 
v_fst_2762_ = lean_ctor_get(v_val_2758_, 0);
v_snd_2763_ = lean_ctor_get(v_val_2758_, 1);
v_isSharedCheck_2831_ = !lean_is_exclusive(v_val_2758_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2765_ = v_val_2758_;
v_isShared_2766_ = v_isSharedCheck_2831_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_snd_2763_);
lean_inc(v_fst_2762_);
lean_dec(v_val_2758_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2831_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v_hName_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; 
if (lean_obj_tag(v_hName_x3f_2745_) == 0)
{
lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2819_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__1));
v___x_2820_ = l_Lean_Core_mkFreshUserName(v___x_2819_, v___y_2748_, v___y_2749_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___x_2820_, 1);
v_hName_2794_ = v_a_2821_;
v___y_2795_ = v___y_2746_;
v___y_2796_ = v___y_2747_;
v___y_2797_ = v___y_2748_;
v___y_2798_ = v___y_2749_;
goto v___jp_2793_;
}
else
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
lean_del_object(v___x_2765_);
lean_dec(v_snd_2763_);
lean_dec(v_fst_2762_);
lean_del_object(v___x_2760_);
lean_dec(v_mvarId_2744_);
v_a_2822_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2824_ = v___x_2820_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2820_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2827_; 
if (v_isShared_2825_ == 0)
{
v___x_2827_ = v___x_2824_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2822_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
else
{
lean_object* v_val_2830_; 
v_val_2830_ = lean_ctor_get(v_hName_x3f_2745_, 0);
lean_inc(v_val_2830_);
lean_dec_ref_known(v_hName_x3f_2745_, 1);
v_hName_2794_ = v_val_2830_;
v___y_2795_ = v___y_2746_;
v___y_2796_ = v___y_2747_;
v___y_2797_ = v___y_2748_;
v___y_2798_ = v___y_2749_;
goto v___jp_2793_;
}
v___jp_2767_:
{
lean_object* v___x_2773_; 
v___x_2773_ = l_Lean_MVarId_byCasesDec(v_mvarId_2744_, v_fst_2762_, v_snd_2763_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2784_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2776_ = v___x_2773_;
v_isShared_2777_ = v_isSharedCheck_2784_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2773_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2784_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2779_; 
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v_a_2774_);
v___x_2779_ = v___x_2760_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2774_);
v___x_2779_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
lean_object* v___x_2781_; 
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 0, v___x_2779_);
v___x_2781_ = v___x_2776_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___x_2779_);
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
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
lean_del_object(v___x_2760_);
v_a_2785_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2773_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2773_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2790_; 
if (v_isShared_2788_ == 0)
{
v___x_2790_ = v___x_2787_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2785_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
v___jp_2793_:
{
lean_object* v_options_2799_; uint8_t v_hasTrace_2800_; 
v_options_2799_ = lean_ctor_get(v___y_2797_, 2);
v_hasTrace_2800_ = lean_ctor_get_uint8(v_options_2799_, sizeof(void*)*1);
if (v_hasTrace_2800_ == 0)
{
lean_del_object(v___x_2765_);
v___y_2768_ = v_hName_2794_;
v___y_2769_ = v___y_2795_;
v___y_2770_ = v___y_2796_;
v___y_2771_ = v___y_2797_;
v___y_2772_ = v___y_2798_;
goto v___jp_2767_;
}
else
{
lean_object* v_inheritedTraceOptions_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; uint8_t v___x_2804_; 
v_inheritedTraceOptions_2801_ = lean_ctor_get(v___y_2797_, 13);
v___x_2802_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10));
v___x_2803_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11);
v___x_2804_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2801_, v_options_2799_, v___x_2803_);
if (v___x_2804_ == 0)
{
lean_del_object(v___x_2765_);
v___y_2768_ = v_hName_2794_;
v___y_2769_ = v___y_2795_;
v___y_2770_ = v___y_2796_;
v___y_2771_ = v___y_2797_;
v___y_2772_ = v___y_2798_;
goto v___jp_2767_;
}
else
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2808_; 
v___x_2805_ = lean_obj_once(&l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1, &l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1_once, _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1);
lean_inc(v_snd_2763_);
v___x_2806_ = l_Lean_MessageData_ofExpr(v_snd_2763_);
if (v_isShared_2766_ == 0)
{
lean_ctor_set_tag(v___x_2765_, 7);
lean_ctor_set(v___x_2765_, 1, v___x_2806_);
lean_ctor_set(v___x_2765_, 0, v___x_2805_);
v___x_2808_ = v___x_2765_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v___x_2805_);
lean_ctor_set(v_reuseFailAlloc_2818_, 1, v___x_2806_);
v___x_2808_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
lean_object* v___x_2809_; 
v___x_2809_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_2802_, v___x_2808_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_dec_ref_known(v___x_2809_, 1);
v___y_2768_ = v_hName_2794_;
v___y_2769_ = v___y_2795_;
v___y_2770_ = v___y_2796_;
v___y_2771_ = v___y_2797_;
v___y_2772_ = v___y_2798_;
goto v___jp_2767_;
}
else
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
lean_dec(v_hName_2794_);
lean_dec(v_snd_2763_);
lean_dec(v_fst_2762_);
lean_del_object(v___x_2760_);
lean_dec(v_mvarId_2744_);
v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v___x_2809_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2809_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
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
lean_object* v_options_2833_; uint8_t v_hasTrace_2834_; 
lean_dec(v_a_2757_);
lean_dec(v_hName_x3f_2745_);
lean_dec(v_mvarId_2744_);
v_options_2833_ = lean_ctor_get(v___y_2748_, 2);
v_hasTrace_2834_ = lean_ctor_get_uint8(v_options_2833_, sizeof(void*)*1);
if (v_hasTrace_2834_ == 0)
{
lean_dec(v_a_2755_);
goto v___jp_2751_;
}
else
{
lean_object* v_inheritedTraceOptions_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; uint8_t v___x_2838_; 
v_inheritedTraceOptions_2835_ = lean_ctor_get(v___y_2748_, 13);
v___x_2836_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10));
v___x_2837_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11);
v___x_2838_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2835_, v_options_2833_, v___x_2837_);
if (v___x_2838_ == 0)
{
lean_dec(v_a_2755_);
goto v___jp_2751_;
}
else
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2839_ = lean_obj_once(&l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3, &l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3_once, _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3);
v___x_2840_ = l_Lean_indentExpr(v_a_2755_);
v___x_2841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2839_);
lean_ctor_set(v___x_2841_, 1, v___x_2840_);
v___x_2842_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_2836_, v___x_2841_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_dec_ref_known(v___x_2842_, 1);
goto v___jp_2751_;
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2842_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2842_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
lean_dec(v_a_2755_);
lean_dec(v_hName_x3f_2745_);
lean_dec(v_mvarId_2744_);
v_a_2851_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2853_ = v___x_2756_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2756_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_a_2851_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
v___jp_2751_:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2752_ = lean_box(0);
v___x_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2752_);
return v___x_2753_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___boxed(lean_object* v_e_2859_, lean_object* v_mvarId_2860_, lean_object* v_hName_x3f_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
lean_object* v_res_2867_; 
v_res_2867_ = l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0(v_e_2859_, v_mvarId_2860_, v_hName_x3f_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec_ref(v___y_2862_);
return v_res_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f(lean_object* v_mvarId_2868_, lean_object* v_e_2869_, lean_object* v_hName_x3f_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_){
_start:
{
lean_object* v___f_2876_; lean_object* v___x_2877_; 
lean_inc(v_mvarId_2868_);
v___f_2876_ = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2876_, 0, v_e_2869_);
lean_closure_set(v___f_2876_, 1, v_mvarId_2868_);
lean_closure_set(v___f_2876_, 2, v_hName_x3f_2870_);
v___x_2877_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2868_, v___f_2876_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___boxed(lean_object* v_mvarId_2878_, lean_object* v_e_2879_, lean_object* v_hName_x3f_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_){
_start:
{
lean_object* v_res_2886_; 
v_res_2886_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(v_mvarId_2878_, v_e_2879_, v_hName_x3f_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_);
lean_dec(v_a_2884_);
lean_dec_ref(v_a_2883_);
lean_dec(v_a_2882_);
lean_dec_ref(v_a_2881_);
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0(lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v_lctx_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
v_lctx_2892_ = lean_ctor_get(v___y_2887_, 2);
lean_inc_ref(v_lctx_2892_);
lean_dec_ref(v___y_2887_);
v___x_2893_ = lean_local_ctx_num_indices(v_lctx_2892_);
v___x_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2893_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0___boxed(lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0(v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_);
lean_dec(v___y_2898_);
lean_dec_ref(v___y_2897_);
lean_dec(v___y_2896_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(lean_object* v_mvarId_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_){
_start:
{
lean_object* v___f_2908_; lean_object* v___x_2909_; 
v___f_2908_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___closed__0));
v___x_2909_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2902_, v___f_2908_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___boxed(lean_object* v_mvarId_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(v_mvarId_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
lean_dec(v_a_2914_);
lean_dec_ref(v_a_2913_);
lean_dec(v_a_2912_);
lean_dec_ref(v_a_2911_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_simpIfTarget_spec__0(lean_object* v_msg_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v___f_2924_; lean_object* v___x_1955__overap_2925_; lean_object* v___x_2926_; 
v___f_2924_ = ((lean_object*)(l_panic___at___00Lean_Meta_simpIfTarget_spec__0___closed__0));
v___x_1955__overap_2925_ = lean_panic_fn_borrowed(v___f_2924_, v_msg_2918_);
lean_inc(v___y_2922_);
lean_inc_ref(v___y_2921_);
lean_inc(v___y_2920_);
lean_inc_ref(v___y_2919_);
v___x_2926_ = lean_apply_5(v___x_1955__overap_2925_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, lean_box(0));
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_simpIfTarget_spec__0___boxed(lean_object* v_msg_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v_msg_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
return v_res_2933_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(lean_object* v_opts_2934_, lean_object* v_opt_2935_){
_start:
{
lean_object* v_name_2936_; lean_object* v_defValue_2937_; lean_object* v_map_2938_; lean_object* v___x_2939_; 
v_name_2936_ = lean_ctor_get(v_opt_2935_, 0);
v_defValue_2937_ = lean_ctor_get(v_opt_2935_, 1);
v_map_2938_ = lean_ctor_get(v_opts_2934_, 0);
v___x_2939_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2938_, v_name_2936_);
if (lean_obj_tag(v___x_2939_) == 0)
{
uint8_t v___x_2940_; 
v___x_2940_ = lean_unbox(v_defValue_2937_);
return v___x_2940_;
}
else
{
lean_object* v_val_2941_; 
v_val_2941_ = lean_ctor_get(v___x_2939_, 0);
lean_inc(v_val_2941_);
lean_dec_ref_known(v___x_2939_, 1);
if (lean_obj_tag(v_val_2941_) == 1)
{
uint8_t v_v_2942_; 
v_v_2942_ = lean_ctor_get_uint8(v_val_2941_, 0);
lean_dec_ref_known(v_val_2941_, 0);
return v_v_2942_;
}
else
{
uint8_t v___x_2943_; 
lean_dec(v_val_2941_);
v___x_2943_ = lean_unbox(v_defValue_2937_);
return v___x_2943_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1___boxed(lean_object* v_opts_2944_, lean_object* v_opt_2945_){
_start:
{
uint8_t v_res_2946_; lean_object* v_r_2947_; 
v_res_2946_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v_opts_2944_, v_opt_2945_);
lean_dec_ref(v_opt_2945_);
lean_dec_ref(v_opts_2944_);
v_r_2947_ = lean_box(v_res_2946_);
return v_r_2947_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__0(void){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2948_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__1(void){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2949_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__0, &l_Lean_Meta_simpIfTarget___closed__0_once, _init_l_Lean_Meta_simpIfTarget___closed__0);
v___x_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
return v___x_2950_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__2(void){
_start:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2951_ = lean_unsigned_to_nat(0u);
v___x_2952_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__1, &l_Lean_Meta_simpIfTarget___closed__1_once, _init_l_Lean_Meta_simpIfTarget___closed__1);
v___x_2953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2952_);
lean_ctor_set(v___x_2953_, 1, v___x_2951_);
return v___x_2953_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__3(void){
_start:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2954_ = lean_unsigned_to_nat(32u);
v___x_2955_ = lean_mk_empty_array_with_capacity(v___x_2954_);
v___x_2956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2955_);
return v___x_2956_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__4(void){
_start:
{
size_t v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2957_ = ((size_t)5ULL);
v___x_2958_ = lean_unsigned_to_nat(0u);
v___x_2959_ = lean_unsigned_to_nat(32u);
v___x_2960_ = lean_mk_empty_array_with_capacity(v___x_2959_);
v___x_2961_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__3, &l_Lean_Meta_simpIfTarget___closed__3_once, _init_l_Lean_Meta_simpIfTarget___closed__3);
v___x_2962_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
lean_ctor_set(v___x_2962_, 1, v___x_2960_);
lean_ctor_set(v___x_2962_, 2, v___x_2958_);
lean_ctor_set(v___x_2962_, 3, v___x_2958_);
lean_ctor_set_usize(v___x_2962_, 4, v___x_2957_);
return v___x_2962_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__5(void){
_start:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2963_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__4, &l_Lean_Meta_simpIfTarget___closed__4_once, _init_l_Lean_Meta_simpIfTarget___closed__4);
v___x_2964_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__1, &l_Lean_Meta_simpIfTarget___closed__1_once, _init_l_Lean_Meta_simpIfTarget___closed__1);
v___x_2965_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
lean_ctor_set(v___x_2965_, 1, v___x_2964_);
lean_ctor_set(v___x_2965_, 2, v___x_2964_);
lean_ctor_set(v___x_2965_, 3, v___x_2963_);
return v___x_2965_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__6(void){
_start:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2966_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__5, &l_Lean_Meta_simpIfTarget___closed__5_once, _init_l_Lean_Meta_simpIfTarget___closed__5);
v___x_2967_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__2, &l_Lean_Meta_simpIfTarget___closed__2_once, _init_l_Lean_Meta_simpIfTarget___closed__2);
v___x_2968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2967_);
lean_ctor_set(v___x_2968_, 1, v___x_2966_);
return v___x_2968_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__10(void){
_start:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2972_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__9));
v___x_2973_ = lean_unsigned_to_nat(78u);
v___x_2974_ = lean_unsigned_to_nat(289u);
v___x_2975_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__8));
v___x_2976_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_2977_ = l_mkPanicMessageWithDecl(v___x_2976_, v___x_2975_, v___x_2974_, v___x_2973_, v___x_2972_);
return v___x_2977_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__12(void){
_start:
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2980_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__9));
v___x_2981_ = lean_unsigned_to_nat(128u);
v___x_2982_ = lean_unsigned_to_nat(293u);
v___x_2983_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__8));
v___x_2984_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_2985_ = l_mkPanicMessageWithDecl(v___x_2984_, v___x_2983_, v___x_2982_, v___x_2981_, v___x_2980_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfTarget(lean_object* v_mvarId_2986_, uint8_t v_useDecide_2987_, uint8_t v_useNewSemantics_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_){
_start:
{
if (v_useNewSemantics_2988_ == 0)
{
lean_object* v_options_3041_; lean_object* v___x_3042_; uint8_t v___x_3043_; 
v_options_3041_ = lean_ctor_get(v_a_2991_, 2);
v___x_3042_ = l_Lean_Meta_backward_split;
v___x_3043_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v_options_3041_, v___x_3042_);
if (v___x_3043_ == 0)
{
goto v___jp_2994_;
}
else
{
lean_object* v___x_3044_; 
v___x_3044_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc(v_a_3045_);
lean_dec_ref_known(v___x_3044_, 1);
v___x_3046_ = lean_box(v_useDecide_2987_);
v___x_3047_ = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed), 6, 1);
lean_closure_set(v___x_3047_, 0, v___x_3046_);
lean_inc(v_mvarId_2986_);
v___x_3048_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2986_, v___x_3047_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v_a_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_a_3049_);
lean_dec_ref_known(v___x_3048_, 1);
v___x_3050_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__11));
v___x_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3051_, 0, v_a_3049_);
v___x_3052_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__6, &l_Lean_Meta_simpIfTarget___closed__6_once, _init_l_Lean_Meta_simpIfTarget___closed__6);
v___x_3053_ = l_Lean_Meta_simpTarget(v_mvarId_2986_, v_a_3045_, v___x_3050_, v___x_3051_, v_useNewSemantics_2988_, v___x_3052_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3065_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3056_ = v___x_3053_;
v_isShared_3057_ = v_isSharedCheck_3065_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_3053_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3065_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v_fst_3058_; 
v_fst_3058_ = lean_ctor_get(v_a_3054_, 0);
lean_inc(v_fst_3058_);
lean_dec(v_a_3054_);
if (lean_obj_tag(v_fst_3058_) == 1)
{
lean_object* v_val_3059_; lean_object* v___x_3061_; 
v_val_3059_ = lean_ctor_get(v_fst_3058_, 0);
lean_inc(v_val_3059_);
lean_dec_ref_known(v_fst_3058_, 1);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 0, v_val_3059_);
v___x_3061_ = v___x_3056_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_val_3059_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
else
{
lean_object* v___x_3063_; lean_object* v___x_3064_; 
lean_dec(v_fst_3058_);
lean_del_object(v___x_3056_);
v___x_3063_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__12, &l_Lean_Meta_simpIfTarget___closed__12_once, _init_l_Lean_Meta_simpIfTarget___closed__12);
v___x_3064_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3063_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_);
return v___x_3064_;
}
}
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
v_a_3066_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_3053_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3053_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3066_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
}
else
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
lean_dec(v_a_3045_);
lean_dec(v_mvarId_2986_);
v_a_3074_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_3048_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_3048_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_a_3074_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
else
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3089_; 
lean_dec(v_mvarId_2986_);
v_a_3082_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3084_ = v___x_3044_;
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_3044_);
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
}
else
{
goto v___jp_2994_;
}
v___jp_2994_:
{
lean_object* v___x_2995_; 
v___x_2995_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_2989_, v_a_2991_, v_a_2992_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_a_2996_; lean_object* v___x_2997_; 
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_a_2996_);
lean_dec_ref_known(v___x_2995_, 1);
lean_inc(v_mvarId_2986_);
v___x_2997_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(v_mvarId_2986_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v___x_2999_; lean_object* v_a_3000_; lean_object* v___x_3001_; uint8_t v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
lean_dec_ref_known(v___x_2997_, 1);
v___x_2999_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_a_2998_, v_useDecide_2987_);
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc(v_a_3000_);
lean_dec_ref(v___x_2999_);
v___x_3001_ = lean_box(0);
v___x_3002_ = 0;
v___x_3003_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__6, &l_Lean_Meta_simpIfTarget___closed__6_once, _init_l_Lean_Meta_simpIfTarget___closed__6);
v___x_3004_ = l_Lean_Meta_simpTarget(v_mvarId_2986_, v_a_2996_, v_a_3000_, v___x_3001_, v___x_3002_, v___x_3003_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3016_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3007_ = v___x_3004_;
v_isShared_3008_ = v_isSharedCheck_3016_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_3004_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3016_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v_fst_3009_; 
v_fst_3009_ = lean_ctor_get(v_a_3005_, 0);
lean_inc(v_fst_3009_);
lean_dec(v_a_3005_);
if (lean_obj_tag(v_fst_3009_) == 1)
{
lean_object* v_val_3010_; lean_object* v___x_3012_; 
v_val_3010_ = lean_ctor_get(v_fst_3009_, 0);
lean_inc(v_val_3010_);
lean_dec_ref_known(v_fst_3009_, 1);
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 0, v_val_3010_);
v___x_3012_ = v___x_3007_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_val_3010_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
else
{
lean_object* v___x_3014_; lean_object* v___x_3015_; 
lean_dec(v_fst_3009_);
lean_del_object(v___x_3007_);
v___x_3014_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__10, &l_Lean_Meta_simpIfTarget___closed__10_once, _init_l_Lean_Meta_simpIfTarget___closed__10);
v___x_3015_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3014_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_);
return v___x_3015_;
}
}
}
else
{
lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3024_; 
v_a_3017_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3019_ = v___x_3004_;
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_3004_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3022_; 
if (v_isShared_3020_ == 0)
{
v___x_3022_ = v___x_3019_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_a_3017_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
}
else
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
lean_dec(v_a_2996_);
lean_dec(v_mvarId_2986_);
v_a_3025_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3027_ = v___x_2997_;
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_2997_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
if (v_isShared_3028_ == 0)
{
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3025_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
else
{
lean_object* v_a_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3040_; 
lean_dec(v_mvarId_2986_);
v_a_3033_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3035_ = v___x_2995_;
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_a_3033_);
lean_dec(v___x_2995_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3038_; 
if (v_isShared_3036_ == 0)
{
v___x_3038_ = v___x_3035_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_a_3033_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfTarget___boxed(lean_object* v_mvarId_3090_, lean_object* v_useDecide_3091_, lean_object* v_useNewSemantics_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_){
_start:
{
uint8_t v_useDecide_boxed_3098_; uint8_t v_useNewSemantics_boxed_3099_; lean_object* v_res_3100_; 
v_useDecide_boxed_3098_ = lean_unbox(v_useDecide_3091_);
v_useNewSemantics_boxed_3099_ = lean_unbox(v_useNewSemantics_3092_);
v_res_3100_ = l_Lean_Meta_simpIfTarget(v_mvarId_3090_, v_useDecide_boxed_3098_, v_useNewSemantics_boxed_3099_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_);
lean_dec(v_a_3096_);
lean_dec_ref(v_a_3095_);
lean_dec(v_a_3094_);
lean_dec_ref(v_a_3093_);
return v_res_3100_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfLocalDecl___closed__1(void){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3102_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__9));
v___x_3103_ = lean_unsigned_to_nat(93u);
v___x_3104_ = lean_unsigned_to_nat(305u);
v___x_3105_ = ((lean_object*)(l_Lean_Meta_simpIfLocalDecl___closed__0));
v___x_3106_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_3107_ = l_mkPanicMessageWithDecl(v___x_3106_, v___x_3105_, v___x_3104_, v___x_3103_, v___x_3102_);
return v___x_3107_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfLocalDecl___closed__2(void){
_start:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3108_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__9));
v___x_3109_ = lean_unsigned_to_nat(133u);
v___x_3110_ = lean_unsigned_to_nat(309u);
v___x_3111_ = ((lean_object*)(l_Lean_Meta_simpIfLocalDecl___closed__0));
v___x_3112_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_3113_ = l_mkPanicMessageWithDecl(v___x_3112_, v___x_3111_, v___x_3110_, v___x_3109_, v___x_3108_);
return v___x_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfLocalDecl(lean_object* v_mvarId_3114_, lean_object* v_fvarId_3115_, uint8_t v_useNewSemantics_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_){
_start:
{
if (v_useNewSemantics_3116_ == 0)
{
lean_object* v_options_3170_; lean_object* v___x_3171_; uint8_t v___x_3172_; 
v_options_3170_ = lean_ctor_get(v_a_3119_, 2);
v___x_3171_ = l_Lean_Meta_backward_split;
v___x_3172_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v_options_3170_, v___x_3171_);
if (v___x_3172_ == 0)
{
goto v___jp_3122_;
}
else
{
lean_object* v___x_3173_; 
v___x_3173_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_);
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_object* v_a_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v_a_3174_ = lean_ctor_get(v___x_3173_, 0);
lean_inc(v_a_3174_);
lean_dec_ref_known(v___x_3173_, 1);
v___x_3175_ = lean_box(v_useNewSemantics_3116_);
v___x_3176_ = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed), 6, 1);
lean_closure_set(v___x_3176_, 0, v___x_3175_);
lean_inc(v_mvarId_3114_);
v___x_3177_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_3114_, v___x_3176_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
lean_inc(v_a_3178_);
lean_dec_ref_known(v___x_3177_, 1);
v___x_3179_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__11));
v___x_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3180_, 0, v_a_3178_);
v___x_3181_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__6, &l_Lean_Meta_simpIfTarget___closed__6_once, _init_l_Lean_Meta_simpIfTarget___closed__6);
v___x_3182_ = l_Lean_Meta_simpLocalDecl(v_mvarId_3114_, v_fvarId_3115_, v_a_3174_, v___x_3179_, v___x_3180_, v_useNewSemantics_3116_, v___x_3181_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_);
if (lean_obj_tag(v___x_3182_) == 0)
{
lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3195_; 
v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3185_ = v___x_3182_;
v_isShared_3186_ = v_isSharedCheck_3195_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3182_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3195_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v_fst_3187_; 
v_fst_3187_ = lean_ctor_get(v_a_3183_, 0);
lean_inc(v_fst_3187_);
lean_dec(v_a_3183_);
if (lean_obj_tag(v_fst_3187_) == 1)
{
lean_object* v_val_3188_; lean_object* v_snd_3189_; lean_object* v___x_3191_; 
v_val_3188_ = lean_ctor_get(v_fst_3187_, 0);
lean_inc(v_val_3188_);
lean_dec_ref_known(v_fst_3187_, 1);
v_snd_3189_ = lean_ctor_get(v_val_3188_, 1);
lean_inc(v_snd_3189_);
lean_dec(v_val_3188_);
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 0, v_snd_3189_);
v___x_3191_ = v___x_3185_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_snd_3189_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
else
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
lean_dec(v_fst_3187_);
lean_del_object(v___x_3185_);
v___x_3193_ = lean_obj_once(&l_Lean_Meta_simpIfLocalDecl___closed__2, &l_Lean_Meta_simpIfLocalDecl___closed__2_once, _init_l_Lean_Meta_simpIfLocalDecl___closed__2);
v___x_3194_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3193_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_);
return v___x_3194_;
}
}
}
else
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3203_; 
v_a_3196_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3198_ = v___x_3182_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_3182_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3201_; 
if (v_isShared_3199_ == 0)
{
v___x_3201_ = v___x_3198_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_a_3196_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
}
else
{
lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3211_; 
lean_dec(v_a_3174_);
lean_dec(v_fvarId_3115_);
lean_dec(v_mvarId_3114_);
v_a_3204_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3206_ = v___x_3177_;
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3177_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3209_; 
if (v_isShared_3207_ == 0)
{
v___x_3209_ = v___x_3206_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_a_3204_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
}
else
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3219_; 
lean_dec(v_fvarId_3115_);
lean_dec(v_mvarId_3114_);
v_a_3212_ = lean_ctor_get(v___x_3173_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3214_ = v___x_3173_;
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3173_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3217_; 
if (v_isShared_3215_ == 0)
{
v___x_3217_ = v___x_3214_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_a_3212_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
}
}
}
else
{
goto v___jp_3122_;
}
v___jp_3122_:
{
lean_object* v___x_3123_; 
v___x_3123_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_3117_, v_a_3119_, v_a_3120_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v_a_3124_; lean_object* v___x_3125_; 
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
lean_inc(v_a_3124_);
lean_dec_ref_known(v___x_3123_, 1);
lean_inc(v_mvarId_3114_);
v___x_3125_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(v_mvarId_3114_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_);
if (lean_obj_tag(v___x_3125_) == 0)
{
lean_object* v_a_3126_; uint8_t v___x_3127_; lean_object* v___x_3128_; lean_object* v_a_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v_a_3126_ = lean_ctor_get(v___x_3125_, 0);
lean_inc(v_a_3126_);
lean_dec_ref_known(v___x_3125_, 1);
v___x_3127_ = 0;
v___x_3128_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_a_3126_, v___x_3127_);
v_a_3129_ = lean_ctor_get(v___x_3128_, 0);
lean_inc(v_a_3129_);
lean_dec_ref(v___x_3128_);
v___x_3130_ = lean_box(0);
v___x_3131_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__6, &l_Lean_Meta_simpIfTarget___closed__6_once, _init_l_Lean_Meta_simpIfTarget___closed__6);
v___x_3132_ = l_Lean_Meta_simpLocalDecl(v_mvarId_3114_, v_fvarId_3115_, v_a_3124_, v_a_3129_, v___x_3130_, v___x_3127_, v___x_3131_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3145_; 
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3135_ = v___x_3132_;
v_isShared_3136_ = v_isSharedCheck_3145_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3132_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3145_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v_fst_3137_; 
v_fst_3137_ = lean_ctor_get(v_a_3133_, 0);
lean_inc(v_fst_3137_);
lean_dec(v_a_3133_);
if (lean_obj_tag(v_fst_3137_) == 1)
{
lean_object* v_val_3138_; lean_object* v_snd_3139_; lean_object* v___x_3141_; 
v_val_3138_ = lean_ctor_get(v_fst_3137_, 0);
lean_inc(v_val_3138_);
lean_dec_ref_known(v_fst_3137_, 1);
v_snd_3139_ = lean_ctor_get(v_val_3138_, 1);
lean_inc(v_snd_3139_);
lean_dec(v_val_3138_);
if (v_isShared_3136_ == 0)
{
lean_ctor_set(v___x_3135_, 0, v_snd_3139_);
v___x_3141_ = v___x_3135_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_snd_3139_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
else
{
lean_object* v___x_3143_; lean_object* v___x_3144_; 
lean_dec(v_fst_3137_);
lean_del_object(v___x_3135_);
v___x_3143_ = lean_obj_once(&l_Lean_Meta_simpIfLocalDecl___closed__1, &l_Lean_Meta_simpIfLocalDecl___closed__1_once, _init_l_Lean_Meta_simpIfLocalDecl___closed__1);
v___x_3144_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3143_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_);
return v___x_3144_;
}
}
}
else
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
v_a_3146_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v___x_3132_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3132_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3151_; 
if (v_isShared_3149_ == 0)
{
v___x_3151_ = v___x_3148_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_a_3146_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
}
}
}
}
else
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
lean_dec(v_a_3124_);
lean_dec(v_fvarId_3115_);
lean_dec(v_mvarId_3114_);
v_a_3154_ = lean_ctor_get(v___x_3125_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v___x_3125_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_3125_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3154_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
}
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
lean_dec(v_fvarId_3115_);
lean_dec(v_mvarId_3114_);
v_a_3162_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3123_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3123_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfLocalDecl___boxed(lean_object* v_mvarId_3220_, lean_object* v_fvarId_3221_, lean_object* v_useNewSemantics_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_){
_start:
{
uint8_t v_useNewSemantics_boxed_3228_; lean_object* v_res_3229_; 
v_useNewSemantics_boxed_3228_ = lean_unbox(v_useNewSemantics_3222_);
v_res_3229_ = l_Lean_Meta_simpIfLocalDecl(v_mvarId_3220_, v_fvarId_3221_, v_useNewSemantics_boxed_3228_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
lean_dec(v_a_3226_);
lean_dec_ref(v_a_3225_);
lean_dec(v_a_3224_);
lean_dec_ref(v_a_3223_);
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(lean_object* v_x_x3f_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_){
_start:
{
lean_object* v___x_3236_; 
v___x_3236_ = l_Lean_Meta_saveState___redArg(v___y_3232_, v___y_3234_);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3281_; 
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3239_ = v___x_3236_;
v_isShared_3240_ = v_isSharedCheck_3281_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3236_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3281_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___y_3242_; uint8_t v___y_3243_; lean_object* v_a_3265_; lean_object* v___x_3268_; 
lean_inc(v___y_3234_);
lean_inc_ref(v___y_3233_);
lean_inc(v___y_3232_);
lean_inc_ref(v___y_3231_);
v___x_3268_ = lean_apply_5(v_x_x3f_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, lean_box(0));
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3269_);
if (lean_obj_tag(v_a_3269_) == 0)
{
lean_object* v___x_3270_; 
lean_dec_ref_known(v___x_3268_, 1);
v___x_3270_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3237_, v___y_3232_, v___y_3234_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3277_; 
lean_del_object(v___x_3239_);
lean_dec(v_a_3237_);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3277_ == 0)
{
lean_object* v_unused_3278_; 
v_unused_3278_ = lean_ctor_get(v___x_3270_, 0);
lean_dec(v_unused_3278_);
v___x_3272_ = v___x_3270_;
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
else
{
lean_dec(v___x_3270_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3275_; 
if (v_isShared_3273_ == 0)
{
lean_ctor_set(v___x_3272_, 0, v_a_3269_);
v___x_3275_ = v___x_3272_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3269_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
else
{
lean_object* v_a_3279_; 
v_a_3279_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3279_);
lean_dec_ref_known(v___x_3270_, 1);
v_a_3265_ = v_a_3279_;
goto v___jp_3264_;
}
}
else
{
lean_dec_ref_known(v_a_3269_, 1);
lean_del_object(v___x_3239_);
lean_dec(v_a_3237_);
return v___x_3268_;
}
}
else
{
lean_object* v_a_3280_; 
v_a_3280_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3280_);
lean_dec_ref_known(v___x_3268_, 1);
v_a_3265_ = v_a_3280_;
goto v___jp_3264_;
}
v___jp_3241_:
{
if (v___y_3243_ == 0)
{
lean_object* v___x_3244_; 
lean_del_object(v___x_3239_);
v___x_3244_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3237_, v___y_3232_, v___y_3234_);
lean_dec(v_a_3237_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3251_; 
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3251_ == 0)
{
lean_object* v_unused_3252_; 
v_unused_3252_ = lean_ctor_get(v___x_3244_, 0);
lean_dec(v_unused_3252_);
v___x_3246_ = v___x_3244_;
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
else
{
lean_dec(v___x_3244_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3249_; 
if (v_isShared_3247_ == 0)
{
lean_ctor_set_tag(v___x_3246_, 1);
lean_ctor_set(v___x_3246_, 0, v___y_3242_);
v___x_3249_ = v___x_3246_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v___y_3242_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
}
else
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
lean_dec_ref(v___y_3242_);
v_a_3253_ = lean_ctor_get(v___x_3244_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3255_ = v___x_3244_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3244_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
}
else
{
lean_object* v___x_3262_; 
lean_dec(v_a_3237_);
if (v_isShared_3240_ == 0)
{
lean_ctor_set_tag(v___x_3239_, 1);
lean_ctor_set(v___x_3239_, 0, v___y_3242_);
v___x_3262_ = v___x_3239_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___y_3242_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
v___jp_3264_:
{
uint8_t v___x_3266_; 
v___x_3266_ = l_Lean_Exception_isInterrupt(v_a_3265_);
if (v___x_3266_ == 0)
{
uint8_t v___x_3267_; 
lean_inc_ref(v_a_3265_);
v___x_3267_ = l_Lean_Exception_isRuntime(v_a_3265_);
v___y_3242_ = v_a_3265_;
v___y_3243_ = v___x_3267_;
goto v___jp_3241_;
}
else
{
v___y_3242_ = v_a_3265_;
v___y_3243_ = v___x_3266_;
goto v___jp_3241_;
}
}
}
}
else
{
lean_object* v_a_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3289_; 
lean_dec_ref(v_x_x3f_3230_);
v_a_3282_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3284_ = v___x_3236_;
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_a_3282_);
lean_dec(v___x_3236_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3287_; 
if (v_isShared_3285_ == 0)
{
v___x_3287_ = v___x_3284_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_a_3282_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg___boxed(lean_object* v_x_x3f_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v_x_x3f_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0(lean_object* v_00_u03b1_3297_, lean_object* v_x_x3f_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_){
_start:
{
lean_object* v___x_3304_; 
v___x_3304_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v_x_x3f_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
return v___x_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___boxed(lean_object* v_00_u03b1_3305_, lean_object* v_x_x3f_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0(v_00_u03b1_3305_, v_x_x3f_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3309_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
return v_res_3312_;
}
}
static lean_object* _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3317_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1));
v___x_3318_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4));
v___x_3319_ = l_Lean_Name_append(v___x_3318_, v___x_3317_);
return v___x_3319_;
}
}
static lean_object* _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3321_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__3));
v___x_3322_ = l_Lean_stringToMessageData(v___x_3321_);
return v___x_3322_;
}
}
static lean_object* _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3324_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__5));
v___x_3325_ = l_Lean_stringToMessageData(v___x_3324_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0(lean_object* v_mvarId_3326_, lean_object* v_hName_x3f_3327_, uint8_t v_useNewSemantics_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
lean_object* v___x_3337_; 
lean_inc(v_mvarId_3326_);
v___x_3337_ = l_Lean_MVarId_getType(v_mvarId_3326_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; lean_object* v___x_3339_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
lean_inc(v_a_3338_);
lean_dec_ref_known(v___x_3337_, 1);
v___x_3339_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(v_mvarId_3326_, v_a_3338_, v_hName_x3f_3327_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v_a_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3436_; 
v_a_3340_ = lean_ctor_get(v___x_3339_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3339_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3342_ = v___x_3339_;
v_isShared_3343_ = v_isSharedCheck_3436_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_dec(v___x_3339_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3436_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
if (lean_obj_tag(v_a_3340_) == 1)
{
lean_object* v_val_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3431_; 
lean_del_object(v___x_3342_);
v_val_3344_ = lean_ctor_get(v_a_3340_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v_a_3340_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3346_ = v_a_3340_;
v_isShared_3347_ = v_isSharedCheck_3431_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_val_3344_);
lean_dec(v_a_3340_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3431_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v_fst_3348_; lean_object* v_snd_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3430_; 
v_fst_3348_ = lean_ctor_get(v_val_3344_, 0);
v_snd_3349_ = lean_ctor_get(v_val_3344_, 1);
v_isSharedCheck_3430_ = !lean_is_exclusive(v_val_3344_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3351_ = v_val_3344_;
v_isShared_3352_ = v_isSharedCheck_3430_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_snd_3349_);
lean_inc(v_fst_3348_);
lean_dec(v_val_3344_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3430_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v_mvarId_3353_; lean_object* v_fvarId_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3429_; 
v_mvarId_3353_ = lean_ctor_get(v_fst_3348_, 0);
v_fvarId_3354_ = lean_ctor_get(v_fst_3348_, 1);
v_isSharedCheck_3429_ = !lean_is_exclusive(v_fst_3348_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3356_ = v_fst_3348_;
v_isShared_3357_ = v_isSharedCheck_3429_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_fvarId_3354_);
lean_inc(v_mvarId_3353_);
lean_dec(v_fst_3348_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3429_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
uint8_t v___x_3358_; lean_object* v___x_3359_; 
v___x_3358_ = 0;
lean_inc(v_mvarId_3353_);
v___x_3359_ = l_Lean_Meta_simpIfTarget(v_mvarId_3353_, v___x_3358_, v_useNewSemantics_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v_a_3360_; lean_object* v_mvarId_3361_; lean_object* v_fvarId_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3420_; 
v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_a_3360_);
lean_dec_ref_known(v___x_3359_, 1);
v_mvarId_3361_ = lean_ctor_get(v_snd_3349_, 0);
v_fvarId_3362_ = lean_ctor_get(v_snd_3349_, 1);
v_isSharedCheck_3420_ = !lean_is_exclusive(v_snd_3349_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3364_ = v_snd_3349_;
v_isShared_3365_ = v_isSharedCheck_3420_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_fvarId_3362_);
lean_inc(v_mvarId_3361_);
lean_dec(v_snd_3349_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3420_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3366_; 
lean_inc(v_mvarId_3361_);
v___x_3366_ = l_Lean_Meta_simpIfTarget(v_mvarId_3361_, v___x_3358_, v_useNewSemantics_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3411_; 
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3369_ = v___x_3366_;
v_isShared_3370_ = v_isSharedCheck_3411_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3366_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3411_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
uint8_t v___x_3387_; 
v___x_3387_ = l_Lean_instBEqMVarId_beq(v_mvarId_3353_, v_a_3360_);
lean_dec(v_mvarId_3353_);
if (v___x_3387_ == 0)
{
lean_dec(v_mvarId_3361_);
goto v___jp_3371_;
}
else
{
uint8_t v___x_3388_; 
v___x_3388_ = l_Lean_instBEqMVarId_beq(v_mvarId_3361_, v_a_3367_);
lean_dec(v_mvarId_3361_);
if (v___x_3388_ == 0)
{
goto v___jp_3371_;
}
else
{
lean_object* v_options_3389_; uint8_t v_hasTrace_3390_; 
lean_del_object(v___x_3369_);
lean_del_object(v___x_3364_);
lean_dec(v_fvarId_3362_);
lean_del_object(v___x_3356_);
lean_dec(v_fvarId_3354_);
lean_del_object(v___x_3351_);
lean_del_object(v___x_3346_);
v_options_3389_ = lean_ctor_get(v___y_3331_, 2);
v_hasTrace_3390_ = lean_ctor_get_uint8(v_options_3389_, sizeof(void*)*1);
if (v_hasTrace_3390_ == 0)
{
lean_dec(v_a_3367_);
lean_dec(v_a_3360_);
goto v___jp_3334_;
}
else
{
lean_object* v_inheritedTraceOptions_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; uint8_t v___x_3394_; 
v_inheritedTraceOptions_3391_ = lean_ctor_get(v___y_3331_, 13);
v___x_3392_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1));
v___x_3393_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2);
v___x_3394_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3391_, v_options_3389_, v___x_3393_);
if (v___x_3394_ == 0)
{
lean_dec(v_a_3367_);
lean_dec(v_a_3360_);
goto v___jp_3334_;
}
else
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3395_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4);
v___x_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3396_, 0, v_a_3360_);
v___x_3397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3395_);
lean_ctor_set(v___x_3397_, 1, v___x_3396_);
v___x_3398_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6);
v___x_3399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3397_);
lean_ctor_set(v___x_3399_, 1, v___x_3398_);
v___x_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3400_, 0, v_a_3367_);
v___x_3401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3399_);
lean_ctor_set(v___x_3401_, 1, v___x_3400_);
v___x_3402_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_3392_, v___x_3401_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3402_) == 0)
{
lean_dec_ref_known(v___x_3402_, 1);
goto v___jp_3334_;
}
else
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
v_a_3403_ = lean_ctor_get(v___x_3402_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3402_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3402_);
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
}
}
}
v___jp_3371_:
{
lean_object* v___x_3373_; 
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 1, v_fvarId_3354_);
lean_ctor_set(v___x_3364_, 0, v_a_3360_);
v___x_3373_ = v___x_3364_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_a_3360_);
lean_ctor_set(v_reuseFailAlloc_3386_, 1, v_fvarId_3354_);
v___x_3373_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
lean_object* v___x_3375_; 
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 1, v_fvarId_3362_);
lean_ctor_set(v___x_3356_, 0, v_a_3367_);
v___x_3375_ = v___x_3356_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3367_);
lean_ctor_set(v_reuseFailAlloc_3385_, 1, v_fvarId_3362_);
v___x_3375_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
lean_object* v___x_3377_; 
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 1, v___x_3375_);
lean_ctor_set(v___x_3351_, 0, v___x_3373_);
v___x_3377_ = v___x_3351_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v___x_3373_);
lean_ctor_set(v_reuseFailAlloc_3384_, 1, v___x_3375_);
v___x_3377_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
lean_object* v___x_3379_; 
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 0, v___x_3377_);
v___x_3379_ = v___x_3346_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3377_);
v___x_3379_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
lean_object* v___x_3381_; 
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 0, v___x_3379_);
v___x_3381_ = v___x_3369_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v___x_3379_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
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
lean_object* v_a_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3419_; 
lean_del_object(v___x_3364_);
lean_dec(v_fvarId_3362_);
lean_dec(v_mvarId_3361_);
lean_dec(v_a_3360_);
lean_del_object(v___x_3356_);
lean_dec(v_fvarId_3354_);
lean_dec(v_mvarId_3353_);
lean_del_object(v___x_3351_);
lean_del_object(v___x_3346_);
v_a_3412_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3414_ = v___x_3366_;
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_a_3412_);
lean_dec(v___x_3366_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3417_; 
if (v_isShared_3415_ == 0)
{
v___x_3417_ = v___x_3414_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_a_3412_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
}
}
}
else
{
lean_object* v_a_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3428_; 
lean_del_object(v___x_3356_);
lean_dec(v_fvarId_3354_);
lean_dec(v_mvarId_3353_);
lean_del_object(v___x_3351_);
lean_dec(v_snd_3349_);
lean_del_object(v___x_3346_);
v_a_3421_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3423_ = v___x_3359_;
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_a_3421_);
lean_dec(v___x_3359_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3426_; 
if (v_isShared_3424_ == 0)
{
v___x_3426_ = v___x_3423_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_a_3421_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3432_; lean_object* v___x_3434_; 
lean_dec(v_a_3340_);
v___x_3432_ = lean_box(0);
if (v_isShared_3343_ == 0)
{
lean_ctor_set(v___x_3342_, 0, v___x_3432_);
v___x_3434_ = v___x_3342_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v___x_3432_);
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
else
{
return v___x_3339_;
}
}
else
{
lean_object* v_a_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3444_; 
lean_dec(v_hName_x3f_3327_);
lean_dec(v_mvarId_3326_);
v_a_3437_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3439_ = v___x_3337_;
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_a_3437_);
lean_dec(v___x_3337_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3442_; 
if (v_isShared_3440_ == 0)
{
v___x_3442_ = v___x_3439_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_a_3437_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
}
v___jp_3334_:
{
lean_object* v___x_3335_; lean_object* v___x_3336_; 
v___x_3335_ = lean_box(0);
v___x_3336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3335_);
return v___x_3336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0___boxed(lean_object* v_mvarId_3445_, lean_object* v_hName_x3f_3446_, lean_object* v_useNewSemantics_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_){
_start:
{
uint8_t v_useNewSemantics_boxed_3453_; lean_object* v_res_3454_; 
v_useNewSemantics_boxed_3453_ = lean_unbox(v_useNewSemantics_3447_);
v_res_3454_ = l_Lean_Meta_splitIfTarget_x3f___lam__0(v_mvarId_3445_, v_hName_x3f_3446_, v_useNewSemantics_boxed_3453_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
return v_res_3454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f(lean_object* v_mvarId_3455_, lean_object* v_hName_x3f_3456_, uint8_t v_useNewSemantics_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_){
_start:
{
lean_object* v___x_3463_; lean_object* v___f_3464_; lean_object* v___x_3465_; 
v___x_3463_ = lean_box(v_useNewSemantics_3457_);
v___f_3464_ = lean_alloc_closure((void*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3464_, 0, v_mvarId_3455_);
lean_closure_set(v___f_3464_, 1, v_hName_x3f_3456_);
lean_closure_set(v___f_3464_, 2, v___x_3463_);
v___x_3465_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v___f_3464_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
return v___x_3465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___boxed(lean_object* v_mvarId_3466_, lean_object* v_hName_x3f_3467_, lean_object* v_useNewSemantics_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_){
_start:
{
uint8_t v_useNewSemantics_boxed_3474_; lean_object* v_res_3475_; 
v_useNewSemantics_boxed_3474_ = lean_unbox(v_useNewSemantics_3468_);
v_res_3475_ = l_Lean_Meta_splitIfTarget_x3f(v_mvarId_3466_, v_hName_x3f_3467_, v_useNewSemantics_boxed_3474_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_);
lean_dec(v_a_3472_);
lean_dec_ref(v_a_3471_);
lean_dec(v_a_3470_);
lean_dec_ref(v_a_3469_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___lam__0(lean_object* v___x_3476_, lean_object* v_mvarId_3477_, lean_object* v_hName_x3f_3478_, lean_object* v_fvarId_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_){
_start:
{
lean_object* v___x_3488_; 
lean_inc(v___y_3483_);
lean_inc_ref(v___y_3482_);
lean_inc(v___y_3481_);
lean_inc_ref(v___y_3480_);
v___x_3488_ = lean_infer_type(v___x_3476_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; lean_object* v___x_3490_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_a_3489_);
lean_dec_ref_known(v___x_3488_, 1);
v___x_3490_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(v_mvarId_3477_, v_a_3489_, v_hName_x3f_3478_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3585_; 
v_a_3491_ = lean_ctor_get(v___x_3490_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3493_ = v___x_3490_;
v_isShared_3494_ = v_isSharedCheck_3585_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3490_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3585_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
if (lean_obj_tag(v_a_3491_) == 1)
{
lean_object* v_val_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3580_; 
lean_del_object(v___x_3493_);
v_val_3495_ = lean_ctor_get(v_a_3491_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v_a_3491_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3497_ = v_a_3491_;
v_isShared_3498_ = v_isSharedCheck_3580_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_val_3495_);
lean_dec(v_a_3491_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3580_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v_fst_3499_; lean_object* v_snd_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3579_; 
v_fst_3499_ = lean_ctor_get(v_val_3495_, 0);
v_snd_3500_ = lean_ctor_get(v_val_3495_, 1);
v_isSharedCheck_3579_ = !lean_is_exclusive(v_val_3495_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3502_ = v_val_3495_;
v_isShared_3503_ = v_isSharedCheck_3579_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_snd_3500_);
lean_inc(v_fst_3499_);
lean_dec(v_val_3495_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3579_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v_mvarId_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3577_; 
v_mvarId_3504_ = lean_ctor_get(v_fst_3499_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v_fst_3499_);
if (v_isSharedCheck_3577_ == 0)
{
lean_object* v_unused_3578_; 
v_unused_3578_ = lean_ctor_get(v_fst_3499_, 1);
lean_dec(v_unused_3578_);
v___x_3506_ = v_fst_3499_;
v_isShared_3507_ = v_isSharedCheck_3577_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_mvarId_3504_);
lean_dec(v_fst_3499_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3577_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
uint8_t v___x_3508_; lean_object* v___x_3509_; 
v___x_3508_ = 0;
lean_inc(v_fvarId_3479_);
lean_inc(v_mvarId_3504_);
v___x_3509_ = l_Lean_Meta_simpIfLocalDecl(v_mvarId_3504_, v_fvarId_3479_, v___x_3508_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_object* v_a_3510_; lean_object* v_mvarId_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3567_; 
v_a_3510_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_a_3510_);
lean_dec_ref_known(v___x_3509_, 1);
v_mvarId_3511_ = lean_ctor_get(v_snd_3500_, 0);
v_isSharedCheck_3567_ = !lean_is_exclusive(v_snd_3500_);
if (v_isSharedCheck_3567_ == 0)
{
lean_object* v_unused_3568_; 
v_unused_3568_ = lean_ctor_get(v_snd_3500_, 1);
lean_dec(v_unused_3568_);
v___x_3513_ = v_snd_3500_;
v_isShared_3514_ = v_isSharedCheck_3567_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_mvarId_3511_);
lean_dec(v_snd_3500_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3567_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3515_; 
lean_inc(v_mvarId_3511_);
v___x_3515_ = l_Lean_Meta_simpIfLocalDecl(v_mvarId_3511_, v_fvarId_3479_, v___x_3508_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3558_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3518_ = v___x_3515_;
v_isShared_3519_ = v_isSharedCheck_3558_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3515_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3558_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
uint8_t v___x_3530_; 
v___x_3530_ = l_Lean_instBEqMVarId_beq(v_mvarId_3504_, v_a_3510_);
lean_dec(v_mvarId_3504_);
if (v___x_3530_ == 0)
{
lean_del_object(v___x_3513_);
lean_dec(v_mvarId_3511_);
lean_del_object(v___x_3506_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
goto v___jp_3520_;
}
else
{
uint8_t v___x_3531_; 
v___x_3531_ = l_Lean_instBEqMVarId_beq(v_mvarId_3511_, v_a_3516_);
lean_dec(v_mvarId_3511_);
if (v___x_3531_ == 0)
{
lean_del_object(v___x_3513_);
lean_del_object(v___x_3506_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
goto v___jp_3520_;
}
else
{
lean_object* v_options_3532_; uint8_t v_hasTrace_3533_; 
lean_del_object(v___x_3518_);
lean_del_object(v___x_3502_);
lean_del_object(v___x_3497_);
v_options_3532_ = lean_ctor_get(v___y_3482_, 2);
v_hasTrace_3533_ = lean_ctor_get_uint8(v_options_3532_, sizeof(void*)*1);
if (v_hasTrace_3533_ == 0)
{
lean_dec(v_a_3516_);
lean_del_object(v___x_3513_);
lean_dec(v_a_3510_);
lean_del_object(v___x_3506_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
goto v___jp_3485_;
}
else
{
lean_object* v_inheritedTraceOptions_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; uint8_t v___x_3537_; 
v_inheritedTraceOptions_3534_ = lean_ctor_get(v___y_3482_, 13);
v___x_3535_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1));
v___x_3536_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2);
v___x_3537_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3534_, v_options_3532_, v___x_3536_);
if (v___x_3537_ == 0)
{
lean_dec(v_a_3516_);
lean_del_object(v___x_3513_);
lean_dec(v_a_3510_);
lean_del_object(v___x_3506_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
goto v___jp_3485_;
}
else
{
lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3541_; 
v___x_3538_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4);
v___x_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3539_, 0, v_a_3510_);
if (v_isShared_3514_ == 0)
{
lean_ctor_set_tag(v___x_3513_, 7);
lean_ctor_set(v___x_3513_, 1, v___x_3539_);
lean_ctor_set(v___x_3513_, 0, v___x_3538_);
v___x_3541_ = v___x_3513_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3538_);
lean_ctor_set(v_reuseFailAlloc_3557_, 1, v___x_3539_);
v___x_3541_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
lean_object* v___x_3542_; lean_object* v___x_3544_; 
v___x_3542_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6);
if (v_isShared_3507_ == 0)
{
lean_ctor_set_tag(v___x_3506_, 7);
lean_ctor_set(v___x_3506_, 1, v___x_3542_);
lean_ctor_set(v___x_3506_, 0, v___x_3541_);
v___x_3544_ = v___x_3506_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v___x_3541_);
lean_ctor_set(v_reuseFailAlloc_3556_, 1, v___x_3542_);
v___x_3544_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3545_, 0, v_a_3516_);
v___x_3546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3544_);
lean_ctor_set(v___x_3546_, 1, v___x_3545_);
v___x_3547_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_3535_, v___x_3546_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_dec_ref_known(v___x_3547_, 1);
goto v___jp_3485_;
}
else
{
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3547_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3547_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3548_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
}
}
}
}
}
v___jp_3520_:
{
lean_object* v___x_3522_; 
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 1, v_a_3516_);
lean_ctor_set(v___x_3502_, 0, v_a_3510_);
v___x_3522_ = v___x_3502_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3510_);
lean_ctor_set(v_reuseFailAlloc_3529_, 1, v_a_3516_);
v___x_3522_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
lean_object* v___x_3524_; 
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 0, v___x_3522_);
v___x_3524_ = v___x_3497_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___x_3522_);
v___x_3524_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
lean_object* v___x_3526_; 
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 0, v___x_3524_);
v___x_3526_ = v___x_3518_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3524_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
}
}
}
else
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
lean_del_object(v___x_3513_);
lean_dec(v_mvarId_3511_);
lean_dec(v_a_3510_);
lean_del_object(v___x_3506_);
lean_dec(v_mvarId_3504_);
lean_del_object(v___x_3502_);
lean_del_object(v___x_3497_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
v_a_3559_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___x_3515_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3515_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3564_; 
if (v_isShared_3562_ == 0)
{
v___x_3564_ = v___x_3561_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3559_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
}
}
else
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_del_object(v___x_3506_);
lean_dec(v_mvarId_3504_);
lean_del_object(v___x_3502_);
lean_dec(v_snd_3500_);
lean_del_object(v___x_3497_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v_fvarId_3479_);
v_a_3569_ = lean_ctor_get(v___x_3509_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3509_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3509_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3581_; lean_object* v___x_3583_; 
lean_dec(v_a_3491_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v_fvarId_3479_);
v___x_3581_ = lean_box(0);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 0, v___x_3581_);
v___x_3583_ = v___x_3493_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v___x_3581_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
}
else
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3593_; 
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v_fvarId_3479_);
v_a_3586_ = lean_ctor_get(v___x_3490_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3588_ = v___x_3490_;
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___x_3490_);
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
else
{
lean_object* v_a_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3601_; 
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v_fvarId_3479_);
lean_dec(v_hName_x3f_3478_);
lean_dec(v_mvarId_3477_);
v_a_3594_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3596_ = v___x_3488_;
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_a_3594_);
lean_dec(v___x_3488_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3599_; 
if (v_isShared_3597_ == 0)
{
v___x_3599_ = v___x_3596_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_a_3594_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
v___jp_3485_:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3486_ = lean_box(0);
v___x_3487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3486_);
return v___x_3487_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___lam__0___boxed(lean_object* v___x_3602_, lean_object* v_mvarId_3603_, lean_object* v_hName_x3f_3604_, lean_object* v_fvarId_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l_Lean_Meta_splitIfLocalDecl_x3f___lam__0(v___x_3602_, v_mvarId_3603_, v_hName_x3f_3604_, v_fvarId_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f(lean_object* v_mvarId_3612_, lean_object* v_fvarId_3613_, lean_object* v_hName_x3f_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_){
_start:
{
lean_object* v___x_3620_; lean_object* v___f_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
lean_inc(v_fvarId_3613_);
v___x_3620_ = l_Lean_mkFVar(v_fvarId_3613_);
lean_inc(v_mvarId_3612_);
v___f_3621_ = lean_alloc_closure((void*)(l_Lean_Meta_splitIfLocalDecl_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3621_, 0, v___x_3620_);
lean_closure_set(v___f_3621_, 1, v_mvarId_3612_);
lean_closure_set(v___f_3621_, 2, v_hName_x3f_3614_);
lean_closure_set(v___f_3621_, 3, v_fvarId_3613_);
v___x_3622_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3622_, 0, lean_box(0));
lean_closure_set(v___x_3622_, 1, v_mvarId_3612_);
lean_closure_set(v___x_3622_, 2, v___f_3621_);
v___x_3623_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v___x_3622_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___boxed(lean_object* v_mvarId_3624_, lean_object* v_fvarId_3625_, lean_object* v_hName_x3f_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_){
_start:
{
lean_object* v_res_3632_; 
v_res_3632_ = l_Lean_Meta_splitIfLocalDecl_x3f(v_mvarId_3624_, v_fvarId_3625_, v_hName_x3f_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_);
lean_dec(v_a_3630_);
lean_dec_ref(v_a_3629_);
lean_dec(v_a_3628_);
lean_dec_ref(v_a_3627_);
return v_res_3632_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3653_ = lean_unsigned_to_nat(3526097586u);
v___x_3654_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_));
v___x_3655_ = l_Lean_Name_num___override(v___x_3654_, v___x_3653_);
return v___x_3655_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3657_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_));
v___x_3658_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3659_ = l_Lean_Name_str___override(v___x_3658_, v___x_3657_);
return v___x_3659_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3661_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_));
v___x_3662_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3663_ = l_Lean_Name_str___override(v___x_3662_, v___x_3661_);
return v___x_3663_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3664_ = lean_unsigned_to_nat(2u);
v___x_3665_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3666_ = l_Lean_Name_num___override(v___x_3665_, v___x_3664_);
return v___x_3666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3668_; uint8_t v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3668_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10));
v___x_3669_ = 0;
v___x_3670_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3671_ = l_Lean_registerTraceClass(v___x_3668_, v___x_3669_, v___x_3670_);
return v___x_3671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2____boxed(lean_object* v_a_3672_){
_start:
{
lean_object* v_res_3673_; 
v_res_3673_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_();
return v_res_3673_;
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
