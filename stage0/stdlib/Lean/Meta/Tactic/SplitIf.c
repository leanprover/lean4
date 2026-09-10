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
lean_object* l_Lean_LocalDecl_index(lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v_x_22__boxed_67_; uint8_t v_res_68_; lean_object* v_r_69_; 
v_x_22__boxed_67_ = lean_unbox(v_x_66_);
v_res_68_ = l_Lean_Meta_SplitKind_considerIte(v_x_22__boxed_67_);
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
uint8_t v_x_22__boxed_75_; uint8_t v_res_76_; lean_object* v_r_77_; 
v_x_22__boxed_75_ = lean_unbox(v_x_74_);
v_res_76_ = l_Lean_Meta_SplitKind_considerMatch(v_x_22__boxed_75_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg(lean_object* v_a_78_, lean_object* v_x_79_){
_start:
{
if (lean_obj_tag(v_x_79_) == 0)
{
uint8_t v___x_80_; 
v___x_80_ = 0;
return v___x_80_;
}
else
{
lean_object* v_key_81_; lean_object* v_tail_82_; uint8_t v___x_83_; 
v_key_81_ = lean_ctor_get(v_x_79_, 0);
v_tail_82_ = lean_ctor_get(v_x_79_, 2);
v___x_83_ = lean_expr_eqv(v_key_81_, v_a_78_);
if (v___x_83_ == 0)
{
v_x_79_ = v_tail_82_;
goto _start;
}
else
{
return v___x_83_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_85_, lean_object* v_x_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg(v_a_85_, v_x_86_);
lean_dec(v_x_86_);
lean_dec_ref(v_a_85_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(lean_object* v_m_89_, lean_object* v_a_90_){
_start:
{
lean_object* v_buckets_91_; lean_object* v___x_92_; uint64_t v___x_93_; uint64_t v___x_94_; uint64_t v___x_95_; uint64_t v_fold_96_; uint64_t v___x_97_; uint64_t v___x_98_; uint64_t v___x_99_; size_t v___x_100_; size_t v___x_101_; size_t v___x_102_; size_t v___x_103_; size_t v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v_buckets_91_ = lean_ctor_get(v_m_89_, 1);
v___x_92_ = lean_array_get_size(v_buckets_91_);
v___x_93_ = l_Lean_Expr_hash(v_a_90_);
v___x_94_ = 32ULL;
v___x_95_ = lean_uint64_shift_right(v___x_93_, v___x_94_);
v_fold_96_ = lean_uint64_xor(v___x_93_, v___x_95_);
v___x_97_ = 16ULL;
v___x_98_ = lean_uint64_shift_right(v_fold_96_, v___x_97_);
v___x_99_ = lean_uint64_xor(v_fold_96_, v___x_98_);
v___x_100_ = lean_uint64_to_usize(v___x_99_);
v___x_101_ = lean_usize_of_nat(v___x_92_);
v___x_102_ = ((size_t)1ULL);
v___x_103_ = lean_usize_sub(v___x_101_, v___x_102_);
v___x_104_ = lean_usize_land(v___x_100_, v___x_103_);
v___x_105_ = lean_array_uget_borrowed(v_buckets_91_, v___x_104_);
v___x_106_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg(v_a_90_, v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg___boxed(lean_object* v_m_107_, lean_object* v_a_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(v_m_107_, v_a_108_);
lean_dec_ref(v_a_108_);
lean_dec_ref(v_m_107_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg(lean_object* v_upperBound_119_, lean_object* v_args_120_, lean_object* v_a_121_, lean_object* v_b_122_){
_start:
{
uint8_t v___x_123_; 
v___x_123_ = lean_nat_dec_lt(v_a_121_, v_upperBound_119_);
if (v___x_123_ == 0)
{
lean_dec(v_a_121_);
lean_inc_ref(v_b_122_);
return v_b_122_;
}
else
{
lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_124_ = l_Lean_instInhabitedExpr;
v___x_125_ = lean_array_get_borrowed(v___x_124_, v_args_120_, v_a_121_);
v___x_126_ = l_Lean_Expr_hasLooseBVars(v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_127_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0));
v___x_128_ = lean_unsigned_to_nat(1u);
v___x_129_ = lean_nat_add(v_a_121_, v___x_128_);
lean_dec(v_a_121_);
v_a_121_ = v___x_129_;
v_b_122_ = v___x_127_;
goto _start;
}
else
{
lean_object* v___x_131_; 
lean_dec(v_a_121_);
v___x_131_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__2));
return v___x_131_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___boxed(lean_object* v_upperBound_132_, lean_object* v_args_133_, lean_object* v_a_134_, lean_object* v_b_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg(v_upperBound_132_, v_args_133_, v_a_134_, v_b_135_);
lean_dec_ref(v_b_135_);
lean_dec_ref(v_args_133_);
lean_dec(v_upperBound_132_);
return v_res_136_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0(void){
_start:
{
lean_object* v___x_137_; lean_object* v_dummy_138_; 
v___x_137_ = lean_box(0);
v_dummy_138_ = l_Lean_Expr_sort___override(v___x_137_);
return v_dummy_138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f(lean_object* v_env_145_, lean_object* v_ctx_146_, lean_object* v_e_147_){
_start:
{
lean_object* v_exceptionSet_148_; uint8_t v_kind_149_; lean_object* v_e_151_; uint8_t v___y_179_; uint8_t v___x_188_; 
v_exceptionSet_148_ = lean_ctor_get(v_ctx_146_, 0);
v_kind_149_ = lean_ctor_get_uint8(v_ctx_146_, sizeof(void*)*1);
v___x_188_ = l_Lean_Meta_SplitKind_considerIte(v_kind_149_);
if (v___x_188_ == 0)
{
goto v___jp_155_;
}
else
{
lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_189_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__2));
v___x_190_ = l_Lean_Expr_isAppOf(v_e_147_, v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_191_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__4));
v___x_192_ = l_Lean_Expr_isAppOf(v_e_147_, v___x_191_);
if (v___x_192_ == 0)
{
goto v___jp_155_;
}
else
{
v___y_179_ = v___x_192_;
goto v___jp_178_;
}
}
else
{
v___y_179_ = v___x_190_;
goto v___jp_178_;
}
}
v___jp_150_:
{
uint8_t v___x_152_; 
v___x_152_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(v_exceptionSet_148_, v_e_151_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; 
v___x_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_153_, 0, v_e_151_);
return v___x_153_;
}
else
{
lean_object* v___x_154_; 
lean_dec_ref(v_e_151_);
v___x_154_ = lean_box(0);
return v___x_154_;
}
}
v___jp_155_:
{
uint8_t v___x_156_; 
v___x_156_ = l_Lean_Meta_SplitKind_considerMatch(v_kind_149_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; 
lean_dec_ref(v_e_147_);
lean_dec_ref(v_env_145_);
v___x_157_ = lean_box(0);
return v___x_157_;
}
else
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_145_, v_e_147_);
if (lean_obj_tag(v___x_158_) == 1)
{
lean_object* v_val_159_; lean_object* v_numDiscrs_160_; lean_object* v_nargs_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v_dummy_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v_args_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v_fst_171_; 
v_val_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_val_159_);
lean_dec_ref_known(v___x_158_, 1);
v_numDiscrs_160_ = lean_ctor_get(v_val_159_, 1);
v_nargs_161_ = l_Lean_Expr_getAppNumArgs(v_e_147_);
v___x_162_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_159_);
v___x_163_ = lean_nat_add(v___x_162_, v_numDiscrs_160_);
v_dummy_164_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0);
lean_inc(v_nargs_161_);
v___x_165_ = lean_mk_array(v_nargs_161_, v_dummy_164_);
v___x_166_ = lean_unsigned_to_nat(1u);
v___x_167_ = lean_nat_sub(v_nargs_161_, v___x_166_);
lean_dec(v_nargs_161_);
lean_inc_ref(v_e_147_);
v_args_168_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_147_, v___x_165_, v___x_167_);
v___x_169_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0));
v___x_170_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg(v___x_163_, v_args_168_, v___x_162_, v___x_169_);
lean_dec(v___x_163_);
v_fst_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_fst_171_);
lean_dec_ref(v___x_170_);
if (lean_obj_tag(v_fst_171_) == 0)
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_172_ = lean_array_get_size(v_args_168_);
lean_dec_ref(v_args_168_);
v___x_173_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_159_);
lean_dec(v_val_159_);
v___x_174_ = lean_nat_sub(v___x_172_, v___x_173_);
lean_dec(v___x_173_);
v___x_175_ = l_Lean_Expr_getBoundedAppFn(v___x_174_, v_e_147_);
lean_dec_ref(v_e_147_);
v_e_151_ = v___x_175_;
goto v___jp_150_;
}
else
{
lean_object* v_val_176_; 
lean_dec_ref(v_args_168_);
lean_dec(v_val_159_);
lean_dec_ref(v_e_147_);
v_val_176_ = lean_ctor_get(v_fst_171_, 0);
lean_inc(v_val_176_);
lean_dec_ref_known(v_fst_171_, 1);
return v_val_176_;
}
}
else
{
lean_object* v___x_177_; 
lean_dec(v___x_158_);
lean_dec_ref(v_e_147_);
v___x_177_ = lean_box(0);
return v___x_177_;
}
}
}
v___jp_178_:
{
lean_object* v_numArgs_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v_numArgs_180_ = l_Lean_Expr_getAppNumArgs(v_e_147_);
v___x_181_ = lean_unsigned_to_nat(5u);
v___x_182_ = lean_nat_dec_le(v___x_181_, v_numArgs_180_);
if (v___x_182_ == 0)
{
lean_dec(v_numArgs_180_);
goto v___jp_155_;
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_183_ = lean_unsigned_to_nat(3u);
v___x_184_ = l_Lean_Expr_getRevArg_x21(v_e_147_, v___x_183_);
v___x_185_ = l_Lean_Expr_hasLooseBVars(v___x_184_);
lean_dec_ref(v___x_184_);
if (v___x_185_ == 0)
{
if (v___y_179_ == 0)
{
lean_dec(v_numArgs_180_);
goto v___jp_155_;
}
else
{
lean_object* v___x_186_; lean_object* v___x_187_; 
lean_dec_ref(v_env_145_);
v___x_186_ = lean_nat_sub(v_numArgs_180_, v___x_181_);
lean_dec(v_numArgs_180_);
v___x_187_ = l_Lean_Expr_getBoundedAppFn(v___x_186_, v_e_147_);
lean_dec_ref(v_e_147_);
v_e_151_ = v___x_187_;
goto v___jp_150_;
}
}
else
{
lean_dec(v_numArgs_180_);
goto v___jp_155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___boxed(lean_object* v_env_193_, lean_object* v_ctx_194_, lean_object* v_e_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f(v_env_193_, v_ctx_194_, v_e_195_);
lean_dec_ref(v_ctx_194_);
return v_res_196_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0(lean_object* v_00_u03b2_197_, lean_object* v_m_198_, lean_object* v_a_199_){
_start:
{
uint8_t v___x_200_; 
v___x_200_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(v_m_198_, v_a_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___boxed(lean_object* v_00_u03b2_201_, lean_object* v_m_202_, lean_object* v_a_203_){
_start:
{
uint8_t v_res_204_; lean_object* v_r_205_; 
v_res_204_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0(v_00_u03b2_201_, v_m_202_, v_a_203_);
lean_dec_ref(v_a_203_);
lean_dec_ref(v_m_202_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1(lean_object* v_upperBound_206_, lean_object* v_args_207_, lean_object* v_inst_208_, lean_object* v_R_209_, lean_object* v_a_210_, lean_object* v_b_211_, lean_object* v_c_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg(v_upperBound_206_, v_args_207_, v_a_210_, v_b_211_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___boxed(lean_object* v_upperBound_214_, lean_object* v_args_215_, lean_object* v_inst_216_, lean_object* v_R_217_, lean_object* v_a_218_, lean_object* v_b_219_, lean_object* v_c_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1(v_upperBound_214_, v_args_215_, v_inst_216_, v_R_217_, v_a_218_, v_b_219_, v_c_220_);
lean_dec_ref(v_b_219_);
lean_dec_ref(v_args_215_);
lean_dec(v_upperBound_214_);
return v_res_221_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0(lean_object* v_00_u03b2_222_, lean_object* v_a_223_, lean_object* v_x_224_){
_start:
{
uint8_t v___x_225_; 
v___x_225_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg(v_a_223_, v_x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_226_, lean_object* v_a_227_, lean_object* v_x_228_){
_start:
{
uint8_t v_res_229_; lean_object* v_r_230_; 
v_res_229_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0(v_00_u03b2_226_, v_a_227_, v_x_228_);
lean_dec(v_x_228_);
lean_dec_ref(v_a_227_);
v_r_230_ = lean_box(v_res_229_);
return v_r_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___redArg(lean_object* v_e_235_, lean_object* v_a_236_){
_start:
{
lean_object* v___f_238_; lean_object* v___f_239_; uint8_t v___x_240_; 
v___f_238_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__0));
v___f_239_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__1));
lean_inc_ref(v_e_235_);
v___x_240_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_238_, v___f_239_, v_a_236_, v_e_235_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_241_ = lean_box(0);
v___x_242_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_238_, v___f_239_, v_a_236_, v_e_235_, v___x_241_);
v___x_243_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__2));
v___x_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v___x_242_);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
else
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec_ref(v_e_235_);
v___x_246_ = lean_box(0);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v_a_236_);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___redArg___boxed(lean_object* v_e_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Meta_FindSplitImpl_checkVisited___redArg(v_e_249_, v_a_250_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited(lean_object* v_e_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_){
_start:
{
lean_object* v___f_261_; lean_object* v___f_262_; uint8_t v___x_263_; 
v___f_261_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__0));
v___f_262_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__1));
lean_inc_ref(v_e_253_);
v___x_263_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_261_, v___f_262_, v_a_255_, v_e_253_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_264_ = lean_box(0);
v___x_265_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_261_, v___f_262_, v_a_255_, v_e_253_, v___x_264_);
v___x_266_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__2));
v___x_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v___x_265_);
v___x_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
return v___x_268_;
}
else
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
lean_dec_ref(v_e_253_);
v___x_269_ = lean_box(0);
v___x_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v_a_255_);
v___x_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___boxed(lean_object* v_e_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Meta_FindSplitImpl_checkVisited(v_e_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec(v_a_276_);
lean_dec_ref(v_a_275_);
lean_dec_ref(v_a_273_);
return v_res_280_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(lean_object* v_a_281_, lean_object* v_x_282_){
_start:
{
if (lean_obj_tag(v_x_282_) == 0)
{
uint8_t v___x_283_; 
v___x_283_ = 0;
return v___x_283_;
}
else
{
lean_object* v_key_284_; lean_object* v_tail_285_; size_t v___x_286_; size_t v___x_287_; uint8_t v___x_288_; 
v_key_284_ = lean_ctor_get(v_x_282_, 0);
v_tail_285_ = lean_ctor_get(v_x_282_, 2);
v___x_286_ = lean_ptr_addr(v_key_284_);
v___x_287_ = lean_ptr_addr(v_a_281_);
v___x_288_ = lean_usize_dec_eq(v___x_286_, v___x_287_);
if (v___x_288_ == 0)
{
v_x_282_ = v_tail_285_;
goto _start;
}
else
{
return v___x_288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg___boxed(lean_object* v_a_290_, lean_object* v_x_291_){
_start:
{
uint8_t v_res_292_; lean_object* v_r_293_; 
v_res_292_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(v_a_290_, v_x_291_);
lean_dec(v_x_291_);
lean_dec_ref(v_a_290_);
v_r_293_ = lean_box(v_res_292_);
return v_r_293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6_spec__7___redArg(lean_object* v_x_294_, lean_object* v_x_295_){
_start:
{
if (lean_obj_tag(v_x_295_) == 0)
{
return v_x_294_;
}
else
{
lean_object* v_key_296_; lean_object* v_value_297_; lean_object* v_tail_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_324_; 
v_key_296_ = lean_ctor_get(v_x_295_, 0);
v_value_297_ = lean_ctor_get(v_x_295_, 1);
v_tail_298_ = lean_ctor_get(v_x_295_, 2);
v_isSharedCheck_324_ = !lean_is_exclusive(v_x_295_);
if (v_isSharedCheck_324_ == 0)
{
v___x_300_ = v_x_295_;
v_isShared_301_ = v_isSharedCheck_324_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_tail_298_);
lean_inc(v_value_297_);
lean_inc(v_key_296_);
lean_dec(v_x_295_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_324_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; size_t v___x_303_; uint64_t v___x_304_; uint64_t v___x_305_; uint64_t v___x_306_; uint64_t v___x_307_; uint64_t v___x_308_; uint64_t v_fold_309_; uint64_t v___x_310_; uint64_t v___x_311_; uint64_t v___x_312_; size_t v___x_313_; size_t v___x_314_; size_t v___x_315_; size_t v___x_316_; size_t v___x_317_; lean_object* v___x_318_; lean_object* v___x_320_; 
v___x_302_ = lean_array_get_size(v_x_294_);
v___x_303_ = lean_ptr_addr(v_key_296_);
v___x_304_ = lean_usize_to_uint64(v___x_303_);
v___x_305_ = 11ULL;
v___x_306_ = lean_uint64_mix_hash(v___x_304_, v___x_305_);
v___x_307_ = 32ULL;
v___x_308_ = lean_uint64_shift_right(v___x_306_, v___x_307_);
v_fold_309_ = lean_uint64_xor(v___x_306_, v___x_308_);
v___x_310_ = 16ULL;
v___x_311_ = lean_uint64_shift_right(v_fold_309_, v___x_310_);
v___x_312_ = lean_uint64_xor(v_fold_309_, v___x_311_);
v___x_313_ = lean_uint64_to_usize(v___x_312_);
v___x_314_ = lean_usize_of_nat(v___x_302_);
v___x_315_ = ((size_t)1ULL);
v___x_316_ = lean_usize_sub(v___x_314_, v___x_315_);
v___x_317_ = lean_usize_land(v___x_313_, v___x_316_);
v___x_318_ = lean_array_uget_borrowed(v_x_294_, v___x_317_);
lean_inc(v___x_318_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 2, v___x_318_);
v___x_320_ = v___x_300_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_key_296_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v_value_297_);
lean_ctor_set(v_reuseFailAlloc_323_, 2, v___x_318_);
v___x_320_ = v_reuseFailAlloc_323_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_321_; 
v___x_321_ = lean_array_uset(v_x_294_, v___x_317_, v___x_320_);
v_x_294_ = v___x_321_;
v_x_295_ = v_tail_298_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6___redArg(lean_object* v_i_325_, lean_object* v_source_326_, lean_object* v_target_327_){
_start:
{
lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_328_ = lean_array_get_size(v_source_326_);
v___x_329_ = lean_nat_dec_lt(v_i_325_, v___x_328_);
if (v___x_329_ == 0)
{
lean_dec_ref(v_source_326_);
lean_dec(v_i_325_);
return v_target_327_;
}
else
{
lean_object* v_es_330_; lean_object* v___x_331_; lean_object* v_source_332_; lean_object* v_target_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v_es_330_ = lean_array_fget(v_source_326_, v_i_325_);
v___x_331_ = lean_box(0);
v_source_332_ = lean_array_fset(v_source_326_, v_i_325_, v___x_331_);
v_target_333_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6_spec__7___redArg(v_target_327_, v_es_330_);
v___x_334_ = lean_unsigned_to_nat(1u);
v___x_335_ = lean_nat_add(v_i_325_, v___x_334_);
lean_dec(v_i_325_);
v_i_325_ = v___x_335_;
v_source_326_ = v_source_332_;
v_target_327_ = v_target_333_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5___redArg(lean_object* v_data_337_){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v_nbuckets_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_338_ = lean_array_get_size(v_data_337_);
v___x_339_ = lean_unsigned_to_nat(2u);
v_nbuckets_340_ = lean_nat_mul(v___x_338_, v___x_339_);
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = lean_box(0);
v___x_343_ = lean_mk_array(v_nbuckets_340_, v___x_342_);
v___x_344_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6___redArg(v___x_341_, v_data_337_, v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4___redArg(lean_object* v_m_345_, lean_object* v_a_346_, lean_object* v_b_347_){
_start:
{
lean_object* v_size_348_; lean_object* v_buckets_349_; lean_object* v___x_350_; size_t v___x_351_; uint64_t v___x_352_; uint64_t v___x_353_; uint64_t v___x_354_; uint64_t v___x_355_; uint64_t v___x_356_; uint64_t v_fold_357_; uint64_t v___x_358_; uint64_t v___x_359_; uint64_t v___x_360_; size_t v___x_361_; size_t v___x_362_; size_t v___x_363_; size_t v___x_364_; size_t v___x_365_; lean_object* v_bkt_366_; uint8_t v___x_367_; 
v_size_348_ = lean_ctor_get(v_m_345_, 0);
v_buckets_349_ = lean_ctor_get(v_m_345_, 1);
v___x_350_ = lean_array_get_size(v_buckets_349_);
v___x_351_ = lean_ptr_addr(v_a_346_);
v___x_352_ = lean_usize_to_uint64(v___x_351_);
v___x_353_ = 11ULL;
v___x_354_ = lean_uint64_mix_hash(v___x_352_, v___x_353_);
v___x_355_ = 32ULL;
v___x_356_ = lean_uint64_shift_right(v___x_354_, v___x_355_);
v_fold_357_ = lean_uint64_xor(v___x_354_, v___x_356_);
v___x_358_ = 16ULL;
v___x_359_ = lean_uint64_shift_right(v_fold_357_, v___x_358_);
v___x_360_ = lean_uint64_xor(v_fold_357_, v___x_359_);
v___x_361_ = lean_uint64_to_usize(v___x_360_);
v___x_362_ = lean_usize_of_nat(v___x_350_);
v___x_363_ = ((size_t)1ULL);
v___x_364_ = lean_usize_sub(v___x_362_, v___x_363_);
v___x_365_ = lean_usize_land(v___x_361_, v___x_364_);
v_bkt_366_ = lean_array_uget_borrowed(v_buckets_349_, v___x_365_);
v___x_367_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(v_a_346_, v_bkt_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_388_; 
lean_inc_ref(v_buckets_349_);
lean_inc(v_size_348_);
v_isSharedCheck_388_ = !lean_is_exclusive(v_m_345_);
if (v_isSharedCheck_388_ == 0)
{
lean_object* v_unused_389_; lean_object* v_unused_390_; 
v_unused_389_ = lean_ctor_get(v_m_345_, 1);
lean_dec(v_unused_389_);
v_unused_390_ = lean_ctor_get(v_m_345_, 0);
lean_dec(v_unused_390_);
v___x_369_ = v_m_345_;
v_isShared_370_ = v_isSharedCheck_388_;
goto v_resetjp_368_;
}
else
{
lean_dec(v_m_345_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_388_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; lean_object* v_size_x27_372_; lean_object* v___x_373_; lean_object* v_buckets_x27_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_371_ = lean_unsigned_to_nat(1u);
v_size_x27_372_ = lean_nat_add(v_size_348_, v___x_371_);
lean_dec(v_size_348_);
lean_inc(v_bkt_366_);
v___x_373_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_373_, 0, v_a_346_);
lean_ctor_set(v___x_373_, 1, v_b_347_);
lean_ctor_set(v___x_373_, 2, v_bkt_366_);
v_buckets_x27_374_ = lean_array_uset(v_buckets_349_, v___x_365_, v___x_373_);
v___x_375_ = lean_unsigned_to_nat(4u);
v___x_376_ = lean_nat_mul(v_size_x27_372_, v___x_375_);
v___x_377_ = lean_unsigned_to_nat(3u);
v___x_378_ = lean_nat_div(v___x_376_, v___x_377_);
lean_dec(v___x_376_);
v___x_379_ = lean_array_get_size(v_buckets_x27_374_);
v___x_380_ = lean_nat_dec_le(v___x_378_, v___x_379_);
lean_dec(v___x_378_);
if (v___x_380_ == 0)
{
lean_object* v_val_381_; lean_object* v___x_383_; 
v_val_381_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5___redArg(v_buckets_x27_374_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v_val_381_);
lean_ctor_set(v___x_369_, 0, v_size_x27_372_);
v___x_383_ = v___x_369_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_size_x27_372_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v_val_381_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
else
{
lean_object* v___x_386_; 
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v_buckets_x27_374_);
lean_ctor_set(v___x_369_, 0, v_size_x27_372_);
v___x_386_ = v___x_369_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_size_x27_372_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v_buckets_x27_374_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
else
{
lean_dec(v_b_347_);
lean_dec_ref(v_a_346_);
return v_m_345_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg(lean_object* v_m_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_buckets_393_; lean_object* v___x_394_; size_t v___x_395_; uint64_t v___x_396_; uint64_t v___x_397_; uint64_t v___x_398_; uint64_t v___x_399_; uint64_t v___x_400_; uint64_t v_fold_401_; uint64_t v___x_402_; uint64_t v___x_403_; uint64_t v___x_404_; size_t v___x_405_; size_t v___x_406_; size_t v___x_407_; size_t v___x_408_; size_t v___x_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v_buckets_393_ = lean_ctor_get(v_m_391_, 1);
v___x_394_ = lean_array_get_size(v_buckets_393_);
v___x_395_ = lean_ptr_addr(v_a_392_);
v___x_396_ = lean_usize_to_uint64(v___x_395_);
v___x_397_ = 11ULL;
v___x_398_ = lean_uint64_mix_hash(v___x_396_, v___x_397_);
v___x_399_ = 32ULL;
v___x_400_ = lean_uint64_shift_right(v___x_398_, v___x_399_);
v_fold_401_ = lean_uint64_xor(v___x_398_, v___x_400_);
v___x_402_ = 16ULL;
v___x_403_ = lean_uint64_shift_right(v_fold_401_, v___x_402_);
v___x_404_ = lean_uint64_xor(v_fold_401_, v___x_403_);
v___x_405_ = lean_uint64_to_usize(v___x_404_);
v___x_406_ = lean_usize_of_nat(v___x_394_);
v___x_407_ = ((size_t)1ULL);
v___x_408_ = lean_usize_sub(v___x_406_, v___x_407_);
v___x_409_ = lean_usize_land(v___x_405_, v___x_408_);
v___x_410_ = lean_array_uget_borrowed(v_buckets_393_, v___x_409_);
v___x_411_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(v_a_392_, v___x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg___boxed(lean_object* v_m_412_, lean_object* v_a_413_){
_start:
{
uint8_t v_res_414_; lean_object* v_r_415_; 
v_res_414_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg(v_m_412_, v_a_413_);
lean_dec_ref(v_a_413_);
lean_dec_ref(v_m_412_);
v_r_415_ = lean_box(v_res_414_);
return v_r_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_visit(lean_object* v_e_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_){
_start:
{
lean_object* v___y_425_; lean_object* v___y_426_; lean_object* v___y_427_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___y_430_; uint8_t v___x_455_; 
v___x_455_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg(v_a_418_, v_e_416_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; lean_object* v_env_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_456_ = lean_st_ref_get(v_a_422_);
v_env_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc_ref(v_env_457_);
lean_dec(v___x_456_);
v___x_458_ = lean_box(0);
lean_inc_ref_n(v_e_416_, 2);
v___x_459_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4___redArg(v_a_418_, v_e_416_, v___x_458_);
v___x_460_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f(v_env_457_, v_a_417_, v_e_416_);
if (lean_obj_tag(v___x_460_) == 1)
{
lean_object* v___x_461_; lean_object* v___x_462_; 
lean_dec_ref(v_e_416_);
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
lean_ctor_set(v___x_461_, 1, v___x_459_);
v___x_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
return v___x_462_;
}
else
{
uint8_t v___x_463_; 
lean_dec(v___x_460_);
v___x_463_ = l_Lean_Expr_hasLooseBVars(v_e_416_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; 
lean_inc_ref(v_e_416_);
v___x_464_ = l_Lean_Meta_isProof(v_e_416_, v_a_419_, v_a_420_, v_a_421_, v_a_422_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_475_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_475_ == 0)
{
v___x_467_ = v___x_464_;
v_isShared_468_ = v_isSharedCheck_475_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_464_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_475_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
uint8_t v___x_469_; 
v___x_469_ = lean_unbox(v_a_465_);
lean_dec(v_a_465_);
if (v___x_469_ == 0)
{
lean_del_object(v___x_467_);
v___y_425_ = v_a_417_;
v___y_426_ = v___x_459_;
v___y_427_ = v_a_419_;
v___y_428_ = v_a_420_;
v___y_429_ = v_a_421_;
v___y_430_ = v_a_422_;
goto v___jp_424_;
}
else
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_473_; 
lean_dec_ref(v_e_416_);
v___x_470_ = lean_box(0);
v___x_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v___x_459_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 0, v___x_471_);
v___x_473_ = v___x_467_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
lean_dec_ref(v___x_459_);
lean_dec_ref(v_e_416_);
v_a_476_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_464_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_464_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
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
v___y_425_ = v_a_417_;
v___y_426_ = v___x_459_;
v___y_427_ = v_a_419_;
v___y_428_ = v_a_420_;
v___y_429_ = v_a_421_;
v___y_430_ = v_a_422_;
goto v___jp_424_;
}
}
}
else
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
lean_dec_ref(v_e_416_);
v___x_484_ = lean_box(0);
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
lean_ctor_set(v___x_485_, 1, v_a_418_);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
v___jp_424_:
{
switch(lean_obj_tag(v_e_416_))
{
case 6:
{
lean_object* v_body_431_; 
v_body_431_ = lean_ctor_get(v_e_416_, 2);
lean_inc_ref(v_body_431_);
lean_dec_ref_known(v_e_416_, 3);
v_e_416_ = v_body_431_;
v_a_417_ = v___y_425_;
v_a_418_ = v___y_426_;
v_a_419_ = v___y_427_;
v_a_420_ = v___y_428_;
v_a_421_ = v___y_429_;
v_a_422_ = v___y_430_;
goto _start;
}
case 11:
{
lean_object* v_struct_433_; 
v_struct_433_ = lean_ctor_get(v_e_416_, 2);
lean_inc_ref(v_struct_433_);
lean_dec_ref_known(v_e_416_, 3);
v_e_416_ = v_struct_433_;
v_a_417_ = v___y_425_;
v_a_418_ = v___y_426_;
v_a_419_ = v___y_427_;
v_a_420_ = v___y_428_;
v_a_421_ = v___y_429_;
v_a_422_ = v___y_430_;
goto _start;
}
case 10:
{
lean_object* v_expr_435_; 
v_expr_435_ = lean_ctor_get(v_e_416_, 1);
lean_inc_ref(v_expr_435_);
lean_dec_ref_known(v_e_416_, 2);
v_e_416_ = v_expr_435_;
v_a_417_ = v___y_425_;
v_a_418_ = v___y_426_;
v_a_419_ = v___y_427_;
v_a_420_ = v___y_428_;
v_a_421_ = v___y_429_;
v_a_422_ = v___y_430_;
goto _start;
}
case 7:
{
lean_object* v_binderType_437_; lean_object* v_body_438_; lean_object* v___x_439_; 
v_binderType_437_ = lean_ctor_get(v_e_416_, 1);
lean_inc_ref(v_binderType_437_);
v_body_438_ = lean_ctor_get(v_e_416_, 2);
lean_inc_ref(v_body_438_);
lean_dec_ref_known(v_e_416_, 3);
v___x_439_ = l_Lean_Meta_FindSplitImpl_visit(v_binderType_437_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v_fst_441_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_a_440_);
v_fst_441_ = lean_ctor_get(v_a_440_, 0);
if (lean_obj_tag(v_fst_441_) == 0)
{
lean_object* v_snd_442_; 
lean_dec_ref_known(v___x_439_, 1);
v_snd_442_ = lean_ctor_get(v_a_440_, 1);
lean_inc(v_snd_442_);
lean_dec(v_a_440_);
v_e_416_ = v_body_438_;
v_a_417_ = v___y_425_;
v_a_418_ = v_snd_442_;
v_a_419_ = v___y_427_;
v_a_420_ = v___y_428_;
v_a_421_ = v___y_429_;
v_a_422_ = v___y_430_;
goto _start;
}
else
{
lean_dec(v_a_440_);
lean_dec_ref(v_body_438_);
return v___x_439_;
}
}
else
{
lean_dec_ref(v_body_438_);
return v___x_439_;
}
}
case 8:
{
lean_object* v_value_444_; lean_object* v_body_445_; lean_object* v___x_446_; 
v_value_444_ = lean_ctor_get(v_e_416_, 2);
lean_inc_ref(v_value_444_);
v_body_445_ = lean_ctor_get(v_e_416_, 3);
lean_inc_ref(v_body_445_);
lean_dec_ref_known(v_e_416_, 4);
v___x_446_ = l_Lean_Meta_FindSplitImpl_visit(v_value_444_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v_fst_448_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_a_447_);
v_fst_448_ = lean_ctor_get(v_a_447_, 0);
if (lean_obj_tag(v_fst_448_) == 0)
{
lean_object* v_snd_449_; 
lean_dec_ref_known(v___x_446_, 1);
v_snd_449_ = lean_ctor_get(v_a_447_, 1);
lean_inc(v_snd_449_);
lean_dec(v_a_447_);
v_e_416_ = v_body_445_;
v_a_417_ = v___y_425_;
v_a_418_ = v_snd_449_;
v_a_419_ = v___y_427_;
v_a_420_ = v___y_428_;
v_a_421_ = v___y_429_;
v_a_422_ = v___y_430_;
goto _start;
}
else
{
lean_dec(v_a_447_);
lean_dec_ref(v_body_445_);
return v___x_446_;
}
}
else
{
lean_dec_ref(v_body_445_);
return v___x_446_;
}
}
case 5:
{
lean_object* v___x_451_; 
v___x_451_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f(v_e_416_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
return v___x_451_;
}
default: 
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
lean_dec_ref(v_e_416_);
v___x_452_ = lean_box(0);
v___x_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v___y_426_);
v___x_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
return v___x_454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(lean_object* v_upperBound_487_, lean_object* v_args_488_, lean_object* v_info_489_, lean_object* v_a_490_, lean_object* v_b_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v_a_500_; lean_object* v_snd_501_; lean_object* v_a_505_; lean_object* v_snd_506_; uint8_t v___x_510_; 
v___x_510_ = lean_nat_dec_lt(v_a_490_, v_upperBound_487_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; lean_object* v___x_512_; 
lean_dec(v_a_490_);
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v_b_491_);
lean_ctor_set(v___x_511_, 1, v___y_493_);
v___x_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
return v___x_512_;
}
else
{
lean_object* v_paramInfo_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
lean_dec_ref(v_b_491_);
v_paramInfo_513_ = lean_ctor_get(v_info_489_, 0);
v___x_514_ = lean_box(0);
v___x_515_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0));
v___x_516_ = lean_array_fget_borrowed(v_args_488_, v_a_490_);
v___x_517_ = lean_array_get_size(v_paramInfo_513_);
v___x_518_ = lean_nat_dec_lt(v_a_490_, v___x_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; 
lean_inc(v___x_516_);
v___x_519_ = l_Lean_Meta_FindSplitImpl_visit(v___x_516_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v_fst_521_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref_known(v___x_519_, 1);
v_fst_521_ = lean_ctor_get(v_a_520_, 0);
if (lean_obj_tag(v_fst_521_) == 1)
{
lean_object* v_snd_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_530_; 
lean_inc_ref(v_fst_521_);
lean_dec(v_a_490_);
v_snd_522_ = lean_ctor_get(v_a_520_, 1);
v_isSharedCheck_530_ = !lean_is_exclusive(v_a_520_);
if (v_isSharedCheck_530_ == 0)
{
lean_object* v_unused_531_; 
v_unused_531_ = lean_ctor_get(v_a_520_, 0);
lean_dec(v_unused_531_);
v___x_524_ = v_a_520_;
v_isShared_525_ = v_isSharedCheck_530_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_snd_522_);
lean_dec(v_a_520_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_530_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_526_, 0, v_fst_521_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 1, v___x_514_);
lean_ctor_set(v___x_524_, 0, v___x_526_);
v___x_528_ = v___x_524_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v___x_514_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
v_a_500_ = v___x_528_;
v_snd_501_ = v_snd_522_;
goto v___jp_499_;
}
}
}
else
{
lean_object* v_snd_532_; 
v_snd_532_ = lean_ctor_get(v_a_520_, 1);
lean_inc(v_snd_532_);
lean_dec(v_a_520_);
v_a_505_ = v___x_515_;
v_snd_506_ = v_snd_532_;
goto v___jp_504_;
}
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
lean_dec(v_a_490_);
v_a_533_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_519_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_519_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
else
{
lean_object* v___x_541_; uint8_t v_isProp_542_; 
v___x_541_ = lean_array_fget_borrowed(v_paramInfo_513_, v_a_490_);
v_isProp_542_ = lean_ctor_get_uint8(v___x_541_, sizeof(void*)*1 + 2);
if (v_isProp_542_ == 0)
{
uint8_t v___x_543_; 
v___x_543_ = l_Lean_Meta_ParamInfo_isExplicit(v___x_541_);
if (v___x_543_ == 0)
{
v_a_505_ = v___x_515_;
v_snd_506_ = v___y_493_;
goto v___jp_504_;
}
else
{
lean_object* v___x_544_; 
lean_inc(v___x_516_);
v___x_544_ = l_Lean_Meta_FindSplitImpl_visit(v___x_516_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; lean_object* v_fst_546_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_545_);
lean_dec_ref_known(v___x_544_, 1);
v_fst_546_ = lean_ctor_get(v_a_545_, 0);
if (lean_obj_tag(v_fst_546_) == 1)
{
lean_object* v_snd_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_555_; 
lean_inc_ref(v_fst_546_);
lean_dec(v_a_490_);
v_snd_547_ = lean_ctor_get(v_a_545_, 1);
v_isSharedCheck_555_ = !lean_is_exclusive(v_a_545_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; 
v_unused_556_ = lean_ctor_get(v_a_545_, 0);
lean_dec(v_unused_556_);
v___x_549_ = v_a_545_;
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_snd_547_);
lean_dec(v_a_545_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_551_, 0, v_fst_546_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 1, v___x_514_);
lean_ctor_set(v___x_549_, 0, v___x_551_);
v___x_553_ = v___x_549_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v___x_514_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
v_a_500_ = v___x_553_;
v_snd_501_ = v_snd_547_;
goto v___jp_499_;
}
}
}
else
{
lean_object* v_snd_557_; 
v_snd_557_ = lean_ctor_get(v_a_545_, 1);
lean_inc(v_snd_557_);
lean_dec(v_a_545_);
v_a_505_ = v___x_515_;
v_snd_506_ = v_snd_557_;
goto v___jp_504_;
}
}
else
{
lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_565_; 
lean_dec(v_a_490_);
v_a_558_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_565_ == 0)
{
v___x_560_ = v___x_544_;
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_544_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_563_; 
if (v_isShared_561_ == 0)
{
v___x_563_ = v___x_560_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_a_558_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
}
else
{
v_a_505_ = v___x_515_;
v_snd_506_ = v___y_493_;
goto v___jp_504_;
}
}
}
v___jp_499_:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_502_, 0, v_a_500_);
lean_ctor_set(v___x_502_, 1, v_snd_501_);
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
v___jp_504_:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_unsigned_to_nat(1u);
v___x_508_ = lean_nat_add(v_a_490_, v___x_507_);
lean_dec(v_a_490_);
lean_inc_ref(v_a_505_);
v_a_490_ = v___x_508_;
v_b_491_ = v_a_505_;
v___y_493_ = v_snd_506_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1(lean_object* v_x_570_, lean_object* v_x_571_, lean_object* v_x_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v_info_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; 
if (lean_obj_tag(v_x_570_) == 5)
{
lean_object* v_fn_622_; lean_object* v_arg_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v_fn_622_ = lean_ctor_get(v_x_570_, 0);
lean_inc_ref(v_fn_622_);
v_arg_623_ = lean_ctor_get(v_x_570_, 1);
lean_inc_ref(v_arg_623_);
lean_dec_ref_known(v_x_570_, 2);
v___x_624_ = lean_array_set(v_x_571_, v_x_572_, v_arg_623_);
v___x_625_ = lean_unsigned_to_nat(1u);
v___x_626_ = lean_nat_sub(v_x_572_, v___x_625_);
lean_dec(v_x_572_);
v_x_570_ = v_fn_622_;
v_x_571_ = v___x_624_;
v_x_572_ = v___x_626_;
goto _start;
}
else
{
uint8_t v___x_628_; 
lean_dec(v_x_572_);
v___x_628_ = l_Lean_Expr_hasLooseBVars(v_x_570_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_box(0);
lean_inc_ref(v_x_570_);
v___x_630_ = l_Lean_Meta_getFunInfo(v_x_570_, v___x_629_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_631_);
lean_dec_ref_known(v___x_630_, 1);
v_info_581_ = v_a_631_;
v___y_582_ = v___y_573_;
v___y_583_ = v___y_574_;
v___y_584_ = v___y_575_;
v___y_585_ = v___y_576_;
v___y_586_ = v___y_577_;
v___y_587_ = v___y_578_;
goto v___jp_580_;
}
else
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
lean_dec_ref(v___y_574_);
lean_dec_ref(v_x_571_);
lean_dec_ref(v_x_570_);
v_a_632_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_630_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_630_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
else
{
lean_object* v___x_640_; 
v___x_640_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___closed__1));
v_info_581_ = v___x_640_;
v___y_582_ = v___y_573_;
v___y_583_ = v___y_574_;
v___y_584_ = v___y_575_;
v___y_585_ = v___y_576_;
v___y_586_ = v___y_577_;
v___y_587_ = v___y_578_;
goto v___jp_580_;
}
}
v___jp_580_:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_588_ = lean_array_get_size(v_x_571_);
v___x_589_ = lean_unsigned_to_nat(0u);
v___x_590_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0));
v___x_591_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(v___x_588_, v_x_571_, v_info_581_, v___x_589_, v___x_590_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
lean_dec_ref(v_info_581_);
lean_dec_ref(v_x_571_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_613_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_613_ == 0)
{
v___x_594_ = v___x_591_;
v_isShared_595_ = v_isSharedCheck_613_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_591_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_613_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v_fst_596_; lean_object* v_fst_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_611_; 
v_fst_596_ = lean_ctor_get(v_a_592_, 0);
lean_inc(v_fst_596_);
v_fst_597_ = lean_ctor_get(v_fst_596_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v_fst_596_);
if (v_isSharedCheck_611_ == 0)
{
lean_object* v_unused_612_; 
v_unused_612_ = lean_ctor_get(v_fst_596_, 1);
lean_dec(v_unused_612_);
v___x_599_ = v_fst_596_;
v_isShared_600_ = v_isSharedCheck_611_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_fst_597_);
lean_dec(v_fst_596_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_611_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
if (lean_obj_tag(v_fst_597_) == 0)
{
lean_object* v_snd_601_; lean_object* v___x_602_; 
lean_del_object(v___x_599_);
lean_del_object(v___x_594_);
v_snd_601_ = lean_ctor_get(v_a_592_, 1);
lean_inc(v_snd_601_);
lean_dec(v_a_592_);
v___x_602_ = l_Lean_Meta_FindSplitImpl_visit(v_x_570_, v___y_582_, v_snd_601_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
return v___x_602_;
}
else
{
lean_object* v_snd_603_; lean_object* v_val_604_; lean_object* v___x_606_; 
lean_dec_ref(v_x_570_);
v_snd_603_ = lean_ctor_get(v_a_592_, 1);
lean_inc(v_snd_603_);
lean_dec(v_a_592_);
v_val_604_ = lean_ctor_get(v_fst_597_, 0);
lean_inc(v_val_604_);
lean_dec_ref_known(v_fst_597_, 1);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 1, v_snd_603_);
lean_ctor_set(v___x_599_, 0, v_val_604_);
v___x_606_ = v___x_599_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_val_604_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_snd_603_);
v___x_606_ = v_reuseFailAlloc_610_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_608_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_606_);
v___x_608_ = v___x_594_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
}
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
lean_dec_ref(v_x_570_);
v_a_614_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_591_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_591_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f(lean_object* v_e_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_dummy_649_; lean_object* v_nargs_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v_dummy_649_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0);
v_nargs_650_ = l_Lean_Expr_getAppNumArgs(v_e_641_);
lean_inc(v_nargs_650_);
v___x_651_ = lean_mk_array(v_nargs_650_, v_dummy_649_);
v___x_652_ = lean_unsigned_to_nat(1u);
v___x_653_ = lean_nat_sub(v_nargs_650_, v___x_652_);
lean_dec(v_nargs_650_);
v___x_654_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1(v_e_641_, v___x_651_, v___x_653_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f___boxed(lean_object* v_e_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f(v_e_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
lean_dec(v_a_659_);
lean_dec_ref(v_a_658_);
lean_dec_ref(v_a_656_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___boxed(lean_object* v_x_664_, lean_object* v_x_665_, lean_object* v_x_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1(v_x_664_, v_x_665_, v_x_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec_ref(v___y_667_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg___boxed(lean_object* v_upperBound_675_, lean_object* v_args_676_, lean_object* v_info_677_, lean_object* v_a_678_, lean_object* v_b_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(v_upperBound_675_, v_args_676_, v_info_677_, v_a_678_, v_b_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec_ref(v___y_680_);
lean_dec_ref(v_info_677_);
lean_dec_ref(v_args_676_);
lean_dec(v_upperBound_675_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_visit___boxed(lean_object* v_e_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Lean_Meta_FindSplitImpl_visit(v_e_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
lean_dec_ref(v_a_689_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0(lean_object* v_upperBound_697_, lean_object* v_args_698_, lean_object* v_info_699_, lean_object* v_inst_700_, lean_object* v_R_701_, lean_object* v_a_702_, lean_object* v_b_703_, lean_object* v_c_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(v_upperBound_697_, v_args_698_, v_info_699_, v_a_702_, v_b_703_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___boxed(lean_object* v_upperBound_713_, lean_object* v_args_714_, lean_object* v_info_715_, lean_object* v_inst_716_, lean_object* v_R_717_, lean_object* v_a_718_, lean_object* v_b_719_, lean_object* v_c_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0(v_upperBound_713_, v_args_714_, v_info_715_, v_inst_716_, v_R_717_, v_a_718_, v_b_719_, v_c_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec_ref(v___y_721_);
lean_dec_ref(v_info_715_);
lean_dec_ref(v_args_714_);
lean_dec(v_upperBound_713_);
return v_res_728_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3(lean_object* v_00_u03b2_729_, lean_object* v_m_730_, lean_object* v_a_731_){
_start:
{
uint8_t v___x_732_; 
v___x_732_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg(v_m_730_, v_a_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___boxed(lean_object* v_00_u03b2_733_, lean_object* v_m_734_, lean_object* v_a_735_){
_start:
{
uint8_t v_res_736_; lean_object* v_r_737_; 
v_res_736_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3(v_00_u03b2_733_, v_m_734_, v_a_735_);
lean_dec_ref(v_a_735_);
lean_dec_ref(v_m_734_);
v_r_737_ = lean_box(v_res_736_);
return v_r_737_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4(lean_object* v_00_u03b2_738_, lean_object* v_m_739_, lean_object* v_a_740_, lean_object* v_b_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4___redArg(v_m_739_, v_a_740_, v_b_741_);
return v___x_742_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3(lean_object* v_00_u03b2_743_, lean_object* v_a_744_, lean_object* v_x_745_){
_start:
{
uint8_t v___x_746_; 
v___x_746_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(v_a_744_, v_x_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___boxed(lean_object* v_00_u03b2_747_, lean_object* v_a_748_, lean_object* v_x_749_){
_start:
{
uint8_t v_res_750_; lean_object* v_r_751_; 
v_res_750_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3(v_00_u03b2_747_, v_a_748_, v_x_749_);
lean_dec(v_x_749_);
lean_dec_ref(v_a_748_);
v_r_751_ = lean_box(v_res_750_);
return v_r_751_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5(lean_object* v_00_u03b2_752_, lean_object* v_data_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5___redArg(v_data_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_755_, lean_object* v_i_756_, lean_object* v_source_757_, lean_object* v_target_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6___redArg(v_i_756_, v_source_757_, v_target_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_760_, lean_object* v_x_761_, lean_object* v_x_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6_spec__7___redArg(v_x_761_, v_x_762_);
return v___x_763_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = lean_unsigned_to_nat(64u);
v___x_765_ = l_Lean_mkPtrSet___redArg(v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1(uint8_t v_kind_766_, lean_object* v_exceptionSet_767_, lean_object* v_e_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_774_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_774_, 0, v_exceptionSet_767_);
lean_ctor_set_uint8(v___x_774_, sizeof(void*)*1, v_kind_766_);
v___x_775_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0);
v___x_776_ = l_Lean_Meta_FindSplitImpl_visit(v_e_768_, v___x_774_, v___x_775_, v_a_769_, v_a_770_, v_a_771_, v_a_772_);
lean_dec_ref_known(v___x_774_, 1);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_785_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_785_ == 0)
{
v___x_779_ = v___x_776_;
v_isShared_780_ = v_isSharedCheck_785_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_776_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_785_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v_fst_781_; lean_object* v___x_783_; 
v_fst_781_ = lean_ctor_get(v_a_777_, 0);
lean_inc(v_fst_781_);
lean_dec(v_a_777_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v_fst_781_);
v___x_783_ = v___x_779_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_fst_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
v_a_786_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_776_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_776_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___boxed(lean_object* v_kind_794_, lean_object* v_exceptionSet_795_, lean_object* v_e_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
uint8_t v_kind_boxed_802_; lean_object* v_res_803_; 
v_kind_boxed_802_ = lean_unbox(v_kind_794_);
v_res_803_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1(v_kind_boxed_802_, v_exceptionSet_795_, v_e_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(lean_object* v_msgData_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v___x_810_; lean_object* v_env_811_; lean_object* v___x_812_; lean_object* v_toCold_813_; lean_object* v_mctx_814_; lean_object* v_lctx_815_; lean_object* v_options_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_810_ = lean_st_ref_get(v___y_808_);
v_env_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc_ref(v_env_811_);
lean_dec(v___x_810_);
v___x_812_ = lean_st_ref_get(v___y_806_);
v_toCold_813_ = lean_ctor_get(v___y_807_, 0);
v_mctx_814_ = lean_ctor_get(v___x_812_, 0);
lean_inc_ref(v_mctx_814_);
lean_dec(v___x_812_);
v_lctx_815_ = lean_ctor_get(v___y_805_, 2);
v_options_816_ = lean_ctor_get(v_toCold_813_, 2);
lean_inc_ref(v_options_816_);
lean_inc_ref(v_lctx_815_);
v___x_817_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_817_, 0, v_env_811_);
lean_ctor_set(v___x_817_, 1, v_mctx_814_);
lean_ctor_set(v___x_817_, 2, v_lctx_815_);
lean_ctor_set(v___x_817_, 3, v_options_816_);
v___x_818_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
lean_ctor_set(v___x_818_, 1, v_msgData_804_);
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0___boxed(lean_object* v_msgData_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(v_msgData_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
return v_res_826_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_827_; double v___x_828_; 
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = lean_float_of_nat(v___x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(lean_object* v_cls_832_, lean_object* v_msg_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_ref_839_; lean_object* v___x_840_; lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_885_; 
v_ref_839_ = lean_ctor_get(v___y_836_, 2);
v___x_840_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(v_msg_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
v_a_841_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_885_ == 0)
{
v___x_843_ = v___x_840_;
v_isShared_844_ = v_isSharedCheck_885_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_840_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_885_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; lean_object* v_traceState_846_; lean_object* v_env_847_; lean_object* v_nextMacroScope_848_; lean_object* v_ngen_849_; lean_object* v_auxDeclNGen_850_; lean_object* v_cache_851_; lean_object* v_messages_852_; lean_object* v_infoState_853_; lean_object* v_snapshotTasks_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_884_; 
v___x_845_ = lean_st_ref_take(v___y_837_);
v_traceState_846_ = lean_ctor_get(v___x_845_, 4);
v_env_847_ = lean_ctor_get(v___x_845_, 0);
v_nextMacroScope_848_ = lean_ctor_get(v___x_845_, 1);
v_ngen_849_ = lean_ctor_get(v___x_845_, 2);
v_auxDeclNGen_850_ = lean_ctor_get(v___x_845_, 3);
v_cache_851_ = lean_ctor_get(v___x_845_, 5);
v_messages_852_ = lean_ctor_get(v___x_845_, 6);
v_infoState_853_ = lean_ctor_get(v___x_845_, 7);
v_snapshotTasks_854_ = lean_ctor_get(v___x_845_, 8);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_884_ == 0)
{
v___x_856_ = v___x_845_;
v_isShared_857_ = v_isSharedCheck_884_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_snapshotTasks_854_);
lean_inc(v_infoState_853_);
lean_inc(v_messages_852_);
lean_inc(v_cache_851_);
lean_inc(v_traceState_846_);
lean_inc(v_auxDeclNGen_850_);
lean_inc(v_ngen_849_);
lean_inc(v_nextMacroScope_848_);
lean_inc(v_env_847_);
lean_dec(v___x_845_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_884_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
uint64_t v_tid_858_; lean_object* v_traces_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_883_; 
v_tid_858_ = lean_ctor_get_uint64(v_traceState_846_, sizeof(void*)*1);
v_traces_859_ = lean_ctor_get(v_traceState_846_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v_traceState_846_);
if (v_isSharedCheck_883_ == 0)
{
v___x_861_ = v_traceState_846_;
v_isShared_862_ = v_isSharedCheck_883_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_traces_859_);
lean_dec(v_traceState_846_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_883_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_863_; double v___x_864_; uint8_t v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_863_ = lean_box(0);
v___x_864_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0);
v___x_865_ = 0;
v___x_866_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__1));
v___x_867_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_867_, 0, v_cls_832_);
lean_ctor_set(v___x_867_, 1, v___x_863_);
lean_ctor_set(v___x_867_, 2, v___x_866_);
lean_ctor_set_float(v___x_867_, sizeof(void*)*3, v___x_864_);
lean_ctor_set_float(v___x_867_, sizeof(void*)*3 + 8, v___x_864_);
lean_ctor_set_uint8(v___x_867_, sizeof(void*)*3 + 16, v___x_865_);
v___x_868_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__2));
v___x_869_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_869_, 0, v___x_867_);
lean_ctor_set(v___x_869_, 1, v_a_841_);
lean_ctor_set(v___x_869_, 2, v___x_868_);
lean_inc(v_ref_839_);
v___x_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_870_, 0, v_ref_839_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = l_Lean_PersistentArray_push___redArg(v_traces_859_, v___x_870_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_871_);
v___x_873_ = v___x_861_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_871_);
lean_ctor_set_uint64(v_reuseFailAlloc_882_, sizeof(void*)*1, v_tid_858_);
v___x_873_ = v_reuseFailAlloc_882_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_875_; 
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 4, v___x_873_);
v___x_875_ = v___x_856_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_env_847_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_nextMacroScope_848_);
lean_ctor_set(v_reuseFailAlloc_881_, 2, v_ngen_849_);
lean_ctor_set(v_reuseFailAlloc_881_, 3, v_auxDeclNGen_850_);
lean_ctor_set(v_reuseFailAlloc_881_, 4, v___x_873_);
lean_ctor_set(v_reuseFailAlloc_881_, 5, v_cache_851_);
lean_ctor_set(v_reuseFailAlloc_881_, 6, v_messages_852_);
lean_ctor_set(v_reuseFailAlloc_881_, 7, v_infoState_853_);
lean_ctor_set(v_reuseFailAlloc_881_, 8, v_snapshotTasks_854_);
v___x_875_ = v_reuseFailAlloc_881_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_879_; 
v___x_876_ = lean_st_ref_put(v___y_837_, v___x_875_);
v___x_877_ = lean_box(0);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v___x_877_);
v___x_879_ = v___x_843_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___boxed(lean_object* v_cls_886_, lean_object* v_msg_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v_cls_886_, v_msg_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
return v_res_893_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_902_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__2));
v___x_903_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4));
v___x_904_ = l_Lean_Name_append(v___x_903_, v___x_902_);
return v___x_904_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__6));
v___x_907_ = l_Lean_stringToMessageData(v___x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f(uint8_t v_kind_908_, lean_object* v_exceptionSet_909_, lean_object* v_e_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_916_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_916_, 0, v_exceptionSet_909_);
lean_ctor_set_uint8(v___x_916_, sizeof(void*)*1, v_kind_908_);
v___x_917_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0);
v___x_918_ = l_Lean_Meta_FindSplitImpl_visit(v_e_910_, v___x_916_, v___x_917_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
lean_dec_ref_known(v___x_916_, 1);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_966_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_966_ == 0)
{
v___x_921_ = v___x_918_;
v_isShared_922_ = v_isSharedCheck_966_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_918_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_966_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v_fst_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_964_; 
v_fst_923_ = lean_ctor_get(v_a_919_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v_a_919_);
if (v_isSharedCheck_964_ == 0)
{
lean_object* v_unused_965_; 
v_unused_965_ = lean_ctor_get(v_a_919_, 1);
lean_dec(v_unused_965_);
v___x_925_ = v_a_919_;
v_isShared_926_ = v_isSharedCheck_964_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_fst_923_);
lean_dec(v_a_919_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_964_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
if (lean_obj_tag(v_fst_923_) == 1)
{
lean_object* v_toCold_927_; lean_object* v_options_928_; lean_object* v_val_929_; lean_object* v_inheritedTraceOptions_930_; uint8_t v_hasTrace_931_; lean_object* v___x_933_; 
v_toCold_927_ = lean_ctor_get(v_a_913_, 0);
v_options_928_ = lean_ctor_get(v_toCold_927_, 2);
v_val_929_ = lean_ctor_get(v_fst_923_, 0);
v_inheritedTraceOptions_930_ = lean_ctor_get(v_toCold_927_, 11);
v_hasTrace_931_ = lean_ctor_get_uint8(v_options_928_, sizeof(void*)*1);
lean_inc_ref(v_fst_923_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v_fst_923_);
v___x_933_ = v___x_921_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_fst_923_);
v___x_933_ = v_reuseFailAlloc_959_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
if (v_hasTrace_931_ == 0)
{
lean_dec_ref_known(v_fst_923_, 1);
lean_del_object(v___x_925_);
return v___x_933_;
}
else
{
lean_object* v___x_934_; lean_object* v___x_935_; uint8_t v___x_936_; 
v___x_934_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__2));
v___x_935_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5);
v___x_936_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_930_, v_options_928_, v___x_935_);
if (v___x_936_ == 0)
{
lean_dec_ref_known(v_fst_923_, 1);
lean_del_object(v___x_925_);
return v___x_933_;
}
else
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_940_; 
lean_dec_ref(v___x_933_);
v___x_937_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7);
lean_inc(v_val_929_);
v___x_938_ = l_Lean_indentExpr(v_val_929_);
if (v_isShared_926_ == 0)
{
lean_ctor_set_tag(v___x_925_, 7);
lean_ctor_set(v___x_925_, 1, v___x_938_);
lean_ctor_set(v___x_925_, 0, v___x_937_);
v___x_940_ = v___x_925_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v___x_938_);
v___x_940_ = v_reuseFailAlloc_958_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_941_; 
v___x_941_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_934_, v___x_940_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; 
v_unused_949_ = lean_ctor_get(v___x_941_, 0);
lean_dec(v_unused_949_);
v___x_943_ = v___x_941_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_dec(v___x_941_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v_fst_923_);
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_fst_923_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec_ref_known(v_fst_923_, 1);
v_a_950_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_941_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_941_);
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
}
}
}
}
else
{
lean_object* v___x_960_; lean_object* v___x_962_; 
lean_del_object(v___x_925_);
lean_dec(v_fst_923_);
v___x_960_ = lean_box(0);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_960_);
v___x_962_ = v___x_921_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_960_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
v_a_967_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_918_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_918_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___boxed(lean_object* v_kind_975_, lean_object* v_exceptionSet_976_, lean_object* v_e_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
uint8_t v_kind_boxed_983_; lean_object* v_res_984_; 
v_kind_boxed_983_ = lean_unbox(v_kind_975_);
v_res_984_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f(v_kind_boxed_983_, v_exceptionSet_976_, v_e_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
lean_dec(v_a_981_);
lean_dec_ref(v_a_980_);
lean_dec(v_a_979_);
lean_dec_ref(v_a_978_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(uint8_t v_kind_985_, lean_object* v_exceptionSet_986_, lean_object* v_e_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
lean_object* v___y_994_; lean_object* v___x_997_; 
lean_inc_ref(v_exceptionSet_986_);
v___x_997_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f(v_kind_985_, v_exceptionSet_986_, v_e_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_998_);
if (lean_obj_tag(v_a_998_) == 1)
{
lean_object* v_val_999_; uint8_t v___y_1001_; uint8_t v___x_1007_; 
v_val_999_ = lean_ctor_get(v_a_998_, 0);
lean_inc(v_val_999_);
lean_dec_ref_known(v_a_998_, 1);
v___x_1007_ = l_Lean_Expr_isIte(v_val_999_);
if (v___x_1007_ == 0)
{
uint8_t v___x_1008_; 
v___x_1008_ = l_Lean_Expr_isDIte(v_val_999_);
v___y_1001_ = v___x_1008_;
goto v___jp_1000_;
}
else
{
v___y_1001_ = v___x_1007_;
goto v___jp_1000_;
}
v___jp_1000_:
{
if (v___y_1001_ == 0)
{
lean_dec(v_val_999_);
lean_dec_ref(v_exceptionSet_986_);
return v___x_997_;
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
lean_dec_ref_known(v___x_997_, 1);
v___x_1002_ = lean_unsigned_to_nat(3u);
v___x_1003_ = l_Lean_Expr_getRevArg_x21(v_val_999_, v___x_1002_);
v___x_1004_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(v_kind_985_, v_exceptionSet_986_, v___x_1003_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1005_);
lean_dec_ref_known(v___x_1004_, 1);
if (lean_obj_tag(v_a_1005_) == 0)
{
v___y_994_ = v_val_999_;
goto v___jp_993_;
}
else
{
lean_object* v_val_1006_; 
lean_dec(v_val_999_);
v_val_1006_ = lean_ctor_get(v_a_1005_, 0);
lean_inc(v_val_1006_);
lean_dec_ref_known(v_a_1005_, 1);
v___y_994_ = v_val_1006_;
goto v___jp_993_;
}
}
else
{
lean_dec(v_val_999_);
return v___x_1004_;
}
}
}
}
else
{
lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1016_; 
lean_dec(v_a_998_);
lean_dec_ref(v_exceptionSet_986_);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1016_ == 0)
{
lean_object* v_unused_1017_; 
v_unused_1017_ = lean_ctor_get(v___x_997_, 0);
lean_dec(v_unused_1017_);
v___x_1010_ = v___x_997_;
v_isShared_1011_ = v_isSharedCheck_1016_;
goto v_resetjp_1009_;
}
else
{
lean_dec(v___x_997_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1016_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1012_; lean_object* v___x_1014_; 
v___x_1012_ = lean_box(0);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v___x_1012_);
v___x_1014_ = v___x_1010_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1012_);
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
else
{
lean_dec_ref(v_exceptionSet_986_);
return v___x_997_;
}
v___jp_993_:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_995_, 0, v___y_994_);
v___x_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
return v___x_996_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go___boxed(lean_object* v_kind_1018_, lean_object* v_exceptionSet_1019_, lean_object* v_e_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_){
_start:
{
uint8_t v_kind_boxed_1026_; lean_object* v_res_1027_; 
v_kind_boxed_1026_ = lean_unbox(v_kind_1018_);
v_res_1027_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(v_kind_boxed_1026_, v_exceptionSet_1019_, v_e_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(lean_object* v_e_1028_, lean_object* v___y_1029_){
_start:
{
uint8_t v___x_1031_; 
v___x_1031_ = l_Lean_Expr_hasMVar(v_e_1028_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; 
v___x_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1032_, 0, v_e_1028_);
return v___x_1032_;
}
else
{
lean_object* v___x_1033_; lean_object* v_mctx_1034_; lean_object* v___x_1035_; lean_object* v_fst_1036_; lean_object* v_snd_1037_; lean_object* v___x_1038_; lean_object* v_cache_1039_; lean_object* v_zetaDeltaFVarIds_1040_; lean_object* v_postponed_1041_; lean_object* v_diag_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1051_; 
v___x_1033_ = lean_st_ref_get(v___y_1029_);
v_mctx_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc_ref(v_mctx_1034_);
lean_dec(v___x_1033_);
v___x_1035_ = l_Lean_instantiateMVarsCore(v_mctx_1034_, v_e_1028_);
v_fst_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_fst_1036_);
v_snd_1037_ = lean_ctor_get(v___x_1035_, 1);
lean_inc(v_snd_1037_);
lean_dec_ref(v___x_1035_);
v___x_1038_ = lean_st_ref_take(v___y_1029_);
v_cache_1039_ = lean_ctor_get(v___x_1038_, 1);
v_zetaDeltaFVarIds_1040_ = lean_ctor_get(v___x_1038_, 2);
v_postponed_1041_ = lean_ctor_get(v___x_1038_, 3);
v_diag_1042_ = lean_ctor_get(v___x_1038_, 4);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1051_ == 0)
{
lean_object* v_unused_1052_; 
v_unused_1052_ = lean_ctor_get(v___x_1038_, 0);
lean_dec(v_unused_1052_);
v___x_1044_ = v___x_1038_;
v_isShared_1045_ = v_isSharedCheck_1051_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_diag_1042_);
lean_inc(v_postponed_1041_);
lean_inc(v_zetaDeltaFVarIds_1040_);
lean_inc(v_cache_1039_);
lean_dec(v___x_1038_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1051_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v_snd_1037_);
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_snd_1037_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_cache_1039_);
lean_ctor_set(v_reuseFailAlloc_1050_, 2, v_zetaDeltaFVarIds_1040_);
lean_ctor_set(v_reuseFailAlloc_1050_, 3, v_postponed_1041_);
lean_ctor_set(v_reuseFailAlloc_1050_, 4, v_diag_1042_);
v___x_1047_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_st_ref_put(v___y_1029_, v___x_1047_);
v___x_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1049_, 0, v_fst_1036_);
return v___x_1049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg___boxed(lean_object* v_e_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_1053_, v___y_1054_);
lean_dec(v___y_1054_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0(lean_object* v_e_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_1057_, v___y_1059_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___boxed(lean_object* v_e_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0(v_e_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f(lean_object* v_e_1071_, uint8_t v_kind_1072_, lean_object* v_exceptionSet_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_){
_start:
{
lean_object* v___x_1079_; lean_object* v_a_1080_; lean_object* v___x_1081_; 
v___x_1079_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_1071_, v_a_1075_);
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref(v___x_1079_);
v___x_1081_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(v_kind_1072_, v_exceptionSet_1073_, v_a_1080_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f___boxed(lean_object* v_e_1082_, lean_object* v_kind_1083_, lean_object* v_exceptionSet_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_){
_start:
{
uint8_t v_kind_boxed_1090_; lean_object* v_res_1091_; 
v_kind_boxed_1090_ = lean_unbox(v_kind_1083_);
v_res_1091_ = l_Lean_Meta_findSplit_x3f(v_e_1082_, v_kind_boxed_1090_, v_exceptionSet_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
lean_dec(v_a_1088_);
lean_dec_ref(v_a_1087_);
lean_dec(v_a_1086_);
lean_dec_ref(v_a_1085_);
return v_res_1091_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0(void){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1092_ = lean_box(0);
v___x_1093_ = lean_unsigned_to_nat(16u);
v___x_1094_ = lean_mk_array(v___x_1093_, v___x_1092_);
return v___x_1094_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1(void){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1095_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0);
v___x_1096_ = lean_unsigned_to_nat(0u);
v___x_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
lean_ctor_set(v___x_1097_, 1, v___x_1095_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(lean_object* v_e_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
uint8_t v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1104_ = 0;
v___x_1105_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1);
v___x_1106_ = l_Lean_Meta_findSplit_x3f(v_e_1098_, v___x_1104_, v___x_1105_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1131_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1109_ = v___x_1106_;
v_isShared_1110_ = v_isSharedCheck_1131_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1106_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1131_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
if (lean_obj_tag(v_a_1107_) == 1)
{
lean_object* v_val_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1126_; 
v_val_1111_ = lean_ctor_get(v_a_1107_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_a_1107_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1113_ = v_a_1107_;
v_isShared_1114_ = v_isSharedCheck_1126_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_val_1111_);
lean_dec(v_a_1107_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1126_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1121_; 
v___x_1115_ = lean_unsigned_to_nat(3u);
v___x_1116_ = l_Lean_Expr_getRevArg_x21(v_val_1111_, v___x_1115_);
v___x_1117_ = lean_unsigned_to_nat(2u);
v___x_1118_ = l_Lean_Expr_getRevArg_x21(v_val_1111_, v___x_1117_);
lean_dec(v_val_1111_);
v___x_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1116_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v___x_1119_);
v___x_1121_ = v___x_1113_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1123_; 
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1121_);
v___x_1123_ = v___x_1109_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1121_);
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
else
{
lean_object* v___x_1127_; lean_object* v___x_1129_; 
lean_dec(v_a_1107_);
v___x_1127_ = lean_box(0);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1127_);
v___x_1129_ = v___x_1109_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1127_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
v_a_1132_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1106_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1106_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___boxed(lean_object* v_e_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(v_e_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(lean_object* v_name_1147_, lean_object* v_decl_1148_, lean_object* v_ref_1149_){
_start:
{
lean_object* v_defValue_1151_; lean_object* v_descr_1152_; lean_object* v_deprecation_x3f_1153_; lean_object* v___x_1154_; uint8_t v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v_defValue_1151_ = lean_ctor_get(v_decl_1148_, 0);
v_descr_1152_ = lean_ctor_get(v_decl_1148_, 1);
v_deprecation_x3f_1153_ = lean_ctor_get(v_decl_1148_, 2);
v___x_1154_ = lean_alloc_ctor(1, 0, 1);
v___x_1155_ = lean_unbox(v_defValue_1151_);
lean_ctor_set_uint8(v___x_1154_, 0, v___x_1155_);
lean_inc(v_deprecation_x3f_1153_);
lean_inc_ref(v_descr_1152_);
lean_inc_n(v_name_1147_, 2);
v___x_1156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1156_, 0, v_name_1147_);
lean_ctor_set(v___x_1156_, 1, v_ref_1149_);
lean_ctor_set(v___x_1156_, 2, v___x_1154_);
lean_ctor_set(v___x_1156_, 3, v_descr_1152_);
lean_ctor_set(v___x_1156_, 4, v_deprecation_x3f_1153_);
v___x_1157_ = lean_register_option(v_name_1147_, v___x_1156_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1165_; 
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1165_ == 0)
{
lean_object* v_unused_1166_; 
v_unused_1166_ = lean_ctor_get(v___x_1157_, 0);
lean_dec(v_unused_1166_);
v___x_1159_ = v___x_1157_;
v_isShared_1160_ = v_isSharedCheck_1165_;
goto v_resetjp_1158_;
}
else
{
lean_dec(v___x_1157_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1165_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v___x_1163_; 
lean_inc(v_defValue_1151_);
v___x_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1161_, 0, v_name_1147_);
lean_ctor_set(v___x_1161_, 1, v_defValue_1151_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1161_);
v___x_1163_ = v___x_1159_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1161_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
lean_dec(v_name_1147_);
v_a_1167_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1157_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1157_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1175_, lean_object* v_decl_1176_, lean_object* v_ref_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(v_name_1175_, v_decl_1176_, v_ref_1177_);
lean_dec_ref(v_decl_1176_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1198_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_));
v___x_1199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_));
v___x_1200_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_));
v___x_1201_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(v___x_1198_, v___x_1199_, v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4____boxed(lean_object* v_a_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_();
return v_res_1203_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1204_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0);
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0(lean_object* v_00_u03b2_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1);
return v___x_1208_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1209_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1(lean_object* v_00_u03b2_1212_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1);
return v___x_1213_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__0(void){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_1214_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__1(void){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0(lean_box(0));
return v___x_1215_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__2(void){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1(lean_box(0));
return v___x_1216_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__3(void){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1217_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__4(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__3, &l_Lean_Meta_SplitIf_getSimpContext___closed__3_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__3);
v___x_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
return v___x_1219_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__5(void){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v_s_1224_; 
v___x_1220_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__4, &l_Lean_Meta_SplitIf_getSimpContext___closed__4_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__4);
v___x_1221_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__2, &l_Lean_Meta_SplitIf_getSimpContext___closed__2_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__2);
v___x_1222_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__1, &l_Lean_Meta_SplitIf_getSimpContext___closed__1_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__1);
v___x_1223_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__0, &l_Lean_Meta_SplitIf_getSimpContext___closed__0_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__0);
v_s_1224_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_s_1224_, 0, v___x_1223_);
lean_ctor_set(v_s_1224_, 1, v___x_1223_);
lean_ctor_set(v_s_1224_, 2, v___x_1222_);
lean_ctor_set(v_s_1224_, 3, v___x_1221_);
lean_ctor_set(v_s_1224_, 4, v___x_1222_);
lean_ctor_set(v_s_1224_, 5, v___x_1220_);
return v_s_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_getSimpContext(lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v_s_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; uint8_t v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v_s_1242_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__5, &l_Lean_Meta_SplitIf_getSimpContext___closed__5_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__5);
v___x_1243_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__7));
v___x_1244_ = 1;
v___x_1245_ = 0;
v___x_1246_ = lean_unsigned_to_nat(1000u);
v___x_1247_ = l_Lean_Meta_SimpTheorems_addConst(v_s_1242_, v___x_1243_, v___x_1244_, v___x_1245_, v___x_1246_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_a_1248_);
lean_dec_ref_known(v___x_1247_, 1);
v___x_1249_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__9));
v___x_1250_ = l_Lean_Meta_SimpTheorems_addConst(v_a_1248_, v___x_1249_, v___x_1244_, v___x_1245_, v___x_1246_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_a_1251_);
lean_dec_ref_known(v___x_1250_, 1);
v___x_1252_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__11));
v___x_1253_ = l_Lean_Meta_SimpTheorems_addConst(v_a_1251_, v___x_1252_, v___x_1244_, v___x_1245_, v___x_1246_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1254_);
lean_dec_ref_known(v___x_1253_, 1);
v___x_1255_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__13));
v___x_1256_ = l_Lean_Meta_SimpTheorems_addConst(v_a_1254_, v___x_1255_, v___x_1244_, v___x_1245_, v___x_1246_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1258_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_a_1257_);
lean_dec_ref_known(v___x_1256_, 1);
v___x_1258_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_1240_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; lean_object* v___x_1260_; lean_object* v_maxSteps_1261_; lean_object* v_maxDischargeDepth_1262_; uint8_t v_contextual_1263_; uint8_t v_memoize_1264_; uint8_t v_singlePass_1265_; uint8_t v_zeta_1266_; uint8_t v_beta_1267_; uint8_t v_eta_1268_; uint8_t v_etaStruct_1269_; uint8_t v_iota_1270_; uint8_t v_proj_1271_; uint8_t v_decide_1272_; uint8_t v_arith_1273_; uint8_t v_autoUnfold_1274_; uint8_t v_failIfUnchanged_1275_; uint8_t v_ground_1276_; uint8_t v_unfoldPartialApp_1277_; uint8_t v_zetaDelta_1278_; uint8_t v_index_1279_; uint8_t v_implicitDefEqProofs_1280_; uint8_t v_zetaUnused_1281_; uint8_t v_catchRuntime_1282_; uint8_t v_zetaHave_1283_; uint8_t v_congrConsts_1284_; uint8_t v_bitVecOfNat_1285_; uint8_t v_warnExponents_1286_; uint8_t v_suggestions_1287_; lean_object* v_maxSuggestions_1288_; uint8_t v_locals_1289_; uint8_t v_instances_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1259_);
lean_dec_ref_known(v___x_1258_, 1);
v___x_1260_ = l_Lean_Meta_Simp_neutralConfig;
v_maxSteps_1261_ = lean_ctor_get(v___x_1260_, 0);
v_maxDischargeDepth_1262_ = lean_ctor_get(v___x_1260_, 1);
v_contextual_1263_ = lean_ctor_get_uint8(v___x_1260_, sizeof(void*)*3);
v_memoize_1264_ = lean_ctor_get_uint8(v___x_1260_, sizeof(void*)*3 + 1);
v_singlePass_1265_ = lean_ctor_get_uint8(v___x_1260_, sizeof(void*)*3 + 2);
v_zeta_1266_ = lean_ctor_get_uint8(v___x_1260_, sizeof(void*)*3 + 3);
v_beta_1267_ = lean_ctor_get_uint8(v___x_1260_, sizeof(void*)*3 + 4);
v_eta_1268_ = lean_ctor_get_uint8(v___x_1260_, sizeof(void*)*3 + 5);
v_etaStruct_1269_ = lean_ctor_get_uint8(v___x_1260_, sizeof(void*)*3 + 6);
v_iota_1270_ = lean_ctor_get_uint8(v___x_1260_, sizeof(void*)*3 + 7);
v_proj_1271_ = lean_ctor_get_uint8(v___x_1260_, sizeof(void*)*3 + 8);
v_decide_1272_ = lean_ctor_get_uint8(v___x_1260_, sizeof(void*)*3 + 9);
v_arith_1273_ = lean_ctor_get_uint8(v___x_1260_, sizeof(void*)*3 + 10);
v_autoUnfold_1274_ = lean_ctor_get_uint8(v___x_1260_, sizeof(void*)*3 + 11);
v_failIfUnchanged_1275_ = lean_ctor_get_uint8(v___x_1260_, sizeof(void*)*3 + 13);
v_ground_1276_ = lean_ctor_get_uint8(v___x_1260_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_1277_ = lean_ctor_get_uint8(v___x_1260_, sizeof(void*)*3 + 15);
v_zetaDelta_1278_ = lean_ctor_get_uint8(v___x_1260_, sizeof(void*)*3 + 16);
v_index_1279_ = lean_ctor_get_uint8(v___x_1260_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_1280_ = lean_ctor_get_uint8(v___x_1260_, sizeof(void*)*3 + 18);
v_zetaUnused_1281_ = lean_ctor_get_uint8(v___x_1260_, sizeof(void*)*3 + 19);
v_catchRuntime_1282_ = lean_ctor_get_uint8(v___x_1260_, sizeof(void*)*3 + 20);
v_zetaHave_1283_ = lean_ctor_get_uint8(v___x_1260_, sizeof(void*)*3 + 21);
v_congrConsts_1284_ = lean_ctor_get_uint8(v___x_1260_, sizeof(void*)*3 + 23);
v_bitVecOfNat_1285_ = lean_ctor_get_uint8(v___x_1260_, sizeof(void*)*3 + 24);
v_warnExponents_1286_ = lean_ctor_get_uint8(v___x_1260_, sizeof(void*)*3 + 25);
v_suggestions_1287_ = lean_ctor_get_uint8(v___x_1260_, sizeof(void*)*3 + 26);
v_maxSuggestions_1288_ = lean_ctor_get(v___x_1260_, 2);
v_locals_1289_ = lean_ctor_get_uint8(v___x_1260_, sizeof(void*)*3 + 27);
v_instances_1290_ = lean_ctor_get_uint8(v___x_1260_, sizeof(void*)*3 + 28);
lean_inc(v_maxSuggestions_1288_);
lean_inc(v_maxDischargeDepth_1262_);
lean_inc(v_maxSteps_1261_);
v___x_1291_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1291_, 0, v_maxSteps_1261_);
lean_ctor_set(v___x_1291_, 1, v_maxDischargeDepth_1262_);
lean_ctor_set(v___x_1291_, 2, v_maxSuggestions_1288_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3, v_contextual_1263_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3 + 1, v_memoize_1264_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3 + 2, v_singlePass_1265_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3 + 3, v_zeta_1266_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3 + 4, v_beta_1267_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3 + 5, v_eta_1268_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3 + 6, v_etaStruct_1269_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3 + 7, v_iota_1270_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3 + 8, v_proj_1271_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3 + 9, v_decide_1272_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3 + 10, v_arith_1273_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3 + 11, v_autoUnfold_1274_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3 + 12, v___x_1245_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3 + 13, v_failIfUnchanged_1275_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3 + 14, v_ground_1276_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3 + 15, v_unfoldPartialApp_1277_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3 + 16, v_zetaDelta_1278_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3 + 17, v_index_1279_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_1280_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3 + 19, v_zetaUnused_1281_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3 + 20, v_catchRuntime_1282_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3 + 21, v_zetaHave_1283_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3 + 22, v___x_1244_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3 + 23, v_congrConsts_1284_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3 + 24, v_bitVecOfNat_1285_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3 + 25, v_warnExponents_1286_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3 + 26, v_suggestions_1287_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3 + 27, v_locals_1289_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3 + 28, v_instances_1290_);
v___x_1292_ = lean_unsigned_to_nat(1u);
v___x_1293_ = lean_mk_empty_array_with_capacity(v___x_1292_);
v___x_1294_ = lean_array_push(v___x_1293_, v_a_1257_);
v___x_1295_ = l_Lean_Options_empty;
v___x_1296_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1291_, v___x_1294_, v_a_1259_, v___x_1295_, v_a_1237_, v_a_1239_, v_a_1240_);
return v___x_1296_;
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_dec(v_a_1257_);
v_a_1297_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1258_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1258_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
v_a_1305_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1256_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1256_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
v_a_1313_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1253_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1253_);
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
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
v_a_1321_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1250_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1250_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
v_a_1329_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1247_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1247_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_getSimpContext___boxed(lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
lean_dec(v_a_1340_);
lean_dec_ref(v_a_1339_);
lean_dec(v_a_1338_);
lean_dec_ref(v_a_1337_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_1347_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1351_; lean_object* v_maxSteps_1352_; lean_object* v_maxDischargeDepth_1353_; uint8_t v_contextual_1354_; uint8_t v_memoize_1355_; uint8_t v_singlePass_1356_; uint8_t v_zeta_1357_; uint8_t v_beta_1358_; uint8_t v_eta_1359_; uint8_t v_etaStruct_1360_; uint8_t v_iota_1361_; uint8_t v_proj_1362_; uint8_t v_decide_1363_; uint8_t v_arith_1364_; uint8_t v_autoUnfold_1365_; uint8_t v_failIfUnchanged_1366_; uint8_t v_ground_1367_; uint8_t v_unfoldPartialApp_1368_; uint8_t v_zetaDelta_1369_; uint8_t v_index_1370_; uint8_t v_implicitDefEqProofs_1371_; uint8_t v_zetaUnused_1372_; uint8_t v_catchRuntime_1373_; uint8_t v_zetaHave_1374_; uint8_t v_congrConsts_1375_; uint8_t v_bitVecOfNat_1376_; uint8_t v_warnExponents_1377_; uint8_t v_suggestions_1378_; lean_object* v_maxSuggestions_1379_; uint8_t v_locals_1380_; uint8_t v_instances_1381_; uint8_t v___x_1382_; uint8_t v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1349_, 1);
v___x_1351_ = l_Lean_Meta_Simp_neutralConfig;
v_maxSteps_1352_ = lean_ctor_get(v___x_1351_, 0);
v_maxDischargeDepth_1353_ = lean_ctor_get(v___x_1351_, 1);
v_contextual_1354_ = lean_ctor_get_uint8(v___x_1351_, sizeof(void*)*3);
v_memoize_1355_ = lean_ctor_get_uint8(v___x_1351_, sizeof(void*)*3 + 1);
v_singlePass_1356_ = lean_ctor_get_uint8(v___x_1351_, sizeof(void*)*3 + 2);
v_zeta_1357_ = lean_ctor_get_uint8(v___x_1351_, sizeof(void*)*3 + 3);
v_beta_1358_ = lean_ctor_get_uint8(v___x_1351_, sizeof(void*)*3 + 4);
v_eta_1359_ = lean_ctor_get_uint8(v___x_1351_, sizeof(void*)*3 + 5);
v_etaStruct_1360_ = lean_ctor_get_uint8(v___x_1351_, sizeof(void*)*3 + 6);
v_iota_1361_ = lean_ctor_get_uint8(v___x_1351_, sizeof(void*)*3 + 7);
v_proj_1362_ = lean_ctor_get_uint8(v___x_1351_, sizeof(void*)*3 + 8);
v_decide_1363_ = lean_ctor_get_uint8(v___x_1351_, sizeof(void*)*3 + 9);
v_arith_1364_ = lean_ctor_get_uint8(v___x_1351_, sizeof(void*)*3 + 10);
v_autoUnfold_1365_ = lean_ctor_get_uint8(v___x_1351_, sizeof(void*)*3 + 11);
v_failIfUnchanged_1366_ = lean_ctor_get_uint8(v___x_1351_, sizeof(void*)*3 + 13);
v_ground_1367_ = lean_ctor_get_uint8(v___x_1351_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_1368_ = lean_ctor_get_uint8(v___x_1351_, sizeof(void*)*3 + 15);
v_zetaDelta_1369_ = lean_ctor_get_uint8(v___x_1351_, sizeof(void*)*3 + 16);
v_index_1370_ = lean_ctor_get_uint8(v___x_1351_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_1371_ = lean_ctor_get_uint8(v___x_1351_, sizeof(void*)*3 + 18);
v_zetaUnused_1372_ = lean_ctor_get_uint8(v___x_1351_, sizeof(void*)*3 + 19);
v_catchRuntime_1373_ = lean_ctor_get_uint8(v___x_1351_, sizeof(void*)*3 + 20);
v_zetaHave_1374_ = lean_ctor_get_uint8(v___x_1351_, sizeof(void*)*3 + 21);
v_congrConsts_1375_ = lean_ctor_get_uint8(v___x_1351_, sizeof(void*)*3 + 23);
v_bitVecOfNat_1376_ = lean_ctor_get_uint8(v___x_1351_, sizeof(void*)*3 + 24);
v_warnExponents_1377_ = lean_ctor_get_uint8(v___x_1351_, sizeof(void*)*3 + 25);
v_suggestions_1378_ = lean_ctor_get_uint8(v___x_1351_, sizeof(void*)*3 + 26);
v_maxSuggestions_1379_ = lean_ctor_get(v___x_1351_, 2);
v_locals_1380_ = lean_ctor_get_uint8(v___x_1351_, sizeof(void*)*3 + 27);
v_instances_1381_ = lean_ctor_get_uint8(v___x_1351_, sizeof(void*)*3 + 28);
v___x_1382_ = 0;
v___x_1383_ = 1;
lean_inc(v_maxSuggestions_1379_);
lean_inc(v_maxDischargeDepth_1353_);
lean_inc(v_maxSteps_1352_);
v___x_1384_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1384_, 0, v_maxSteps_1352_);
lean_ctor_set(v___x_1384_, 1, v_maxDischargeDepth_1353_);
lean_ctor_set(v___x_1384_, 2, v_maxSuggestions_1379_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3, v_contextual_1354_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3 + 1, v_memoize_1355_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3 + 2, v_singlePass_1356_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3 + 3, v_zeta_1357_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3 + 4, v_beta_1358_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3 + 5, v_eta_1359_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3 + 6, v_etaStruct_1360_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3 + 7, v_iota_1361_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3 + 8, v_proj_1362_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3 + 9, v_decide_1363_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3 + 10, v_arith_1364_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3 + 11, v_autoUnfold_1365_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3 + 12, v___x_1382_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3 + 13, v_failIfUnchanged_1366_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3 + 14, v_ground_1367_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3 + 15, v_unfoldPartialApp_1368_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3 + 16, v_zetaDelta_1369_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3 + 17, v_index_1370_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_1371_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3 + 19, v_zetaUnused_1372_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3 + 20, v_catchRuntime_1373_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3 + 21, v_zetaHave_1374_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3 + 22, v___x_1383_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3 + 23, v_congrConsts_1375_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3 + 24, v_bitVecOfNat_1376_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3 + 25, v_warnExponents_1377_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3 + 26, v_suggestions_1378_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3 + 27, v_locals_1380_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*3 + 28, v_instances_1381_);
v___x_1385_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg___closed__0));
v___x_1386_ = l_Lean_Options_empty;
v___x_1387_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1384_, v___x_1385_, v_a_1350_, v___x_1386_, v_a_1345_, v_a_1346_, v_a_1347_);
return v___x_1387_;
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
v_a_1388_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1349_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1349_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg___boxed(lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_1396_, v_a_1397_, v_a_1398_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
lean_dec_ref(v_a_1396_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27(lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_1401_, v_a_1403_, v_a_1404_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___boxed(lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27(v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_);
lean_dec(v_a_1410_);
lean_dec_ref(v_a_1409_);
lean_dec(v_a_1408_);
lean_dec_ref(v_a_1407_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(lean_object* v_e_1413_, lean_object* v___y_1414_){
_start:
{
uint8_t v___x_1416_; 
v___x_1416_ = l_Lean_Expr_hasMVar(v_e_1413_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; 
v___x_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1417_, 0, v_e_1413_);
return v___x_1417_;
}
else
{
lean_object* v___x_1418_; lean_object* v_mctx_1419_; lean_object* v___x_1420_; lean_object* v_fst_1421_; lean_object* v_snd_1422_; lean_object* v___x_1423_; lean_object* v_cache_1424_; lean_object* v_zetaDeltaFVarIds_1425_; lean_object* v_postponed_1426_; lean_object* v_diag_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1436_; 
v___x_1418_ = lean_st_ref_get(v___y_1414_);
v_mctx_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc_ref(v_mctx_1419_);
lean_dec(v___x_1418_);
v___x_1420_ = l_Lean_instantiateMVarsCore(v_mctx_1419_, v_e_1413_);
v_fst_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_fst_1421_);
v_snd_1422_ = lean_ctor_get(v___x_1420_, 1);
lean_inc(v_snd_1422_);
lean_dec_ref(v___x_1420_);
v___x_1423_ = lean_st_ref_take(v___y_1414_);
v_cache_1424_ = lean_ctor_get(v___x_1423_, 1);
v_zetaDeltaFVarIds_1425_ = lean_ctor_get(v___x_1423_, 2);
v_postponed_1426_ = lean_ctor_get(v___x_1423_, 3);
v_diag_1427_ = lean_ctor_get(v___x_1423_, 4);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1436_ == 0)
{
lean_object* v_unused_1437_; 
v_unused_1437_ = lean_ctor_get(v___x_1423_, 0);
lean_dec(v_unused_1437_);
v___x_1429_ = v___x_1423_;
v_isShared_1430_ = v_isSharedCheck_1436_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_diag_1427_);
lean_inc(v_postponed_1426_);
lean_inc(v_zetaDeltaFVarIds_1425_);
lean_inc(v_cache_1424_);
lean_dec(v___x_1423_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1436_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 0, v_snd_1422_);
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_snd_1422_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v_cache_1424_);
lean_ctor_set(v_reuseFailAlloc_1435_, 2, v_zetaDeltaFVarIds_1425_);
lean_ctor_set(v_reuseFailAlloc_1435_, 3, v_postponed_1426_);
lean_ctor_set(v_reuseFailAlloc_1435_, 4, v_diag_1427_);
v___x_1432_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = lean_st_ref_put(v___y_1414_, v___x_1432_);
v___x_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1434_, 0, v_fst_1421_);
return v___x_1434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg___boxed(lean_object* v_e_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_e_1438_, v___y_1439_);
lean_dec(v___y_1439_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0(lean_object* v_e_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_e_1442_, v___y_1447_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___boxed(lean_object* v_e_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0(v_e_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(lean_object* v_cls_1462_, lean_object* v_msg_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v_ref_1469_; lean_object* v___x_1470_; lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1515_; 
v_ref_1469_ = lean_ctor_get(v___y_1466_, 2);
v___x_1470_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(v_msg_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1473_ = v___x_1470_;
v_isShared_1474_ = v_isSharedCheck_1515_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1470_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1515_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1475_; lean_object* v_traceState_1476_; lean_object* v_env_1477_; lean_object* v_nextMacroScope_1478_; lean_object* v_ngen_1479_; lean_object* v_auxDeclNGen_1480_; lean_object* v_cache_1481_; lean_object* v_messages_1482_; lean_object* v_infoState_1483_; lean_object* v_snapshotTasks_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1514_; 
v___x_1475_ = lean_st_ref_take(v___y_1467_);
v_traceState_1476_ = lean_ctor_get(v___x_1475_, 4);
v_env_1477_ = lean_ctor_get(v___x_1475_, 0);
v_nextMacroScope_1478_ = lean_ctor_get(v___x_1475_, 1);
v_ngen_1479_ = lean_ctor_get(v___x_1475_, 2);
v_auxDeclNGen_1480_ = lean_ctor_get(v___x_1475_, 3);
v_cache_1481_ = lean_ctor_get(v___x_1475_, 5);
v_messages_1482_ = lean_ctor_get(v___x_1475_, 6);
v_infoState_1483_ = lean_ctor_get(v___x_1475_, 7);
v_snapshotTasks_1484_ = lean_ctor_get(v___x_1475_, 8);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1486_ = v___x_1475_;
v_isShared_1487_ = v_isSharedCheck_1514_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_snapshotTasks_1484_);
lean_inc(v_infoState_1483_);
lean_inc(v_messages_1482_);
lean_inc(v_cache_1481_);
lean_inc(v_traceState_1476_);
lean_inc(v_auxDeclNGen_1480_);
lean_inc(v_ngen_1479_);
lean_inc(v_nextMacroScope_1478_);
lean_inc(v_env_1477_);
lean_dec(v___x_1475_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1514_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
uint64_t v_tid_1488_; lean_object* v_traces_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1513_; 
v_tid_1488_ = lean_ctor_get_uint64(v_traceState_1476_, sizeof(void*)*1);
v_traces_1489_ = lean_ctor_get(v_traceState_1476_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_traceState_1476_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1491_ = v_traceState_1476_;
v_isShared_1492_ = v_isSharedCheck_1513_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_traces_1489_);
lean_dec(v_traceState_1476_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1513_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1493_; double v___x_1494_; uint8_t v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1493_ = lean_box(0);
v___x_1494_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0);
v___x_1495_ = 0;
v___x_1496_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__1));
v___x_1497_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1497_, 0, v_cls_1462_);
lean_ctor_set(v___x_1497_, 1, v___x_1493_);
lean_ctor_set(v___x_1497_, 2, v___x_1496_);
lean_ctor_set_float(v___x_1497_, sizeof(void*)*3, v___x_1494_);
lean_ctor_set_float(v___x_1497_, sizeof(void*)*3 + 8, v___x_1494_);
lean_ctor_set_uint8(v___x_1497_, sizeof(void*)*3 + 16, v___x_1495_);
v___x_1498_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__2));
v___x_1499_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1497_);
lean_ctor_set(v___x_1499_, 1, v_a_1471_);
lean_ctor_set(v___x_1499_, 2, v___x_1498_);
lean_inc(v_ref_1469_);
v___x_1500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1500_, 0, v_ref_1469_);
lean_ctor_set(v___x_1500_, 1, v___x_1499_);
v___x_1501_ = l_Lean_PersistentArray_push___redArg(v_traces_1489_, v___x_1500_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 0, v___x_1501_);
v___x_1503_ = v___x_1491_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1501_);
lean_ctor_set_uint64(v_reuseFailAlloc_1512_, sizeof(void*)*1, v_tid_1488_);
v___x_1503_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1505_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 4, v___x_1503_);
v___x_1505_ = v___x_1486_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_env_1477_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_nextMacroScope_1478_);
lean_ctor_set(v_reuseFailAlloc_1511_, 2, v_ngen_1479_);
lean_ctor_set(v_reuseFailAlloc_1511_, 3, v_auxDeclNGen_1480_);
lean_ctor_set(v_reuseFailAlloc_1511_, 4, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1511_, 5, v_cache_1481_);
lean_ctor_set(v_reuseFailAlloc_1511_, 6, v_messages_1482_);
lean_ctor_set(v_reuseFailAlloc_1511_, 7, v_infoState_1483_);
lean_ctor_set(v_reuseFailAlloc_1511_, 8, v_snapshotTasks_1484_);
v___x_1505_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1509_; 
v___x_1506_ = lean_st_ref_put(v___y_1467_, v___x_1505_);
v___x_1507_ = lean_box(0);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v___x_1507_);
v___x_1509_ = v___x_1473_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg___boxed(lean_object* v_cls_1516_, lean_object* v_msg_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v_cls_1516_, v_msg_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
return v_res_1523_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1530_ = lean_box(0);
v___x_1531_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__3));
v___x_1532_ = l_Lean_mkConst(v___x_1531_, v___x_1530_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(lean_object* v_numIndices_1533_, lean_object* v_a_1534_, lean_object* v_as_1535_, lean_object* v_i_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v_zero_1542_; uint8_t v_isZero_1543_; 
v_zero_1542_ = lean_unsigned_to_nat(0u);
v_isZero_1543_ = lean_nat_dec_eq(v_i_1536_, v_zero_1542_);
if (v_isZero_1543_ == 1)
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
lean_dec(v_i_1536_);
lean_dec_ref(v_a_1534_);
v___x_1544_ = lean_box(0);
v___x_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
return v___x_1545_;
}
else
{
lean_object* v_one_1546_; lean_object* v_n_1547_; lean_object* v___x_1548_; 
v_one_1546_ = lean_unsigned_to_nat(1u);
v_n_1547_ = lean_nat_sub(v_i_1536_, v_one_1546_);
lean_dec(v_i_1536_);
v___x_1548_ = lean_array_fget(v_as_1535_, v_n_1547_);
if (lean_obj_tag(v___x_1548_) == 0)
{
v_i_1536_ = v_n_1547_;
goto _start;
}
else
{
lean_object* v_val_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1614_; 
v_val_1550_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1552_ = v___x_1548_;
v_isShared_1553_ = v_isSharedCheck_1614_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_val_1550_);
lean_dec(v___x_1548_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1614_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1554_; uint8_t v___x_1555_; 
v___x_1554_ = l_Lean_LocalDecl_index(v_val_1550_);
v___x_1555_ = lean_nat_dec_le(v_numIndices_1533_, v___x_1554_);
lean_dec(v___x_1554_);
if (v___x_1555_ == 0)
{
uint8_t v___x_1556_; 
v___x_1556_ = l_Lean_LocalDecl_isAuxDecl(v_val_1550_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = l_Lean_LocalDecl_type(v_val_1550_);
lean_inc_ref(v___x_1557_);
lean_inc_ref(v_a_1534_);
v___x_1558_ = l_Lean_Meta_isExprDefEq(v_a_1534_, v___x_1557_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1603_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1561_ = v___x_1558_;
v_isShared_1562_ = v_isSharedCheck_1603_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1558_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1603_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
uint8_t v___x_1563_; 
v___x_1563_ = lean_unbox(v_a_1559_);
lean_dec(v_a_1559_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; uint8_t v___x_1565_; 
lean_del_object(v___x_1561_);
v___x_1564_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__1));
v___x_1565_ = l_Lean_Expr_isAppOfArity(v_a_1534_, v___x_1564_, v_one_1546_);
if (v___x_1565_ == 0)
{
lean_dec_ref(v___x_1557_);
lean_del_object(v___x_1552_);
lean_dec(v_val_1550_);
v_i_1536_ = v_n_1547_;
goto _start;
}
else
{
lean_object* v___x_1567_; uint8_t v___x_1568_; 
v___x_1567_ = l_Lean_Expr_appArg_x21(v_a_1534_);
v___x_1568_ = l_Lean_Expr_isAppOfArity(v___x_1567_, v___x_1564_, v_one_1546_);
if (v___x_1568_ == 0)
{
lean_dec_ref(v___x_1567_);
lean_dec_ref(v___x_1557_);
lean_del_object(v___x_1552_);
lean_dec(v_val_1550_);
v_i_1536_ = v_n_1547_;
goto _start;
}
else
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1570_ = l_Lean_Expr_appArg_x21(v___x_1567_);
lean_dec_ref(v___x_1567_);
lean_inc_ref(v___x_1570_);
v___x_1571_ = l_Lean_Meta_isExprDefEq(v___x_1570_, v___x_1557_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1587_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1574_ = v___x_1571_;
v_isShared_1575_ = v_isSharedCheck_1587_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1571_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1587_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
uint8_t v___x_1576_; 
v___x_1576_ = lean_unbox(v_a_1572_);
lean_dec(v_a_1572_);
if (v___x_1576_ == 0)
{
lean_del_object(v___x_1574_);
lean_dec_ref(v___x_1570_);
lean_del_object(v___x_1552_);
lean_dec(v_val_1550_);
v_i_1536_ = v_n_1547_;
goto _start;
}
else
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1582_; 
lean_dec(v_n_1547_);
lean_dec_ref(v_a_1534_);
v___x_1578_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4);
v___x_1579_ = l_Lean_LocalDecl_toExpr(v_val_1550_);
v___x_1580_ = l_Lean_mkAppB(v___x_1578_, v___x_1570_, v___x_1579_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v___x_1580_);
v___x_1582_ = v___x_1552_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1580_);
v___x_1582_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1584_; 
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 0, v___x_1582_);
v___x_1584_ = v___x_1574_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1582_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
lean_dec_ref(v___x_1570_);
lean_del_object(v___x_1552_);
lean_dec(v_val_1550_);
lean_dec(v_n_1547_);
lean_dec_ref(v_a_1534_);
v_a_1588_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1571_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1571_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
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
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
}
}
else
{
lean_object* v___x_1596_; lean_object* v___x_1598_; 
lean_dec_ref(v___x_1557_);
lean_dec(v_n_1547_);
lean_dec_ref(v_a_1534_);
v___x_1596_ = l_Lean_LocalDecl_toExpr(v_val_1550_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v___x_1596_);
v___x_1598_ = v___x_1552_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1600_; 
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v___x_1598_);
v___x_1600_ = v___x_1561_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_dec_ref(v___x_1557_);
lean_del_object(v___x_1552_);
lean_dec(v_val_1550_);
lean_dec(v_n_1547_);
lean_dec_ref(v_a_1534_);
v_a_1604_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1558_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1558_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
else
{
lean_del_object(v___x_1552_);
lean_dec(v_val_1550_);
v_i_1536_ = v_n_1547_;
goto _start;
}
}
else
{
lean_del_object(v___x_1552_);
lean_dec(v_val_1550_);
v_i_1536_ = v_n_1547_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_numIndices_1615_, lean_object* v_a_1616_, lean_object* v_as_1617_, lean_object* v_i_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_numIndices_1615_, v_a_1616_, v_as_1617_, v_i_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec_ref(v_as_1617_);
lean_dec(v_numIndices_1615_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(lean_object* v_numIndices_1625_, lean_object* v_a_1626_, lean_object* v_as_1627_, lean_object* v_i_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v_zero_1637_; uint8_t v_isZero_1638_; 
v_zero_1637_ = lean_unsigned_to_nat(0u);
v_isZero_1638_ = lean_nat_dec_eq(v_i_1628_, v_zero_1637_);
if (v_isZero_1638_ == 1)
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_dec(v_i_1628_);
lean_dec_ref(v_a_1626_);
v___x_1639_ = lean_box(0);
v___x_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
return v___x_1640_;
}
else
{
lean_object* v_one_1641_; lean_object* v_n_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v_one_1641_ = lean_unsigned_to_nat(1u);
v_n_1642_ = lean_nat_sub(v_i_1628_, v_one_1641_);
lean_dec(v_i_1628_);
v___x_1643_ = lean_array_fget_borrowed(v_as_1627_, v_n_1642_);
lean_inc_ref(v_a_1626_);
v___x_1644_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_numIndices_1625_, v_a_1626_, v___x_1643_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_a_1645_);
if (lean_obj_tag(v_a_1645_) == 0)
{
lean_dec_ref_known(v___x_1644_, 1);
v_i_1628_ = v_n_1642_;
goto _start;
}
else
{
lean_dec_ref_known(v_a_1645_, 1);
lean_dec(v_n_1642_);
lean_dec_ref(v_a_1626_);
return v___x_1644_;
}
}
else
{
lean_dec(v_n_1642_);
lean_dec_ref(v_a_1626_);
return v___x_1644_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(lean_object* v_numIndices_1647_, lean_object* v_a_1648_, lean_object* v_x_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
if (lean_obj_tag(v_x_1649_) == 0)
{
lean_object* v_cs_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v_cs_1658_ = lean_ctor_get(v_x_1649_, 0);
v___x_1659_ = lean_array_get_size(v_cs_1658_);
v___x_1660_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_numIndices_1647_, v_a_1648_, v_cs_1658_, v___x_1659_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
return v___x_1660_;
}
else
{
lean_object* v_vs_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v_vs_1661_ = lean_ctor_get(v_x_1649_, 0);
v___x_1662_ = lean_array_get_size(v_vs_1661_);
v___x_1663_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_numIndices_1647_, v_a_1648_, v_vs_1661_, v___x_1662_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
return v___x_1663_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3___boxed(lean_object* v_numIndices_1664_, lean_object* v_a_1665_, lean_object* v_x_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_numIndices_1664_, v_a_1665_, v_x_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v_x_1666_);
lean_dec(v_numIndices_1664_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_numIndices_1676_, lean_object* v_a_1677_, lean_object* v_as_1678_, lean_object* v_i_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_numIndices_1676_, v_a_1677_, v_as_1678_, v_i_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v_as_1678_);
lean_dec(v_numIndices_1676_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(lean_object* v_numIndices_1689_, lean_object* v_a_1690_, lean_object* v_t_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v_root_1700_; lean_object* v_tail_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v_root_1700_ = lean_ctor_get(v_t_1691_, 0);
v_tail_1701_ = lean_ctor_get(v_t_1691_, 1);
v___x_1702_ = lean_array_get_size(v_tail_1701_);
lean_inc_ref(v_a_1690_);
v___x_1703_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_numIndices_1689_, v_a_1690_, v_tail_1701_, v___x_1702_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_a_1704_);
if (lean_obj_tag(v_a_1704_) == 0)
{
lean_object* v___x_1705_; 
lean_dec_ref_known(v___x_1703_, 1);
v___x_1705_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_numIndices_1689_, v_a_1690_, v_root_1700_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
return v___x_1705_;
}
else
{
lean_dec_ref_known(v_a_1704_, 1);
lean_dec_ref(v_a_1690_);
return v___x_1703_;
}
}
else
{
lean_dec_ref(v_a_1690_);
return v___x_1703_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1___boxed(lean_object* v_numIndices_1706_, lean_object* v_a_1707_, lean_object* v_t_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(v_numIndices_1706_, v_a_1707_, v_t_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v_t_1708_);
lean_dec(v_numIndices_1706_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(lean_object* v_numIndices_1718_, lean_object* v_a_1719_, lean_object* v_lctx_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v_decls_1729_; lean_object* v___x_1730_; 
v_decls_1729_ = lean_ctor_get(v_lctx_1720_, 1);
v___x_1730_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(v_numIndices_1718_, v_a_1719_, v_decls_1729_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1___boxed(lean_object* v_numIndices_1731_, lean_object* v_a_1732_, lean_object* v_lctx_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(v_numIndices_1731_, v_a_1732_, v_lctx_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v_lctx_1733_);
lean_dec(v_numIndices_1731_);
return v_res_1742_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3(void){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1748_ = lean_box(0);
v___x_1749_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2));
v___x_1750_ = l_Lean_mkConst(v___x_1749_, v___x_1748_);
return v___x_1750_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1754_ = lean_box(0);
v___x_1755_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__5));
v___x_1756_ = l_Lean_mkConst(v___x_1755_, v___x_1754_);
return v___x_1756_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10(void){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1763_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9));
v___x_1764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4));
v___x_1765_ = l_Lean_Name_append(v___x_1764_, v___x_1763_);
return v___x_1765_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12(void){
_start:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1767_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11));
v___x_1768_ = l_Lean_stringToMessageData(v___x_1767_);
return v___x_1768_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14(void){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13));
v___x_1771_ = l_Lean_stringToMessageData(v___x_1770_);
return v___x_1771_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17(void){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__16));
v___x_1776_ = l_Lean_MessageData_ofFormat(v___x_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(lean_object* v_numIndices_1777_, uint8_t v_useDecide_1778_, lean_object* v_prop_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v___x_1788_; lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1923_; 
v___x_1788_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_prop_1779_, v_a_1784_);
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1791_ = v___x_1788_;
v_isShared_1792_ = v_isSharedCheck_1923_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1788_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1923_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v_toCold_1890_; lean_object* v_options_1891_; uint8_t v_hasTrace_1892_; 
v_toCold_1890_ = lean_ctor_get(v_a_1785_, 0);
v_options_1891_ = lean_ctor_get(v_toCold_1890_, 2);
v_hasTrace_1892_ = lean_ctor_get_uint8(v_options_1891_, sizeof(void*)*1);
if (v_hasTrace_1892_ == 0)
{
v___y_1850_ = v_a_1780_;
v___y_1851_ = v_a_1781_;
v___y_1852_ = v_a_1782_;
v___y_1853_ = v_a_1783_;
v___y_1854_ = v_a_1784_;
v___y_1855_ = v_a_1785_;
v___y_1856_ = v_a_1786_;
goto v___jp_1849_;
}
else
{
lean_object* v_inheritedTraceOptions_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; uint8_t v___x_1896_; 
v_inheritedTraceOptions_1893_ = lean_ctor_get(v_toCold_1890_, 11);
v___x_1894_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9));
v___x_1895_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10);
v___x_1896_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1893_, v_options_1891_, v___x_1895_);
if (v___x_1896_ == 0)
{
v___y_1850_ = v_a_1780_;
v___y_1851_ = v_a_1781_;
v___y_1852_ = v_a_1782_;
v___y_1853_ = v_a_1783_;
v___y_1854_ = v_a_1784_;
v___y_1855_ = v_a_1785_;
v___y_1856_ = v_a_1786_;
goto v___jp_1849_;
}
else
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___y_1903_; lean_object* v___x_1916_; lean_object* v___x_1917_; uint8_t v___x_1918_; 
v___x_1897_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12);
lean_inc(v_a_1789_);
v___x_1898_ = l_Lean_MessageData_ofExpr(v_a_1789_);
v___x_1899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1897_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
v___x_1900_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14);
v___x_1901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1899_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
v___x_1916_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__1));
v___x_1917_ = lean_unsigned_to_nat(1u);
v___x_1918_ = l_Lean_Expr_isAppOfArity(v_a_1789_, v___x_1916_, v___x_1917_);
if (v___x_1918_ == 0)
{
goto v___jp_1914_;
}
else
{
lean_object* v___x_1919_; uint8_t v___x_1920_; 
v___x_1919_ = l_Lean_Expr_appArg_x21(v_a_1789_);
v___x_1920_ = l_Lean_Expr_isAppOfArity(v___x_1919_, v___x_1916_, v___x_1917_);
if (v___x_1920_ == 0)
{
lean_dec_ref(v___x_1919_);
goto v___jp_1914_;
}
else
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1921_ = l_Lean_Expr_appArg_x21(v___x_1919_);
lean_dec_ref(v___x_1919_);
v___x_1922_ = l_Lean_MessageData_ofExpr(v___x_1921_);
v___y_1903_ = v___x_1922_;
goto v___jp_1902_;
}
}
v___jp_1902_:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1901_);
lean_ctor_set(v___x_1904_, 1, v___y_1903_);
v___x_1905_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v___x_1894_, v___x_1904_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_dec_ref_known(v___x_1905_, 1);
v___y_1850_ = v_a_1780_;
v___y_1851_ = v_a_1781_;
v___y_1852_ = v_a_1782_;
v___y_1853_ = v_a_1783_;
v___y_1854_ = v_a_1784_;
v___y_1855_ = v_a_1785_;
v___y_1856_ = v_a_1786_;
goto v___jp_1849_;
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
lean_del_object(v___x_1791_);
lean_dec(v_a_1789_);
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1905_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1905_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
v___jp_1914_:
{
lean_object* v___x_1915_; 
v___x_1915_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17);
v___y_1903_ = v___x_1915_;
goto v___jp_1902_;
}
}
}
v___jp_1793_:
{
lean_object* v_lctx_1801_; lean_object* v___x_1802_; 
v_lctx_1801_ = lean_ctor_get(v___y_1797_, 2);
v___x_1802_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(v_numIndices_1777_, v_a_1789_, v_lctx_1801_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
return v___x_1802_;
}
v___jp_1803_:
{
if (lean_obj_tag(v___y_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v___x_1815_; uint8_t v___x_1816_; 
v_a_1814_ = lean_ctor_get(v___y_1813_, 0);
lean_inc(v_a_1814_);
lean_dec_ref_known(v___y_1813_, 1);
v___x_1815_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2));
v___x_1816_ = l_Lean_Expr_isConstOf(v_a_1814_, v___x_1815_);
lean_dec(v_a_1814_);
if (v___x_1816_ == 0)
{
lean_dec_ref(v___y_1810_);
lean_dec_ref(v___y_1808_);
lean_del_object(v___x_1791_);
v___y_1794_ = v___y_1804_;
v___y_1795_ = v___y_1812_;
v___y_1796_ = v___y_1807_;
v___y_1797_ = v___y_1809_;
v___y_1798_ = v___y_1811_;
v___y_1799_ = v___y_1806_;
v___y_1800_ = v___y_1805_;
goto v___jp_1793_;
}
else
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
lean_dec(v_a_1789_);
v___x_1817_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3);
v___x_1818_ = l_Lean_Meta_mkEqRefl(v___x_1817_, v___y_1809_, v___y_1811_, v___y_1806_, v___y_1805_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1832_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1821_ = v___x_1818_;
v_isShared_1822_ = v_isSharedCheck_1832_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1818_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1832_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1827_; 
v___x_1823_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6);
v___x_1824_ = l_Lean_Expr_appArg_x21(v___y_1808_);
lean_dec_ref(v___y_1808_);
v___x_1825_ = l_Lean_mkApp3(v___x_1823_, v___y_1810_, v___x_1824_, v_a_1819_);
if (v_isShared_1792_ == 0)
{
lean_ctor_set_tag(v___x_1791_, 1);
lean_ctor_set(v___x_1791_, 0, v___x_1825_);
v___x_1827_ = v___x_1791_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1825_);
v___x_1827_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
lean_object* v___x_1829_; 
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v___x_1827_);
v___x_1829_ = v___x_1821_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1827_);
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
else
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
lean_dec_ref(v___y_1810_);
lean_dec_ref(v___y_1808_);
lean_del_object(v___x_1791_);
v_a_1833_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___x_1818_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1818_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1833_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
}
else
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
lean_dec_ref(v___y_1810_);
lean_dec_ref(v___y_1808_);
lean_del_object(v___x_1791_);
lean_dec(v_a_1789_);
v_a_1841_ = lean_ctor_get(v___y_1813_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___y_1813_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___y_1813_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___y_1813_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
v___jp_1849_:
{
if (v_useDecide_1778_ == 0)
{
lean_del_object(v___x_1791_);
v___y_1794_ = v___y_1850_;
v___y_1795_ = v___y_1851_;
v___y_1796_ = v___y_1852_;
v___y_1797_ = v___y_1853_;
v___y_1798_ = v___y_1854_;
v___y_1799_ = v___y_1855_;
v___y_1800_ = v___y_1856_;
goto v___jp_1793_;
}
else
{
lean_object* v___x_1857_; lean_object* v_a_1858_; uint8_t v___x_1859_; 
lean_inc(v_a_1789_);
v___x_1857_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_a_1789_, v___y_1854_);
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
lean_inc(v_a_1858_);
lean_dec_ref(v___x_1857_);
v___x_1859_ = l_Lean_Expr_hasFVar(v_a_1858_);
if (v___x_1859_ == 0)
{
uint8_t v___x_1860_; 
v___x_1860_ = l_Lean_Expr_hasMVar(v_a_1858_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1861_; 
lean_inc(v_a_1858_);
v___x_1861_ = l_Lean_Meta_mkDecide(v_a_1858_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v_a_1862_; lean_object* v___x_1863_; uint8_t v_transparency_1864_; uint8_t v___x_1865_; uint8_t v___x_1866_; 
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
lean_inc(v_a_1862_);
lean_dec_ref_known(v___x_1861_, 1);
v___x_1863_ = l_Lean_Meta_Context_config(v___y_1853_);
v_transparency_1864_ = lean_ctor_get_uint8(v___x_1863_, 9);
lean_dec_ref(v___x_1863_);
v___x_1865_ = 1;
v___x_1866_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1864_, v___x_1865_);
if (v___x_1866_ == 0)
{
lean_object* v_keyedConfig_1867_; uint8_t v_trackZetaDelta_1868_; lean_object* v_zetaDeltaSet_1869_; lean_object* v_lctx_1870_; lean_object* v_localInstances_1871_; lean_object* v_defEqCtx_x3f_1872_; lean_object* v_synthPendingDepth_1873_; lean_object* v_customCanUnfoldPredicate_x3f_1874_; uint8_t v_univApprox_1875_; uint8_t v_inTypeClassResolution_1876_; uint8_t v_cacheInferType_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v_keyedConfig_1867_ = lean_ctor_get(v___y_1853_, 0);
v_trackZetaDelta_1868_ = lean_ctor_get_uint8(v___y_1853_, sizeof(void*)*7);
v_zetaDeltaSet_1869_ = lean_ctor_get(v___y_1853_, 1);
v_lctx_1870_ = lean_ctor_get(v___y_1853_, 2);
v_localInstances_1871_ = lean_ctor_get(v___y_1853_, 3);
v_defEqCtx_x3f_1872_ = lean_ctor_get(v___y_1853_, 4);
v_synthPendingDepth_1873_ = lean_ctor_get(v___y_1853_, 5);
v_customCanUnfoldPredicate_x3f_1874_ = lean_ctor_get(v___y_1853_, 6);
v_univApprox_1875_ = lean_ctor_get_uint8(v___y_1853_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1876_ = lean_ctor_get_uint8(v___y_1853_, sizeof(void*)*7 + 2);
v_cacheInferType_1877_ = lean_ctor_get_uint8(v___y_1853_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1867_);
v___x_1878_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1865_, v_keyedConfig_1867_);
lean_inc(v_customCanUnfoldPredicate_x3f_1874_);
lean_inc(v_synthPendingDepth_1873_);
lean_inc(v_defEqCtx_x3f_1872_);
lean_inc_ref(v_localInstances_1871_);
lean_inc_ref(v_lctx_1870_);
lean_inc(v_zetaDeltaSet_1869_);
v___x_1879_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
lean_ctor_set(v___x_1879_, 1, v_zetaDeltaSet_1869_);
lean_ctor_set(v___x_1879_, 2, v_lctx_1870_);
lean_ctor_set(v___x_1879_, 3, v_localInstances_1871_);
lean_ctor_set(v___x_1879_, 4, v_defEqCtx_x3f_1872_);
lean_ctor_set(v___x_1879_, 5, v_synthPendingDepth_1873_);
lean_ctor_set(v___x_1879_, 6, v_customCanUnfoldPredicate_x3f_1874_);
lean_ctor_set_uint8(v___x_1879_, sizeof(void*)*7, v_trackZetaDelta_1868_);
lean_ctor_set_uint8(v___x_1879_, sizeof(void*)*7 + 1, v_univApprox_1875_);
lean_ctor_set_uint8(v___x_1879_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1876_);
lean_ctor_set_uint8(v___x_1879_, sizeof(void*)*7 + 3, v_cacheInferType_1877_);
lean_inc(v___y_1856_);
lean_inc_ref(v___y_1855_);
lean_inc(v___y_1854_);
lean_inc(v_a_1862_);
v___x_1880_ = lean_whnf(v_a_1862_, v___x_1879_, v___y_1854_, v___y_1855_, v___y_1856_);
v___y_1804_ = v___y_1850_;
v___y_1805_ = v___y_1856_;
v___y_1806_ = v___y_1855_;
v___y_1807_ = v___y_1852_;
v___y_1808_ = v_a_1862_;
v___y_1809_ = v___y_1853_;
v___y_1810_ = v_a_1858_;
v___y_1811_ = v___y_1854_;
v___y_1812_ = v___y_1851_;
v___y_1813_ = v___x_1880_;
goto v___jp_1803_;
}
else
{
lean_object* v___x_1881_; 
lean_inc(v___y_1856_);
lean_inc_ref(v___y_1855_);
lean_inc(v___y_1854_);
lean_inc_ref(v___y_1853_);
lean_inc(v_a_1862_);
v___x_1881_ = lean_whnf(v_a_1862_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
v___y_1804_ = v___y_1850_;
v___y_1805_ = v___y_1856_;
v___y_1806_ = v___y_1855_;
v___y_1807_ = v___y_1852_;
v___y_1808_ = v_a_1862_;
v___y_1809_ = v___y_1853_;
v___y_1810_ = v_a_1858_;
v___y_1811_ = v___y_1854_;
v___y_1812_ = v___y_1851_;
v___y_1813_ = v___x_1881_;
goto v___jp_1803_;
}
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_dec(v_a_1858_);
lean_del_object(v___x_1791_);
lean_dec(v_a_1789_);
v_a_1882_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1861_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1861_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
else
{
lean_dec(v_a_1858_);
lean_del_object(v___x_1791_);
v___y_1794_ = v___y_1850_;
v___y_1795_ = v___y_1851_;
v___y_1796_ = v___y_1852_;
v___y_1797_ = v___y_1853_;
v___y_1798_ = v___y_1854_;
v___y_1799_ = v___y_1855_;
v___y_1800_ = v___y_1856_;
goto v___jp_1793_;
}
}
else
{
lean_dec(v_a_1858_);
lean_del_object(v___x_1791_);
v___y_1794_ = v___y_1850_;
v___y_1795_ = v___y_1851_;
v___y_1796_ = v___y_1852_;
v___y_1797_ = v___y_1853_;
v___y_1798_ = v___y_1854_;
v___y_1799_ = v___y_1855_;
v___y_1800_ = v___y_1856_;
goto v___jp_1793_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___boxed(lean_object* v_numIndices_1924_, lean_object* v_useDecide_1925_, lean_object* v_prop_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_){
_start:
{
uint8_t v_useDecide_boxed_1935_; lean_object* v_res_1936_; 
v_useDecide_boxed_1935_ = lean_unbox(v_useDecide_1925_);
v_res_1936_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_1924_, v_useDecide_boxed_1935_, v_prop_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
lean_dec(v_a_1933_);
lean_dec_ref(v_a_1932_);
lean_dec(v_a_1931_);
lean_dec_ref(v_a_1930_);
lean_dec(v_a_1929_);
lean_dec_ref(v_a_1928_);
lean_dec(v_a_1927_);
lean_dec(v_numIndices_1924_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2(lean_object* v_cls_1937_, lean_object* v_msg_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v___x_1947_; 
v___x_1947_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v_cls_1937_, v_msg_1938_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___boxed(lean_object* v_cls_1948_, lean_object* v_msg_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2(v_cls_1948_, v_msg_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2(lean_object* v_numIndices_1959_, lean_object* v_a_1960_, lean_object* v_as_1961_, lean_object* v_i_1962_, lean_object* v_a_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_numIndices_1959_, v_a_1960_, v_as_1961_, v_i_1962_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_numIndices_1973_, lean_object* v_a_1974_, lean_object* v_as_1975_, lean_object* v_i_1976_, lean_object* v_a_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2(v_numIndices_1973_, v_a_1974_, v_as_1975_, v_i_1976_, v_a_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v_as_1975_);
lean_dec(v_numIndices_1973_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5(lean_object* v_numIndices_1987_, lean_object* v_a_1988_, lean_object* v_as_1989_, lean_object* v_i_1990_, lean_object* v_a_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v___x_2000_; 
v___x_2000_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_numIndices_1987_, v_a_1988_, v_as_1989_, v_i_1990_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_numIndices_2001_, lean_object* v_a_2002_, lean_object* v_as_2003_, lean_object* v_i_2004_, lean_object* v_a_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5(v_numIndices_2001_, v_a_2002_, v_as_2003_, v_i_2004_, v_a_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec_ref(v_as_2003_);
lean_dec(v_numIndices_2001_);
return v_res_2014_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3(void){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2020_ = lean_box(0);
v___x_2021_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__2));
v___x_2022_ = l_Lean_mkConst(v___x_2021_, v___x_2020_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27(lean_object* v_numIndices_2026_, uint8_t v_useDecideBool_2027_, lean_object* v_e_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_){
_start:
{
lean_object* v___x_2037_; 
lean_inc_ref(v_e_2028_);
v___x_2037_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2028_, v_a_2033_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2218_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2040_ = v___x_2037_;
v_isShared_2041_ = v_isSharedCheck_2218_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2037_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2218_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2047_; uint8_t v___x_2048_; 
v___x_2047_ = l_Lean_Expr_cleanupAnnotations(v_a_2038_);
v___x_2048_ = l_Lean_Expr_isApp(v___x_2047_);
if (v___x_2048_ == 0)
{
lean_dec_ref(v___x_2047_);
lean_dec_ref(v_e_2028_);
goto v___jp_2042_;
}
else
{
lean_object* v_arg_2049_; lean_object* v___x_2050_; uint8_t v___x_2051_; 
v_arg_2049_ = lean_ctor_get(v___x_2047_, 1);
lean_inc_ref(v_arg_2049_);
v___x_2050_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2047_);
v___x_2051_ = l_Lean_Expr_isApp(v___x_2050_);
if (v___x_2051_ == 0)
{
lean_dec_ref(v___x_2050_);
lean_dec_ref(v_arg_2049_);
lean_dec_ref(v_e_2028_);
goto v___jp_2042_;
}
else
{
lean_object* v_arg_2052_; lean_object* v___x_2053_; uint8_t v___x_2054_; 
v_arg_2052_ = lean_ctor_get(v___x_2050_, 1);
lean_inc_ref(v_arg_2052_);
v___x_2053_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2050_);
v___x_2054_ = l_Lean_Expr_isApp(v___x_2053_);
if (v___x_2054_ == 0)
{
lean_dec_ref(v___x_2053_);
lean_dec_ref(v_arg_2052_);
lean_dec_ref(v_arg_2049_);
lean_dec_ref(v_e_2028_);
goto v___jp_2042_;
}
else
{
lean_object* v_arg_2055_; lean_object* v___x_2056_; uint8_t v___x_2057_; 
v_arg_2055_ = lean_ctor_get(v___x_2053_, 1);
lean_inc_ref(v_arg_2055_);
v___x_2056_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2053_);
v___x_2057_ = l_Lean_Expr_isApp(v___x_2056_);
if (v___x_2057_ == 0)
{
lean_dec_ref(v___x_2056_);
lean_dec_ref(v_arg_2055_);
lean_dec_ref(v_arg_2052_);
lean_dec_ref(v_arg_2049_);
lean_dec_ref(v_e_2028_);
goto v___jp_2042_;
}
else
{
lean_object* v_arg_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; 
v_arg_2058_ = lean_ctor_get(v___x_2056_, 1);
lean_inc_ref(v_arg_2058_);
v___x_2059_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2056_);
v___x_2060_ = l_Lean_Expr_isApp(v___x_2059_);
if (v___x_2060_ == 0)
{
lean_dec_ref(v___x_2059_);
lean_dec_ref(v_arg_2058_);
lean_dec_ref(v_arg_2055_);
lean_dec_ref(v_arg_2052_);
lean_dec_ref(v_arg_2049_);
lean_dec_ref(v_e_2028_);
goto v___jp_2042_;
}
else
{
lean_object* v_arg_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v_arg_2061_ = lean_ctor_get(v___x_2059_, 1);
lean_inc_ref(v_arg_2061_);
v___x_2062_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2059_);
v___x_2063_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__2));
v___x_2064_ = l_Lean_Expr_isConstOf(v___x_2062_, v___x_2063_);
if (v___x_2064_ == 0)
{
lean_dec_ref(v___x_2062_);
lean_dec_ref(v_arg_2061_);
lean_dec_ref(v_arg_2058_);
lean_dec_ref(v_arg_2055_);
lean_dec_ref(v_arg_2052_);
lean_dec_ref(v_arg_2049_);
lean_dec_ref(v_e_2028_);
goto v___jp_2042_;
}
else
{
lean_object* v___x_2065_; 
lean_del_object(v___x_2040_);
lean_inc_ref(v_arg_2058_);
v___x_2065_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2026_, v_useDecideBool_2027_, v_arg_2058_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2209_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2068_ = v___x_2065_;
v_isShared_2069_ = v_isSharedCheck_2209_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2065_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2209_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2070_; 
v___x_2070_ = l_Lean_Expr_constLevels_x21(v___x_2062_);
if (lean_obj_tag(v_a_2066_) == 1)
{
lean_object* v_val_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2086_; 
lean_dec_ref(v___x_2062_);
lean_dec_ref(v_e_2028_);
v_val_2071_ = lean_ctor_get(v_a_2066_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v_a_2066_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2073_ = v_a_2066_;
v_isShared_2074_ = v_isSharedCheck_2086_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_val_2071_);
lean_dec(v_a_2066_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2086_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2079_; 
v___x_2075_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__7));
v___x_2076_ = l_Lean_mkConst(v___x_2075_, v___x_2070_);
lean_inc_ref(v_arg_2052_);
v___x_2077_ = l_Lean_mkApp6(v___x_2076_, v_arg_2058_, v_arg_2055_, v_val_2071_, v_arg_2061_, v_arg_2052_, v_arg_2049_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2077_);
v___x_2079_ = v___x_2073_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_2077_);
v___x_2079_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2083_; 
v___x_2080_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2080_, 0, v_arg_2052_);
lean_ctor_set(v___x_2080_, 1, v___x_2079_);
lean_ctor_set_uint8(v___x_2080_, sizeof(void*)*2, v___x_2064_);
v___x_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 0, v___x_2081_);
v___x_2083_ = v___x_2068_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
else
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
lean_del_object(v___x_2068_);
lean_dec(v_a_2066_);
lean_inc_ref(v_arg_2058_);
v___x_2087_ = l_Lean_mkNot(v_arg_2058_);
v___x_2088_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2026_, v_useDecideBool_2027_, v___x_2087_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2200_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2091_ = v___x_2088_;
v_isShared_2092_ = v_isSharedCheck_2200_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2088_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2200_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
if (lean_obj_tag(v_a_2089_) == 1)
{
lean_object* v_val_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2108_; 
lean_dec_ref(v___x_2062_);
lean_dec_ref(v_e_2028_);
v_val_2093_ = lean_ctor_get(v_a_2089_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v_a_2089_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2095_ = v_a_2089_;
v_isShared_2096_ = v_isSharedCheck_2108_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_val_2093_);
lean_dec(v_a_2089_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2108_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2097_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__9));
v___x_2098_ = l_Lean_mkConst(v___x_2097_, v___x_2070_);
lean_inc_ref(v_arg_2049_);
v___x_2099_ = l_Lean_mkApp6(v___x_2098_, v_arg_2058_, v_arg_2055_, v_val_2093_, v_arg_2061_, v_arg_2052_, v_arg_2049_);
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 0, v___x_2099_);
v___x_2101_ = v___x_2095_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2105_; 
v___x_2102_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2102_, 0, v_arg_2049_);
lean_ctor_set(v___x_2102_, 1, v___x_2101_);
lean_ctor_set_uint8(v___x_2102_, sizeof(void*)*2, v___x_2064_);
v___x_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 0, v___x_2103_);
v___x_2105_ = v___x_2091_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
else
{
lean_object* v___x_2109_; 
lean_del_object(v___x_2091_);
lean_dec(v_a_2089_);
lean_inc(v_a_2035_);
lean_inc_ref(v_a_2034_);
lean_inc(v_a_2033_);
lean_inc_ref(v_a_2032_);
lean_inc(v_a_2031_);
lean_inc_ref(v_a_2030_);
lean_inc(v_a_2029_);
lean_inc_ref(v_arg_2058_);
v___x_2109_ = lean_simp(v_arg_2058_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2191_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2112_ = v___x_2109_;
v_isShared_2113_ = v_isSharedCheck_2191_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2109_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2191_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v_expr_2114_; uint8_t v___x_2115_; 
v_expr_2114_ = lean_ctor_get(v_a_2110_, 0);
v___x_2115_ = lean_expr_eqv(v_expr_2114_, v_arg_2058_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
lean_del_object(v___x_2112_);
v___x_2116_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3);
lean_inc_ref(v_expr_2114_);
v___x_2117_ = l_Lean_Expr_app___override(v___x_2116_, v_expr_2114_);
v___x_2118_ = lean_box(0);
v___x_2119_ = l_Lean_Meta_trySynthInstance(v___x_2117_, v___x_2118_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2168_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2122_ = v___x_2119_;
v_isShared_2123_ = v_isSharedCheck_2168_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2119_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2168_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
if (lean_obj_tag(v_a_2120_) == 1)
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2154_; 
lean_inc_ref(v_expr_2114_);
lean_del_object(v___x_2122_);
lean_dec_ref(v_e_2028_);
v_a_2124_ = lean_ctor_get(v_a_2120_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v_a_2120_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2126_ = v_a_2120_;
v_isShared_2127_ = v_isSharedCheck_2154_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v_a_2120_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2154_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2128_; 
v___x_2128_ = l_Lean_Meta_Simp_Result_getProof(v_a_2110_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2145_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2131_ = v___x_2128_;
v_isShared_2132_ = v_isSharedCheck_2145_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2128_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2145_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2138_; 
v___x_2133_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__5));
v___x_2134_ = l_Lean_mkConst(v___x_2133_, v___x_2070_);
lean_inc_ref(v_arg_2049_);
lean_inc_ref(v_arg_2052_);
lean_inc(v_a_2124_);
lean_inc_ref(v_expr_2114_);
lean_inc_ref(v_arg_2061_);
v___x_2135_ = l_Lean_mkApp8(v___x_2134_, v_arg_2061_, v_arg_2058_, v_expr_2114_, v_arg_2055_, v_a_2124_, v_arg_2052_, v_arg_2049_, v_a_2129_);
v___x_2136_ = l_Lean_mkApp5(v___x_2062_, v_arg_2061_, v_expr_2114_, v_a_2124_, v_arg_2052_, v_arg_2049_);
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 0, v___x_2135_);
v___x_2138_ = v___x_2126_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2135_);
v___x_2138_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2139_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2139_, 0, v___x_2136_);
lean_ctor_set(v___x_2139_, 1, v___x_2138_);
lean_ctor_set_uint8(v___x_2139_, sizeof(void*)*2, v___x_2064_);
v___x_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2139_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 0, v___x_2140_);
v___x_2142_ = v___x_2131_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_del_object(v___x_2126_);
lean_dec(v_a_2124_);
lean_dec_ref(v_expr_2114_);
lean_dec(v___x_2070_);
lean_dec_ref(v___x_2062_);
lean_dec_ref(v_arg_2061_);
lean_dec_ref(v_arg_2058_);
lean_dec_ref(v_arg_2055_);
lean_dec_ref(v_arg_2052_);
lean_dec_ref(v_arg_2049_);
v_a_2146_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2128_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2128_);
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
else
{
lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2165_; 
lean_dec(v_a_2120_);
lean_dec(v___x_2070_);
lean_dec_ref(v___x_2062_);
lean_dec_ref(v_arg_2061_);
lean_dec_ref(v_arg_2058_);
lean_dec_ref(v_arg_2055_);
lean_dec_ref(v_arg_2052_);
lean_dec_ref(v_arg_2049_);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_a_2110_);
if (v_isSharedCheck_2165_ == 0)
{
lean_object* v_unused_2166_; lean_object* v_unused_2167_; 
v_unused_2166_ = lean_ctor_get(v_a_2110_, 1);
lean_dec(v_unused_2166_);
v_unused_2167_ = lean_ctor_get(v_a_2110_, 0);
lean_dec(v_unused_2167_);
v___x_2156_ = v_a_2110_;
v_isShared_2157_ = v_isSharedCheck_2165_;
goto v_resetjp_2155_;
}
else
{
lean_dec(v_a_2110_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2165_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 1, v___x_2118_);
lean_ctor_set(v___x_2156_, 0, v_e_2028_);
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_e_2028_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v___x_2118_);
v___x_2159_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
lean_object* v___x_2160_; lean_object* v___x_2162_; 
lean_ctor_set_uint8(v___x_2159_, sizeof(void*)*2, v___x_2064_);
v___x_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 0, v___x_2160_);
v___x_2162_ = v___x_2122_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2160_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
}
}
else
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
lean_dec(v_a_2110_);
lean_dec(v___x_2070_);
lean_dec_ref(v___x_2062_);
lean_dec_ref(v_arg_2061_);
lean_dec_ref(v_arg_2058_);
lean_dec_ref(v_arg_2055_);
lean_dec_ref(v_arg_2052_);
lean_dec_ref(v_arg_2049_);
lean_dec_ref(v_e_2028_);
v_a_2169_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2119_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2119_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
else
{
lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2188_; 
lean_dec(v___x_2070_);
lean_dec_ref(v___x_2062_);
lean_dec_ref(v_arg_2061_);
lean_dec_ref(v_arg_2058_);
lean_dec_ref(v_arg_2055_);
lean_dec_ref(v_arg_2052_);
lean_dec_ref(v_arg_2049_);
v_isSharedCheck_2188_ = !lean_is_exclusive(v_a_2110_);
if (v_isSharedCheck_2188_ == 0)
{
lean_object* v_unused_2189_; lean_object* v_unused_2190_; 
v_unused_2189_ = lean_ctor_get(v_a_2110_, 1);
lean_dec(v_unused_2189_);
v_unused_2190_ = lean_ctor_get(v_a_2110_, 0);
lean_dec(v_unused_2190_);
v___x_2178_ = v_a_2110_;
v_isShared_2179_ = v_isSharedCheck_2188_;
goto v_resetjp_2177_;
}
else
{
lean_dec(v_a_2110_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2188_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2180_; lean_object* v___x_2182_; 
v___x_2180_ = lean_box(0);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 1, v___x_2180_);
lean_ctor_set(v___x_2178_, 0, v_e_2028_);
v___x_2182_ = v___x_2178_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_e_2028_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v___x_2180_);
v___x_2182_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
lean_object* v___x_2183_; lean_object* v___x_2185_; 
lean_ctor_set_uint8(v___x_2182_, sizeof(void*)*2, v___x_2064_);
v___x_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2182_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 0, v___x_2183_);
v___x_2185_ = v___x_2112_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2183_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_dec(v___x_2070_);
lean_dec_ref(v___x_2062_);
lean_dec_ref(v_arg_2061_);
lean_dec_ref(v_arg_2058_);
lean_dec_ref(v_arg_2055_);
lean_dec_ref(v_arg_2052_);
lean_dec_ref(v_arg_2049_);
lean_dec_ref(v_e_2028_);
v_a_2192_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2109_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2109_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
}
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
lean_dec(v___x_2070_);
lean_dec_ref(v___x_2062_);
lean_dec_ref(v_arg_2061_);
lean_dec_ref(v_arg_2058_);
lean_dec_ref(v_arg_2055_);
lean_dec_ref(v_arg_2052_);
lean_dec_ref(v_arg_2049_);
lean_dec_ref(v_e_2028_);
v_a_2201_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2088_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2088_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
}
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec_ref(v___x_2062_);
lean_dec_ref(v_arg_2061_);
lean_dec_ref(v_arg_2058_);
lean_dec_ref(v_arg_2055_);
lean_dec_ref(v_arg_2052_);
lean_dec_ref(v_arg_2049_);
lean_dec_ref(v_e_2028_);
v_a_2210_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2065_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2065_);
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
}
}
}
v___jp_2042_:
{
lean_object* v___x_2043_; lean_object* v___x_2045_; 
v___x_2043_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__0));
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 0, v___x_2043_);
v___x_2045_ = v___x_2040_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2043_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2226_; 
lean_dec_ref(v_e_2028_);
v_a_2219_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2221_ = v___x_2037_;
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2037_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___boxed(lean_object* v_numIndices_2227_, lean_object* v_useDecideBool_2228_, lean_object* v_e_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_){
_start:
{
uint8_t v_useDecideBool_boxed_2238_; lean_object* v_res_2239_; 
v_useDecideBool_boxed_2238_ = lean_unbox(v_useDecideBool_2228_);
v_res_2239_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27(v_numIndices_2227_, v_useDecideBool_boxed_2238_, v_e_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_);
lean_dec(v_a_2236_);
lean_dec_ref(v_a_2235_);
lean_dec(v_a_2234_);
lean_dec_ref(v_a_2233_);
lean_dec(v_a_2232_);
lean_dec_ref(v_a_2231_);
lean_dec(v_a_2230_);
lean_dec(v_numIndices_2227_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(lean_object* v_e_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_){
_start:
{
if (lean_obj_tag(v_e_2243_) == 6)
{
lean_object* v_binderName_2247_; lean_object* v___x_2248_; 
v_binderName_2247_ = lean_ctor_get(v_e_2243_, 0);
lean_inc(v_binderName_2247_);
v___x_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2248_, 0, v_binderName_2247_);
return v___x_2248_;
}
else
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__1));
v___x_2250_ = l_Lean_Core_mkFreshUserName(v___x_2249_, v_a_2244_, v_a_2245_);
return v___x_2250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___boxed(lean_object* v_e_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_e_2251_, v_a_2252_, v_a_2253_);
lean_dec(v_a_2253_);
lean_dec_ref(v_a_2252_);
lean_dec_ref(v_e_2251_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName(lean_object* v_e_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_){
_start:
{
lean_object* v___x_2262_; 
v___x_2262_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_e_2256_, v_a_2259_, v_a_2260_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___boxed(lean_object* v_e_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName(v_e_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_);
lean_dec(v_a_2267_);
lean_dec_ref(v_a_2266_);
lean_dec(v_a_2265_);
lean_dec_ref(v_a_2264_);
lean_dec_ref(v_e_2263_);
return v_res_2269_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3(void){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2275_ = lean_box(0);
v___x_2276_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__2));
v___x_2277_ = l_Lean_mkConst(v___x_2276_, v___x_2275_);
return v___x_2277_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4(void){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2278_ = lean_unsigned_to_nat(0u);
v___x_2279_ = l_Lean_mkBVar(v___x_2278_);
return v___x_2279_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7(void){
_start:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2284_ = lean_box(0);
v___x_2285_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__6));
v___x_2286_ = l_Lean_mkConst(v___x_2285_, v___x_2284_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27(lean_object* v_numIndices_2290_, uint8_t v_useDecideBool_2291_, lean_object* v_e_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_){
_start:
{
lean_object* v___x_2301_; 
lean_inc_ref(v_e_2292_);
v___x_2301_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2292_, v_a_2297_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2511_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2304_ = v___x_2301_;
v_isShared_2305_ = v_isSharedCheck_2511_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2301_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2511_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2311_; uint8_t v___x_2312_; 
v___x_2311_ = l_Lean_Expr_cleanupAnnotations(v_a_2302_);
v___x_2312_ = l_Lean_Expr_isApp(v___x_2311_);
if (v___x_2312_ == 0)
{
lean_dec_ref(v___x_2311_);
lean_dec_ref(v_e_2292_);
goto v___jp_2306_;
}
else
{
lean_object* v_arg_2313_; lean_object* v___x_2314_; uint8_t v___x_2315_; 
v_arg_2313_ = lean_ctor_get(v___x_2311_, 1);
lean_inc_ref(v_arg_2313_);
v___x_2314_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2311_);
v___x_2315_ = l_Lean_Expr_isApp(v___x_2314_);
if (v___x_2315_ == 0)
{
lean_dec_ref(v___x_2314_);
lean_dec_ref(v_arg_2313_);
lean_dec_ref(v_e_2292_);
goto v___jp_2306_;
}
else
{
lean_object* v_arg_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; 
v_arg_2316_ = lean_ctor_get(v___x_2314_, 1);
lean_inc_ref(v_arg_2316_);
v___x_2317_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2314_);
v___x_2318_ = l_Lean_Expr_isApp(v___x_2317_);
if (v___x_2318_ == 0)
{
lean_dec_ref(v___x_2317_);
lean_dec_ref(v_arg_2316_);
lean_dec_ref(v_arg_2313_);
lean_dec_ref(v_e_2292_);
goto v___jp_2306_;
}
else
{
lean_object* v_arg_2319_; lean_object* v___x_2320_; uint8_t v___x_2321_; 
v_arg_2319_ = lean_ctor_get(v___x_2317_, 1);
lean_inc_ref(v_arg_2319_);
v___x_2320_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2317_);
v___x_2321_ = l_Lean_Expr_isApp(v___x_2320_);
if (v___x_2321_ == 0)
{
lean_dec_ref(v___x_2320_);
lean_dec_ref(v_arg_2319_);
lean_dec_ref(v_arg_2316_);
lean_dec_ref(v_arg_2313_);
lean_dec_ref(v_e_2292_);
goto v___jp_2306_;
}
else
{
lean_object* v_arg_2322_; lean_object* v___x_2323_; uint8_t v___x_2324_; 
v_arg_2322_ = lean_ctor_get(v___x_2320_, 1);
lean_inc_ref(v_arg_2322_);
v___x_2323_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2320_);
v___x_2324_ = l_Lean_Expr_isApp(v___x_2323_);
if (v___x_2324_ == 0)
{
lean_dec_ref(v___x_2323_);
lean_dec_ref(v_arg_2322_);
lean_dec_ref(v_arg_2319_);
lean_dec_ref(v_arg_2316_);
lean_dec_ref(v_arg_2313_);
lean_dec_ref(v_e_2292_);
goto v___jp_2306_;
}
else
{
lean_object* v_arg_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; uint8_t v___x_2328_; 
v_arg_2325_ = lean_ctor_get(v___x_2323_, 1);
lean_inc_ref(v_arg_2325_);
v___x_2326_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2323_);
v___x_2327_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__4));
v___x_2328_ = l_Lean_Expr_isConstOf(v___x_2326_, v___x_2327_);
if (v___x_2328_ == 0)
{
lean_dec_ref(v___x_2326_);
lean_dec_ref(v_arg_2325_);
lean_dec_ref(v_arg_2322_);
lean_dec_ref(v_arg_2319_);
lean_dec_ref(v_arg_2316_);
lean_dec_ref(v_arg_2313_);
lean_dec_ref(v_e_2292_);
goto v___jp_2306_;
}
else
{
lean_object* v___x_2329_; 
lean_del_object(v___x_2304_);
lean_inc_ref(v_arg_2322_);
v___x_2329_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2290_, v_useDecideBool_2291_, v_arg_2322_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2502_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2332_ = v___x_2329_;
v_isShared_2333_ = v_isSharedCheck_2502_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2329_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2502_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2334_; 
v___x_2334_ = l_Lean_Expr_constLevels_x21(v___x_2326_);
if (lean_obj_tag(v_a_2330_) == 1)
{
lean_object* v_val_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2352_; 
lean_dec_ref(v___x_2326_);
lean_dec_ref(v_e_2292_);
v_val_2335_ = lean_ctor_get(v_a_2330_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v_a_2330_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2337_ = v_a_2330_;
v_isShared_2338_ = v_isSharedCheck_2352_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_val_2335_);
lean_dec(v_a_2330_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2352_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2345_; 
lean_inc(v_val_2335_);
lean_inc_ref(v_arg_2316_);
v___x_2339_ = l_Lean_Expr_app___override(v_arg_2316_, v_val_2335_);
v___x_2340_ = l_Lean_Expr_headBeta(v___x_2339_);
v___x_2341_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__11));
v___x_2342_ = l_Lean_mkConst(v___x_2341_, v___x_2334_);
v___x_2343_ = l_Lean_mkApp6(v___x_2342_, v_arg_2322_, v_arg_2319_, v_val_2335_, v_arg_2325_, v_arg_2316_, v_arg_2313_);
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 0, v___x_2343_);
v___x_2345_ = v___x_2337_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2343_);
v___x_2345_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2349_; 
v___x_2346_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2346_, 0, v___x_2340_);
lean_ctor_set(v___x_2346_, 1, v___x_2345_);
lean_ctor_set_uint8(v___x_2346_, sizeof(void*)*2, v___x_2328_);
v___x_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2346_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v___x_2347_);
v___x_2349_ = v___x_2332_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2347_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
else
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
lean_del_object(v___x_2332_);
lean_dec(v_a_2330_);
lean_inc_ref(v_arg_2322_);
v___x_2353_ = l_Lean_mkNot(v_arg_2322_);
v___x_2354_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2290_, v_useDecideBool_2291_, v___x_2353_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2493_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2357_ = v___x_2354_;
v_isShared_2358_ = v_isSharedCheck_2493_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2354_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2493_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
if (lean_obj_tag(v_a_2355_) == 1)
{
lean_object* v_val_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2376_; 
lean_dec_ref(v___x_2326_);
lean_dec_ref(v_e_2292_);
v_val_2359_ = lean_ctor_get(v_a_2355_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_a_2355_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2361_ = v_a_2355_;
v_isShared_2362_ = v_isSharedCheck_2376_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_val_2359_);
lean_dec(v_a_2355_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2376_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2369_; 
lean_inc(v_val_2359_);
lean_inc_ref(v_arg_2313_);
v___x_2363_ = l_Lean_Expr_app___override(v_arg_2313_, v_val_2359_);
v___x_2364_ = l_Lean_Expr_headBeta(v___x_2363_);
v___x_2365_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__13));
v___x_2366_ = l_Lean_mkConst(v___x_2365_, v___x_2334_);
v___x_2367_ = l_Lean_mkApp6(v___x_2366_, v_arg_2322_, v_arg_2319_, v_val_2359_, v_arg_2325_, v_arg_2316_, v_arg_2313_);
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 0, v___x_2367_);
v___x_2369_ = v___x_2361_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2373_; 
v___x_2370_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2370_, 0, v___x_2364_);
lean_ctor_set(v___x_2370_, 1, v___x_2369_);
lean_ctor_set_uint8(v___x_2370_, sizeof(void*)*2, v___x_2328_);
v___x_2371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2370_);
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 0, v___x_2371_);
v___x_2373_ = v___x_2357_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2371_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
else
{
lean_object* v___x_2377_; 
lean_del_object(v___x_2357_);
lean_dec(v_a_2355_);
lean_inc(v_a_2299_);
lean_inc_ref(v_a_2298_);
lean_inc(v_a_2297_);
lean_inc_ref(v_a_2296_);
lean_inc(v_a_2295_);
lean_inc_ref(v_a_2294_);
lean_inc(v_a_2293_);
lean_inc_ref(v_arg_2322_);
v___x_2377_ = lean_simp(v_arg_2322_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2484_; 
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2380_ = v___x_2377_;
v_isShared_2381_ = v_isSharedCheck_2484_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2377_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2484_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v_expr_2382_; uint8_t v___x_2383_; 
v_expr_2382_ = lean_ctor_get(v_a_2378_, 0);
v___x_2383_ = lean_expr_eqv(v_expr_2382_, v_arg_2322_);
if (v___x_2383_ == 0)
{
lean_object* v___x_2384_; 
lean_inc_ref(v_expr_2382_);
lean_del_object(v___x_2380_);
v___x_2384_ = l_Lean_Meta_Simp_Result_getProof(v_a_2378_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_a_2385_);
lean_dec_ref_known(v___x_2384_, 1);
v___x_2386_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3);
lean_inc_ref(v_expr_2382_);
v___x_2387_ = l_Lean_Expr_app___override(v___x_2386_, v_expr_2382_);
v___x_2388_ = lean_box(0);
v___x_2389_ = l_Lean_Meta_trySynthInstance(v___x_2387_, v___x_2388_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2453_; 
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2392_ = v___x_2389_;
v_isShared_2393_ = v_isSharedCheck_2453_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2389_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2453_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
if (lean_obj_tag(v_a_2390_) == 1)
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2447_; 
lean_del_object(v___x_2392_);
lean_dec_ref(v_e_2292_);
v_a_2394_ = lean_ctor_get(v_a_2390_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v_a_2390_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2396_ = v_a_2390_;
v_isShared_2397_ = v_isSharedCheck_2447_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v_a_2390_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2447_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2398_; 
v___x_2398_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_arg_2316_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_a_2399_; lean_object* v___x_2400_; 
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_a_2399_);
lean_dec_ref_known(v___x_2398_, 1);
v___x_2400_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_arg_2313_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2430_; 
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2403_ = v___x_2400_;
v_isShared_2404_ = v_isSharedCheck_2430_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2400_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2430_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; uint8_t v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2423_; 
v___x_2405_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3);
v___x_2406_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4);
lean_inc_n(v_a_2385_, 2);
lean_inc_ref_n(v_expr_2382_, 5);
lean_inc_ref_n(v_arg_2322_, 2);
v___x_2407_ = l_Lean_mkApp4(v___x_2405_, v_arg_2322_, v_expr_2382_, v_a_2385_, v___x_2406_);
lean_inc_ref(v_arg_2316_);
v___x_2408_ = l_Lean_Expr_app___override(v_arg_2316_, v___x_2407_);
v___x_2409_ = l_Lean_Expr_headBeta(v___x_2408_);
v___x_2410_ = 0;
v___x_2411_ = l_Lean_mkLambda(v_a_2399_, v___x_2410_, v_expr_2382_, v___x_2409_);
v___x_2412_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7);
v___x_2413_ = l_Lean_mkApp4(v___x_2412_, v_arg_2322_, v_expr_2382_, v_a_2385_, v___x_2406_);
lean_inc_ref(v_arg_2313_);
v___x_2414_ = l_Lean_Expr_app___override(v_arg_2313_, v___x_2413_);
v___x_2415_ = l_Lean_Expr_headBeta(v___x_2414_);
v___x_2416_ = l_Lean_mkNot(v_expr_2382_);
v___x_2417_ = l_Lean_mkLambda(v_a_2401_, v___x_2410_, v___x_2416_, v___x_2415_);
lean_inc(v_a_2394_);
lean_inc_ref(v_arg_2325_);
v___x_2418_ = l_Lean_mkApp5(v___x_2326_, v_arg_2325_, v_expr_2382_, v_a_2394_, v___x_2411_, v___x_2417_);
v___x_2419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__9));
v___x_2420_ = l_Lean_mkConst(v___x_2419_, v___x_2334_);
v___x_2421_ = l_Lean_mkApp8(v___x_2420_, v_arg_2325_, v_arg_2322_, v_expr_2382_, v_arg_2319_, v_a_2394_, v_arg_2316_, v_arg_2313_, v_a_2385_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 0, v___x_2421_);
v___x_2423_ = v___x_2396_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v___x_2421_);
v___x_2423_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2427_; 
v___x_2424_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2424_, 0, v___x_2418_);
lean_ctor_set(v___x_2424_, 1, v___x_2423_);
lean_ctor_set_uint8(v___x_2424_, sizeof(void*)*2, v___x_2328_);
v___x_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 0, v___x_2425_);
v___x_2427_ = v___x_2403_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2425_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
else
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2438_; 
lean_dec(v_a_2399_);
lean_del_object(v___x_2396_);
lean_dec(v_a_2394_);
lean_dec(v_a_2385_);
lean_dec_ref(v_expr_2382_);
lean_dec(v___x_2334_);
lean_dec_ref(v___x_2326_);
lean_dec_ref(v_arg_2325_);
lean_dec_ref(v_arg_2322_);
lean_dec_ref(v_arg_2319_);
lean_dec_ref(v_arg_2316_);
lean_dec_ref(v_arg_2313_);
v_a_2431_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2433_ = v___x_2400_;
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2400_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
if (v_isShared_2434_ == 0)
{
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_a_2431_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
else
{
lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2446_; 
lean_del_object(v___x_2396_);
lean_dec(v_a_2394_);
lean_dec(v_a_2385_);
lean_dec_ref(v_expr_2382_);
lean_dec(v___x_2334_);
lean_dec_ref(v___x_2326_);
lean_dec_ref(v_arg_2325_);
lean_dec_ref(v_arg_2322_);
lean_dec_ref(v_arg_2319_);
lean_dec_ref(v_arg_2316_);
lean_dec_ref(v_arg_2313_);
v_a_2439_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2441_ = v___x_2398_;
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___x_2398_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2439_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
}
}
else
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2451_; 
lean_dec(v_a_2390_);
lean_dec(v_a_2385_);
lean_dec_ref(v_expr_2382_);
lean_dec(v___x_2334_);
lean_dec_ref(v___x_2326_);
lean_dec_ref(v_arg_2325_);
lean_dec_ref(v_arg_2322_);
lean_dec_ref(v_arg_2319_);
lean_dec_ref(v_arg_2316_);
lean_dec_ref(v_arg_2313_);
v___x_2448_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2448_, 0, v_e_2292_);
lean_ctor_set(v___x_2448_, 1, v___x_2388_);
lean_ctor_set_uint8(v___x_2448_, sizeof(void*)*2, v___x_2328_);
v___x_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2448_);
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 0, v___x_2449_);
v___x_2451_ = v___x_2392_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2449_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
else
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2461_; 
lean_dec(v_a_2385_);
lean_dec_ref(v_expr_2382_);
lean_dec(v___x_2334_);
lean_dec_ref(v___x_2326_);
lean_dec_ref(v_arg_2325_);
lean_dec_ref(v_arg_2322_);
lean_dec_ref(v_arg_2319_);
lean_dec_ref(v_arg_2316_);
lean_dec_ref(v_arg_2313_);
lean_dec_ref(v_e_2292_);
v_a_2454_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2456_ = v___x_2389_;
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2389_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2459_; 
if (v_isShared_2457_ == 0)
{
v___x_2459_ = v___x_2456_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_a_2454_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_dec_ref(v_expr_2382_);
lean_dec(v___x_2334_);
lean_dec_ref(v___x_2326_);
lean_dec_ref(v_arg_2325_);
lean_dec_ref(v_arg_2322_);
lean_dec_ref(v_arg_2319_);
lean_dec_ref(v_arg_2316_);
lean_dec_ref(v_arg_2313_);
lean_dec_ref(v_e_2292_);
v_a_2462_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2384_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2384_);
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
lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2481_; 
lean_dec(v___x_2334_);
lean_dec_ref(v___x_2326_);
lean_dec_ref(v_arg_2325_);
lean_dec_ref(v_arg_2322_);
lean_dec_ref(v_arg_2319_);
lean_dec_ref(v_arg_2316_);
lean_dec_ref(v_arg_2313_);
v_isSharedCheck_2481_ = !lean_is_exclusive(v_a_2378_);
if (v_isSharedCheck_2481_ == 0)
{
lean_object* v_unused_2482_; lean_object* v_unused_2483_; 
v_unused_2482_ = lean_ctor_get(v_a_2378_, 1);
lean_dec(v_unused_2482_);
v_unused_2483_ = lean_ctor_get(v_a_2378_, 0);
lean_dec(v_unused_2483_);
v___x_2471_ = v_a_2378_;
v_isShared_2472_ = v_isSharedCheck_2481_;
goto v_resetjp_2470_;
}
else
{
lean_dec(v_a_2378_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2481_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2473_; lean_object* v___x_2475_; 
v___x_2473_ = lean_box(0);
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 1, v___x_2473_);
lean_ctor_set(v___x_2471_, 0, v_e_2292_);
v___x_2475_ = v___x_2471_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_e_2292_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v___x_2473_);
v___x_2475_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
lean_object* v___x_2476_; lean_object* v___x_2478_; 
lean_ctor_set_uint8(v___x_2475_, sizeof(void*)*2, v___x_2328_);
v___x_2476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 0, v___x_2476_);
v___x_2478_ = v___x_2380_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2476_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
}
}
else
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
lean_dec(v___x_2334_);
lean_dec_ref(v___x_2326_);
lean_dec_ref(v_arg_2325_);
lean_dec_ref(v_arg_2322_);
lean_dec_ref(v_arg_2319_);
lean_dec_ref(v_arg_2316_);
lean_dec_ref(v_arg_2313_);
lean_dec_ref(v_e_2292_);
v_a_2485_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2377_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2377_);
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
}
}
else
{
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
lean_dec(v___x_2334_);
lean_dec_ref(v___x_2326_);
lean_dec_ref(v_arg_2325_);
lean_dec_ref(v_arg_2322_);
lean_dec_ref(v_arg_2319_);
lean_dec_ref(v_arg_2316_);
lean_dec_ref(v_arg_2313_);
lean_dec_ref(v_e_2292_);
v_a_2494_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___x_2354_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2354_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2499_; 
if (v_isShared_2497_ == 0)
{
v___x_2499_ = v___x_2496_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
}
}
}
else
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2510_; 
lean_dec_ref(v___x_2326_);
lean_dec_ref(v_arg_2325_);
lean_dec_ref(v_arg_2322_);
lean_dec_ref(v_arg_2319_);
lean_dec_ref(v_arg_2316_);
lean_dec_ref(v_arg_2313_);
lean_dec_ref(v_e_2292_);
v_a_2503_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2505_ = v___x_2329_;
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___x_2329_);
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
}
}
}
v___jp_2306_:
{
lean_object* v___x_2307_; lean_object* v___x_2309_; 
v___x_2307_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__0));
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 0, v___x_2307_);
v___x_2309_ = v___x_2304_;
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
else
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2519_; 
lean_dec_ref(v_e_2292_);
v_a_2512_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2514_ = v___x_2301_;
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2301_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___boxed(lean_object* v_numIndices_2520_, lean_object* v_useDecideBool_2521_, lean_object* v_e_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_){
_start:
{
uint8_t v_useDecideBool_boxed_2531_; lean_object* v_res_2532_; 
v_useDecideBool_boxed_2531_ = lean_unbox(v_useDecideBool_2521_);
v_res_2532_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27(v_numIndices_2520_, v_useDecideBool_boxed_2531_, v_e_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
lean_dec(v_a_2529_);
lean_dec_ref(v_a_2528_);
lean_dec(v_a_2527_);
lean_dec_ref(v_a_2526_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
lean_dec(v_a_2523_);
lean_dec(v_numIndices_2520_);
return v_res_2532_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0(void){
_start:
{
lean_object* v___x_2533_; 
v___x_2533_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_2533_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1(void){
_start:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v_s_2536_; 
v___x_2534_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__2, &l_Lean_Meta_SplitIf_getSimpContext___closed__2_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__2);
v___x_2535_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0);
v_s_2536_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_s_2536_, 0, v___x_2535_);
lean_ctor_set(v_s_2536_, 1, v___x_2535_);
lean_ctor_set(v_s_2536_, 2, v___x_2534_);
lean_ctor_set(v_s_2536_, 3, v___x_2534_);
return v_s_2536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(lean_object* v_numIndices_2600_, uint8_t v_useDecide_2601_){
_start:
{
lean_object* v_s_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; uint8_t v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v_s_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v_s_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v_s_2603_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1);
v___x_2604_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__3));
v___x_2605_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__16));
v___x_2606_ = 0;
v___x_2607_ = lean_box(v_useDecide_2601_);
lean_inc(v_numIndices_2600_);
v___x_2608_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___boxed), 11, 2);
lean_closure_set(v___x_2608_, 0, v_numIndices_2600_);
lean_closure_set(v___x_2608_, 1, v___x_2607_);
v___x_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2608_);
v_s_2610_ = l_Lean_Meta_Simp_Simprocs_addCore(v_s_2603_, v___x_2604_, v___x_2605_, v___x_2606_, v___x_2609_);
v___x_2611_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__18));
v___x_2612_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__20));
v___x_2613_ = lean_box(v_useDecide_2601_);
v___x_2614_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___boxed), 11, 2);
lean_closure_set(v___x_2614_, 0, v_numIndices_2600_);
lean_closure_set(v___x_2614_, 1, v___x_2613_);
v___x_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2614_);
v_s_2616_ = l_Lean_Meta_Simp_Simprocs_addCore(v_s_2610_, v___x_2611_, v___x_2612_, v___x_2606_, v___x_2615_);
v___x_2617_ = lean_unsigned_to_nat(1u);
v___x_2618_ = lean_mk_empty_array_with_capacity(v___x_2617_);
v___x_2619_ = lean_array_push(v___x_2618_, v_s_2616_);
v___x_2620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2619_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___boxed(lean_object* v_numIndices_2621_, lean_object* v_useDecide_2622_, lean_object* v_a_2623_){
_start:
{
uint8_t v_useDecide_boxed_2624_; lean_object* v_res_2625_; 
v_useDecide_boxed_2624_ = lean_unbox(v_useDecide_2622_);
v_res_2625_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_numIndices_2621_, v_useDecide_boxed_2624_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs(lean_object* v_numIndices_2626_, uint8_t v_useDecide_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_numIndices_2626_, v_useDecide_2627_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___boxed(lean_object* v_numIndices_2634_, lean_object* v_useDecide_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_){
_start:
{
uint8_t v_useDecide_boxed_2641_; lean_object* v_res_2642_; 
v_useDecide_boxed_2641_ = lean_unbox(v_useDecide_2635_);
v_res_2642_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs(v_numIndices_2634_, v_useDecide_boxed_2641_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_);
lean_dec(v_a_2639_);
lean_dec_ref(v_a_2638_);
lean_dec(v_a_2637_);
lean_dec_ref(v_a_2636_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(uint8_t v_useDecide_2643_, lean_object* v_a_2644_){
_start:
{
lean_object* v_lctx_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v_lctx_2646_ = lean_ctor_get(v_a_2644_, 2);
lean_inc_ref(v_lctx_2646_);
v___x_2647_ = lean_local_ctx_num_indices(v_lctx_2646_);
v___x_2648_ = lean_box(v_useDecide_2643_);
v___x_2649_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___boxed), 11, 2);
lean_closure_set(v___x_2649_, 0, v___x_2647_);
lean_closure_set(v___x_2649_, 1, v___x_2648_);
v___x_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2649_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg___boxed(lean_object* v_useDecide_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_){
_start:
{
uint8_t v_useDecide_boxed_2654_; lean_object* v_res_2655_; 
v_useDecide_boxed_2654_ = lean_unbox(v_useDecide_2651_);
v_res_2655_ = l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(v_useDecide_boxed_2654_, v_a_2652_);
lean_dec_ref(v_a_2652_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f(uint8_t v_useDecide_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(v_useDecide_2656_, v_a_2657_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed(lean_object* v_useDecide_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_){
_start:
{
uint8_t v_useDecide_boxed_2669_; lean_object* v_res_2670_; 
v_useDecide_boxed_2669_ = lean_unbox(v_useDecide_2663_);
v_res_2670_ = l_Lean_Meta_SplitIf_mkDischarge_x3f(v_useDecide_boxed_2669_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_);
lean_dec(v_a_2667_);
lean_dec_ref(v_a_2666_);
lean_dec(v_a_2665_);
lean_dec_ref(v_a_2664_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(lean_object* v_mvarId_2671_, lean_object* v_x_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v___x_2678_; 
v___x_2678_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2671_, v_x_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2681_ = v___x_2678_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2678_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2679_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
else
{
lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
v_a_2687_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2689_ = v___x_2678_;
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_dec(v___x_2678_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2692_; 
if (v_isShared_2690_ == 0)
{
v___x_2692_ = v___x_2689_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_a_2687_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_2695_, lean_object* v_x_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2695_, v_x_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0(lean_object* v_00_u03b1_2703_, lean_object* v_mvarId_2704_, lean_object* v_x_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v___x_2711_; 
v___x_2711_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2704_, v_x_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___boxed(lean_object* v_00_u03b1_2712_, lean_object* v_mvarId_2713_, lean_object* v_x_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0(v_00_u03b1_2712_, v_mvarId_2713_, v_x_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
return v_res_2720_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2722_ = ((lean_object*)(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__0));
v___x_2723_ = l_Lean_stringToMessageData(v___x_2722_);
return v___x_2723_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2725_ = ((lean_object*)(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__2));
v___x_2726_ = l_Lean_stringToMessageData(v___x_2725_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0(lean_object* v_e_2727_, lean_object* v_mvarId_2728_, lean_object* v_hName_x3f_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v___x_2738_; lean_object* v_a_2739_; lean_object* v___x_2740_; 
v___x_2738_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_2727_, v___y_2731_);
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
lean_inc_n(v_a_2739_, 2);
lean_dec_ref(v___x_2738_);
v___x_2740_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(v_a_2739_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v_a_2741_; 
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_a_2741_);
lean_dec_ref_known(v___x_2740_, 1);
if (lean_obj_tag(v_a_2741_) == 1)
{
lean_object* v_val_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2817_; 
lean_dec(v_a_2739_);
v_val_2742_ = lean_ctor_get(v_a_2741_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v_a_2741_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2744_ = v_a_2741_;
v_isShared_2745_ = v_isSharedCheck_2817_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_val_2742_);
lean_dec(v_a_2741_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2817_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v_fst_2746_; lean_object* v_snd_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2816_; 
v_fst_2746_ = lean_ctor_get(v_val_2742_, 0);
v_snd_2747_ = lean_ctor_get(v_val_2742_, 1);
v_isSharedCheck_2816_ = !lean_is_exclusive(v_val_2742_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2749_ = v_val_2742_;
v_isShared_2750_ = v_isSharedCheck_2816_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_snd_2747_);
lean_inc(v_fst_2746_);
lean_dec(v_val_2742_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2816_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v_hName_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; 
if (lean_obj_tag(v_hName_x3f_2729_) == 0)
{
lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2804_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__1));
v___x_2805_ = l_Lean_Core_mkFreshUserName(v___x_2804_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v_a_2806_; 
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2806_);
lean_dec_ref_known(v___x_2805_, 1);
v_hName_2778_ = v_a_2806_;
v___y_2779_ = v___y_2730_;
v___y_2780_ = v___y_2731_;
v___y_2781_ = v___y_2732_;
v___y_2782_ = v___y_2733_;
goto v___jp_2777_;
}
else
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2814_; 
lean_del_object(v___x_2749_);
lean_dec(v_snd_2747_);
lean_dec(v_fst_2746_);
lean_del_object(v___x_2744_);
lean_dec(v_mvarId_2728_);
v_a_2807_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2809_ = v___x_2805_;
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2805_);
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
lean_object* v_val_2815_; 
v_val_2815_ = lean_ctor_get(v_hName_x3f_2729_, 0);
lean_inc(v_val_2815_);
lean_dec_ref_known(v_hName_x3f_2729_, 1);
v_hName_2778_ = v_val_2815_;
v___y_2779_ = v___y_2730_;
v___y_2780_ = v___y_2731_;
v___y_2781_ = v___y_2732_;
v___y_2782_ = v___y_2733_;
goto v___jp_2777_;
}
v___jp_2751_:
{
lean_object* v___x_2757_; 
v___x_2757_ = l_Lean_MVarId_byCasesDec(v_mvarId_2728_, v_fst_2746_, v_snd_2747_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2768_; 
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2760_ = v___x_2757_;
v_isShared_2761_ = v_isSharedCheck_2768_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2757_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2768_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 0, v_a_2758_);
v___x_2763_ = v___x_2744_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2758_);
v___x_2763_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
lean_object* v___x_2765_; 
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v___x_2763_);
v___x_2765_ = v___x_2760_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2763_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
else
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
lean_del_object(v___x_2744_);
v_a_2769_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2757_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2757_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2772_ == 0)
{
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2769_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
v___jp_2777_:
{
lean_object* v_toCold_2783_; lean_object* v_options_2784_; uint8_t v_hasTrace_2785_; 
v_toCold_2783_ = lean_ctor_get(v___y_2781_, 0);
v_options_2784_ = lean_ctor_get(v_toCold_2783_, 2);
v_hasTrace_2785_ = lean_ctor_get_uint8(v_options_2784_, sizeof(void*)*1);
if (v_hasTrace_2785_ == 0)
{
lean_del_object(v___x_2749_);
v___y_2752_ = v_hName_2778_;
v___y_2753_ = v___y_2779_;
v___y_2754_ = v___y_2780_;
v___y_2755_ = v___y_2781_;
v___y_2756_ = v___y_2782_;
goto v___jp_2751_;
}
else
{
lean_object* v_inheritedTraceOptions_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; uint8_t v___x_2789_; 
v_inheritedTraceOptions_2786_ = lean_ctor_get(v_toCold_2783_, 11);
v___x_2787_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9));
v___x_2788_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10);
v___x_2789_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2786_, v_options_2784_, v___x_2788_);
if (v___x_2789_ == 0)
{
lean_del_object(v___x_2749_);
v___y_2752_ = v_hName_2778_;
v___y_2753_ = v___y_2779_;
v___y_2754_ = v___y_2780_;
v___y_2755_ = v___y_2781_;
v___y_2756_ = v___y_2782_;
goto v___jp_2751_;
}
else
{
lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2793_; 
v___x_2790_ = lean_obj_once(&l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1, &l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1_once, _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1);
lean_inc(v_snd_2747_);
v___x_2791_ = l_Lean_MessageData_ofExpr(v_snd_2747_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set_tag(v___x_2749_, 7);
lean_ctor_set(v___x_2749_, 1, v___x_2791_);
lean_ctor_set(v___x_2749_, 0, v___x_2790_);
v___x_2793_ = v___x_2749_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v___x_2790_);
lean_ctor_set(v_reuseFailAlloc_2803_, 1, v___x_2791_);
v___x_2793_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
lean_object* v___x_2794_; 
v___x_2794_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_2787_, v___x_2793_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_dec_ref_known(v___x_2794_, 1);
v___y_2752_ = v_hName_2778_;
v___y_2753_ = v___y_2779_;
v___y_2754_ = v___y_2780_;
v___y_2755_ = v___y_2781_;
v___y_2756_ = v___y_2782_;
goto v___jp_2751_;
}
else
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
lean_dec(v_hName_2778_);
lean_dec(v_snd_2747_);
lean_dec(v_fst_2746_);
lean_del_object(v___x_2744_);
lean_dec(v_mvarId_2728_);
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2794_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2794_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
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
lean_object* v_toCold_2818_; lean_object* v_options_2819_; uint8_t v_hasTrace_2820_; 
lean_dec(v_a_2741_);
lean_dec(v_hName_x3f_2729_);
lean_dec(v_mvarId_2728_);
v_toCold_2818_ = lean_ctor_get(v___y_2732_, 0);
v_options_2819_ = lean_ctor_get(v_toCold_2818_, 2);
v_hasTrace_2820_ = lean_ctor_get_uint8(v_options_2819_, sizeof(void*)*1);
if (v_hasTrace_2820_ == 0)
{
lean_dec(v_a_2739_);
goto v___jp_2735_;
}
else
{
lean_object* v_inheritedTraceOptions_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; uint8_t v___x_2824_; 
v_inheritedTraceOptions_2821_ = lean_ctor_get(v_toCold_2818_, 11);
v___x_2822_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9));
v___x_2823_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10);
v___x_2824_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2821_, v_options_2819_, v___x_2823_);
if (v___x_2824_ == 0)
{
lean_dec(v_a_2739_);
goto v___jp_2735_;
}
else
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2825_ = lean_obj_once(&l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3, &l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3_once, _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3);
v___x_2826_ = l_Lean_indentExpr(v_a_2739_);
v___x_2827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2825_);
lean_ctor_set(v___x_2827_, 1, v___x_2826_);
v___x_2828_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_2822_, v___x_2827_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_dec_ref_known(v___x_2828_, 1);
goto v___jp_2735_;
}
else
{
lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2836_; 
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2831_ = v___x_2828_;
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2828_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2834_; 
if (v_isShared_2832_ == 0)
{
v___x_2834_ = v___x_2831_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
lean_dec(v_a_2739_);
lean_dec(v_hName_x3f_2729_);
lean_dec(v_mvarId_2728_);
v_a_2837_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v___x_2740_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2740_);
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
v___jp_2735_:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2736_ = lean_box(0);
v___x_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2736_);
return v___x_2737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___boxed(lean_object* v_e_2845_, lean_object* v_mvarId_2846_, lean_object* v_hName_x3f_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0(v_e_2845_, v_mvarId_2846_, v_hName_x3f_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f(lean_object* v_mvarId_2854_, lean_object* v_e_2855_, lean_object* v_hName_x3f_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_){
_start:
{
lean_object* v___f_2862_; lean_object* v___x_2863_; 
lean_inc(v_mvarId_2854_);
v___f_2862_ = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2862_, 0, v_e_2855_);
lean_closure_set(v___f_2862_, 1, v_mvarId_2854_);
lean_closure_set(v___f_2862_, 2, v_hName_x3f_2856_);
v___x_2863_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2854_, v___f_2862_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___boxed(lean_object* v_mvarId_2864_, lean_object* v_e_2865_, lean_object* v_hName_x3f_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(v_mvarId_2864_, v_e_2865_, v_hName_x3f_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_);
lean_dec(v_a_2870_);
lean_dec_ref(v_a_2869_);
lean_dec(v_a_2868_);
lean_dec_ref(v_a_2867_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0(lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v_lctx_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v_lctx_2878_ = lean_ctor_get(v___y_2873_, 2);
lean_inc_ref(v_lctx_2878_);
lean_dec_ref(v___y_2873_);
v___x_2879_ = lean_local_ctx_num_indices(v_lctx_2878_);
v___x_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0___boxed(lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
lean_object* v_res_2886_; 
v_res_2886_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0(v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec(v___y_2882_);
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(lean_object* v_mvarId_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_){
_start:
{
lean_object* v___f_2894_; lean_object* v___x_2895_; 
v___f_2894_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___closed__0));
v___x_2895_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2888_, v___f_2894_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___boxed(lean_object* v_mvarId_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(v_mvarId_2896_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_);
lean_dec(v_a_2900_);
lean_dec_ref(v_a_2899_);
lean_dec(v_a_2898_);
lean_dec_ref(v_a_2897_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_simpIfTarget_spec__0(lean_object* v_msg_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
lean_object* v___f_2910_; lean_object* v___x_1604__overap_2911_; lean_object* v___x_2912_; 
v___f_2910_ = ((lean_object*)(l_panic___at___00Lean_Meta_simpIfTarget_spec__0___closed__0));
v___x_1604__overap_2911_ = lean_panic_fn_borrowed(v___f_2910_, v_msg_2904_);
lean_inc(v___y_2908_);
lean_inc_ref(v___y_2907_);
lean_inc(v___y_2906_);
lean_inc_ref(v___y_2905_);
v___x_2912_ = lean_apply_5(v___x_1604__overap_2911_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, lean_box(0));
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_simpIfTarget_spec__0___boxed(lean_object* v_msg_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v_msg_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
return v_res_2919_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(lean_object* v_opts_2920_, lean_object* v_opt_2921_){
_start:
{
lean_object* v_name_2922_; lean_object* v_defValue_2923_; lean_object* v_map_2924_; lean_object* v___x_2925_; 
v_name_2922_ = lean_ctor_get(v_opt_2921_, 0);
v_defValue_2923_ = lean_ctor_get(v_opt_2921_, 1);
v_map_2924_ = lean_ctor_get(v_opts_2920_, 0);
v___x_2925_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2924_, v_name_2922_);
if (lean_obj_tag(v___x_2925_) == 0)
{
uint8_t v___x_2926_; 
v___x_2926_ = lean_unbox(v_defValue_2923_);
return v___x_2926_;
}
else
{
lean_object* v_val_2927_; 
v_val_2927_ = lean_ctor_get(v___x_2925_, 0);
lean_inc(v_val_2927_);
lean_dec_ref_known(v___x_2925_, 1);
if (lean_obj_tag(v_val_2927_) == 1)
{
uint8_t v_v_2928_; 
v_v_2928_ = lean_ctor_get_uint8(v_val_2927_, 0);
lean_dec_ref_known(v_val_2927_, 0);
return v_v_2928_;
}
else
{
uint8_t v___x_2929_; 
lean_dec(v_val_2927_);
v___x_2929_ = lean_unbox(v_defValue_2923_);
return v___x_2929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1___boxed(lean_object* v_opts_2930_, lean_object* v_opt_2931_){
_start:
{
uint8_t v_res_2932_; lean_object* v_r_2933_; 
v_res_2932_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v_opts_2930_, v_opt_2931_);
lean_dec_ref(v_opt_2931_);
lean_dec_ref(v_opts_2930_);
v_r_2933_ = lean_box(v_res_2932_);
return v_r_2933_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__0(void){
_start:
{
lean_object* v___x_2934_; 
v___x_2934_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2934_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__1(void){
_start:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2935_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__0, &l_Lean_Meta_simpIfTarget___closed__0_once, _init_l_Lean_Meta_simpIfTarget___closed__0);
v___x_2936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2935_);
return v___x_2936_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__2(void){
_start:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2937_ = lean_unsigned_to_nat(0u);
v___x_2938_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__1, &l_Lean_Meta_simpIfTarget___closed__1_once, _init_l_Lean_Meta_simpIfTarget___closed__1);
v___x_2939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2938_);
lean_ctor_set(v___x_2939_, 1, v___x_2937_);
return v___x_2939_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__3(void){
_start:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2940_ = lean_unsigned_to_nat(32u);
v___x_2941_ = lean_mk_empty_array_with_capacity(v___x_2940_);
v___x_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
return v___x_2942_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__4(void){
_start:
{
size_t v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2943_ = ((size_t)5ULL);
v___x_2944_ = lean_unsigned_to_nat(0u);
v___x_2945_ = lean_unsigned_to_nat(32u);
v___x_2946_ = lean_mk_empty_array_with_capacity(v___x_2945_);
v___x_2947_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__3, &l_Lean_Meta_simpIfTarget___closed__3_once, _init_l_Lean_Meta_simpIfTarget___closed__3);
v___x_2948_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2948_, 0, v___x_2947_);
lean_ctor_set(v___x_2948_, 1, v___x_2946_);
lean_ctor_set(v___x_2948_, 2, v___x_2944_);
lean_ctor_set(v___x_2948_, 3, v___x_2944_);
lean_ctor_set_usize(v___x_2948_, 4, v___x_2943_);
return v___x_2948_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__5(void){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2949_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__4, &l_Lean_Meta_simpIfTarget___closed__4_once, _init_l_Lean_Meta_simpIfTarget___closed__4);
v___x_2950_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__1, &l_Lean_Meta_simpIfTarget___closed__1_once, _init_l_Lean_Meta_simpIfTarget___closed__1);
v___x_2951_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
lean_ctor_set(v___x_2951_, 1, v___x_2950_);
lean_ctor_set(v___x_2951_, 2, v___x_2950_);
lean_ctor_set(v___x_2951_, 3, v___x_2949_);
return v___x_2951_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__6(void){
_start:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2952_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__5, &l_Lean_Meta_simpIfTarget___closed__5_once, _init_l_Lean_Meta_simpIfTarget___closed__5);
v___x_2953_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__2, &l_Lean_Meta_simpIfTarget___closed__2_once, _init_l_Lean_Meta_simpIfTarget___closed__2);
v___x_2954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
lean_ctor_set(v___x_2954_, 1, v___x_2952_);
return v___x_2954_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__10(void){
_start:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2958_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__9));
v___x_2959_ = lean_unsigned_to_nat(78u);
v___x_2960_ = lean_unsigned_to_nat(289u);
v___x_2961_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__8));
v___x_2962_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_2963_ = l_mkPanicMessageWithDecl(v___x_2962_, v___x_2961_, v___x_2960_, v___x_2959_, v___x_2958_);
return v___x_2963_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__12(void){
_start:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2966_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__9));
v___x_2967_ = lean_unsigned_to_nat(128u);
v___x_2968_ = lean_unsigned_to_nat(293u);
v___x_2969_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__8));
v___x_2970_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_2971_ = l_mkPanicMessageWithDecl(v___x_2970_, v___x_2969_, v___x_2968_, v___x_2967_, v___x_2966_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfTarget(lean_object* v_mvarId_2972_, uint8_t v_useDecide_2973_, uint8_t v_useNewSemantics_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_){
_start:
{
if (v_useNewSemantics_2974_ == 0)
{
lean_object* v_toCold_3027_; lean_object* v_options_3028_; lean_object* v___x_3029_; uint8_t v___x_3030_; 
v_toCold_3027_ = lean_ctor_get(v_a_2977_, 0);
v_options_3028_ = lean_ctor_get(v_toCold_3027_, 2);
v___x_3029_ = l_Lean_Meta_backward_split;
v___x_3030_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v_options_3028_, v___x_3029_);
if (v___x_3030_ == 0)
{
goto v___jp_2980_;
}
else
{
lean_object* v___x_3031_; 
v___x_3031_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v_a_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
lean_inc(v_a_3032_);
lean_dec_ref_known(v___x_3031_, 1);
v___x_3033_ = lean_box(v_useDecide_2973_);
v___x_3034_ = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed), 6, 1);
lean_closure_set(v___x_3034_, 0, v___x_3033_);
lean_inc(v_mvarId_2972_);
v___x_3035_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2972_, v___x_3034_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
lean_inc(v_a_3036_);
lean_dec_ref_known(v___x_3035_, 1);
v___x_3037_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__11));
v___x_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3038_, 0, v_a_3036_);
v___x_3039_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__6, &l_Lean_Meta_simpIfTarget___closed__6_once, _init_l_Lean_Meta_simpIfTarget___closed__6);
v___x_3040_ = l_Lean_Meta_simpTarget(v_mvarId_2972_, v_a_3032_, v___x_3037_, v___x_3038_, v_useNewSemantics_2974_, v___x_3039_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3052_; 
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3043_ = v___x_3040_;
v_isShared_3044_ = v_isSharedCheck_3052_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_3040_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3052_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v_fst_3045_; 
v_fst_3045_ = lean_ctor_get(v_a_3041_, 0);
lean_inc(v_fst_3045_);
lean_dec(v_a_3041_);
if (lean_obj_tag(v_fst_3045_) == 1)
{
lean_object* v_val_3046_; lean_object* v___x_3048_; 
v_val_3046_ = lean_ctor_get(v_fst_3045_, 0);
lean_inc(v_val_3046_);
lean_dec_ref_known(v_fst_3045_, 1);
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 0, v_val_3046_);
v___x_3048_ = v___x_3043_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_val_3046_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
else
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
lean_dec(v_fst_3045_);
lean_del_object(v___x_3043_);
v___x_3050_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__12, &l_Lean_Meta_simpIfTarget___closed__12_once, _init_l_Lean_Meta_simpIfTarget___closed__12);
v___x_3051_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3050_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_);
return v___x_3051_;
}
}
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
v_a_3053_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_3040_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_3040_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3053_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
lean_dec(v_a_3032_);
lean_dec(v_mvarId_2972_);
v_a_3061_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3035_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3035_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
else
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
lean_dec(v_mvarId_2972_);
v_a_3069_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_3031_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3031_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3069_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
}
}
else
{
goto v___jp_2980_;
}
v___jp_2980_:
{
lean_object* v___x_2981_; 
v___x_2981_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_2975_, v_a_2977_, v_a_2978_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v_a_2982_; lean_object* v___x_2983_; 
v_a_2982_ = lean_ctor_get(v___x_2981_, 0);
lean_inc(v_a_2982_);
lean_dec_ref_known(v___x_2981_, 1);
lean_inc(v_mvarId_2972_);
v___x_2983_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(v_mvarId_2972_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v_a_2984_; lean_object* v___x_2985_; lean_object* v_a_2986_; lean_object* v___x_2987_; uint8_t v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_a_2984_);
lean_dec_ref_known(v___x_2983_, 1);
v___x_2985_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_a_2984_, v_useDecide_2973_);
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
lean_inc(v_a_2986_);
lean_dec_ref(v___x_2985_);
v___x_2987_ = lean_box(0);
v___x_2988_ = 0;
v___x_2989_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__6, &l_Lean_Meta_simpIfTarget___closed__6_once, _init_l_Lean_Meta_simpIfTarget___closed__6);
v___x_2990_ = l_Lean_Meta_simpTarget(v_mvarId_2972_, v_a_2982_, v_a_2986_, v___x_2987_, v___x_2988_, v___x_2989_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3002_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2993_ = v___x_2990_;
v_isShared_2994_ = v_isSharedCheck_3002_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2990_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3002_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v_fst_2995_; 
v_fst_2995_ = lean_ctor_get(v_a_2991_, 0);
lean_inc(v_fst_2995_);
lean_dec(v_a_2991_);
if (lean_obj_tag(v_fst_2995_) == 1)
{
lean_object* v_val_2996_; lean_object* v___x_2998_; 
v_val_2996_ = lean_ctor_get(v_fst_2995_, 0);
lean_inc(v_val_2996_);
lean_dec_ref_known(v_fst_2995_, 1);
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 0, v_val_2996_);
v___x_2998_ = v___x_2993_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_val_2996_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
else
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
lean_dec(v_fst_2995_);
lean_del_object(v___x_2993_);
v___x_3000_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__10, &l_Lean_Meta_simpIfTarget___closed__10_once, _init_l_Lean_Meta_simpIfTarget___closed__10);
v___x_3001_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3000_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_);
return v___x_3001_;
}
}
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
v_a_3003_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2990_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2990_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
else
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3018_; 
lean_dec(v_a_2982_);
lean_dec(v_mvarId_2972_);
v_a_3011_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3013_ = v___x_2983_;
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_2983_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3016_; 
if (v_isShared_3014_ == 0)
{
v___x_3016_ = v___x_3013_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3011_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_dec(v_mvarId_2972_);
v_a_3019_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_2981_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_2981_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfTarget___boxed(lean_object* v_mvarId_3077_, lean_object* v_useDecide_3078_, lean_object* v_useNewSemantics_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_){
_start:
{
uint8_t v_useDecide_boxed_3085_; uint8_t v_useNewSemantics_boxed_3086_; lean_object* v_res_3087_; 
v_useDecide_boxed_3085_ = lean_unbox(v_useDecide_3078_);
v_useNewSemantics_boxed_3086_ = lean_unbox(v_useNewSemantics_3079_);
v_res_3087_ = l_Lean_Meta_simpIfTarget(v_mvarId_3077_, v_useDecide_boxed_3085_, v_useNewSemantics_boxed_3086_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_);
lean_dec(v_a_3083_);
lean_dec_ref(v_a_3082_);
lean_dec(v_a_3081_);
lean_dec_ref(v_a_3080_);
return v_res_3087_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfLocalDecl___closed__1(void){
_start:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3089_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__9));
v___x_3090_ = lean_unsigned_to_nat(93u);
v___x_3091_ = lean_unsigned_to_nat(305u);
v___x_3092_ = ((lean_object*)(l_Lean_Meta_simpIfLocalDecl___closed__0));
v___x_3093_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_3094_ = l_mkPanicMessageWithDecl(v___x_3093_, v___x_3092_, v___x_3091_, v___x_3090_, v___x_3089_);
return v___x_3094_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfLocalDecl___closed__2(void){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3095_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__9));
v___x_3096_ = lean_unsigned_to_nat(133u);
v___x_3097_ = lean_unsigned_to_nat(309u);
v___x_3098_ = ((lean_object*)(l_Lean_Meta_simpIfLocalDecl___closed__0));
v___x_3099_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_3100_ = l_mkPanicMessageWithDecl(v___x_3099_, v___x_3098_, v___x_3097_, v___x_3096_, v___x_3095_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfLocalDecl(lean_object* v_mvarId_3101_, lean_object* v_fvarId_3102_, uint8_t v_useNewSemantics_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_){
_start:
{
if (v_useNewSemantics_3103_ == 0)
{
lean_object* v_toCold_3157_; lean_object* v_options_3158_; lean_object* v___x_3159_; uint8_t v___x_3160_; 
v_toCold_3157_ = lean_ctor_get(v_a_3106_, 0);
v_options_3158_ = lean_ctor_get(v_toCold_3157_, 2);
v___x_3159_ = l_Lean_Meta_backward_split;
v___x_3160_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v_options_3158_, v___x_3159_);
if (v___x_3160_ == 0)
{
goto v___jp_3109_;
}
else
{
lean_object* v___x_3161_; 
v___x_3161_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v_a_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v_a_3162_ = lean_ctor_get(v___x_3161_, 0);
lean_inc(v_a_3162_);
lean_dec_ref_known(v___x_3161_, 1);
v___x_3163_ = lean_box(v_useNewSemantics_3103_);
v___x_3164_ = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed), 6, 1);
lean_closure_set(v___x_3164_, 0, v___x_3163_);
lean_inc(v_mvarId_3101_);
v___x_3165_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_3101_, v___x_3164_, v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_);
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_object* v_a_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v_a_3166_ = lean_ctor_get(v___x_3165_, 0);
lean_inc(v_a_3166_);
lean_dec_ref_known(v___x_3165_, 1);
v___x_3167_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__11));
v___x_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3168_, 0, v_a_3166_);
v___x_3169_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__6, &l_Lean_Meta_simpIfTarget___closed__6_once, _init_l_Lean_Meta_simpIfTarget___closed__6);
v___x_3170_ = l_Lean_Meta_simpLocalDecl(v_mvarId_3101_, v_fvarId_3102_, v_a_3162_, v___x_3167_, v___x_3168_, v_useNewSemantics_3103_, v___x_3169_, v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_);
if (lean_obj_tag(v___x_3170_) == 0)
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3183_; 
v_a_3171_ = lean_ctor_get(v___x_3170_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3170_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3173_ = v___x_3170_;
v_isShared_3174_ = v_isSharedCheck_3183_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_3170_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3183_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v_fst_3175_; 
v_fst_3175_ = lean_ctor_get(v_a_3171_, 0);
lean_inc(v_fst_3175_);
lean_dec(v_a_3171_);
if (lean_obj_tag(v_fst_3175_) == 1)
{
lean_object* v_val_3176_; lean_object* v_snd_3177_; lean_object* v___x_3179_; 
v_val_3176_ = lean_ctor_get(v_fst_3175_, 0);
lean_inc(v_val_3176_);
lean_dec_ref_known(v_fst_3175_, 1);
v_snd_3177_ = lean_ctor_get(v_val_3176_, 1);
lean_inc(v_snd_3177_);
lean_dec(v_val_3176_);
if (v_isShared_3174_ == 0)
{
lean_ctor_set(v___x_3173_, 0, v_snd_3177_);
v___x_3179_ = v___x_3173_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_snd_3177_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
else
{
lean_object* v___x_3181_; lean_object* v___x_3182_; 
lean_dec(v_fst_3175_);
lean_del_object(v___x_3173_);
v___x_3181_ = lean_obj_once(&l_Lean_Meta_simpIfLocalDecl___closed__2, &l_Lean_Meta_simpIfLocalDecl___closed__2_once, _init_l_Lean_Meta_simpIfLocalDecl___closed__2);
v___x_3182_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3181_, v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_);
return v___x_3182_;
}
}
}
else
{
lean_object* v_a_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3191_; 
v_a_3184_ = lean_ctor_get(v___x_3170_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3170_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3186_ = v___x_3170_;
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_a_3184_);
lean_dec(v___x_3170_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3189_; 
if (v_isShared_3187_ == 0)
{
v___x_3189_ = v___x_3186_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_a_3184_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
}
else
{
lean_object* v_a_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3199_; 
lean_dec(v_a_3162_);
lean_dec(v_fvarId_3102_);
lean_dec(v_mvarId_3101_);
v_a_3192_ = lean_ctor_get(v___x_3165_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3165_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3194_ = v___x_3165_;
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_a_3192_);
lean_dec(v___x_3165_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3197_; 
if (v_isShared_3195_ == 0)
{
v___x_3197_ = v___x_3194_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3192_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
else
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
lean_dec(v_fvarId_3102_);
lean_dec(v_mvarId_3101_);
v_a_3200_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___x_3161_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3161_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
if (v_isShared_3203_ == 0)
{
v___x_3205_ = v___x_3202_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
}
else
{
goto v___jp_3109_;
}
v___jp_3109_:
{
lean_object* v___x_3110_; 
v___x_3110_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_3104_, v_a_3106_, v_a_3107_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v_a_3111_; lean_object* v___x_3112_; 
v_a_3111_ = lean_ctor_get(v___x_3110_, 0);
lean_inc(v_a_3111_);
lean_dec_ref_known(v___x_3110_, 1);
lean_inc(v_mvarId_3101_);
v___x_3112_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(v_mvarId_3101_, v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3113_; uint8_t v___x_3114_; lean_object* v___x_3115_; lean_object* v_a_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
lean_inc(v_a_3113_);
lean_dec_ref_known(v___x_3112_, 1);
v___x_3114_ = 0;
v___x_3115_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_a_3113_, v___x_3114_);
v_a_3116_ = lean_ctor_get(v___x_3115_, 0);
lean_inc(v_a_3116_);
lean_dec_ref(v___x_3115_);
v___x_3117_ = lean_box(0);
v___x_3118_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__6, &l_Lean_Meta_simpIfTarget___closed__6_once, _init_l_Lean_Meta_simpIfTarget___closed__6);
v___x_3119_ = l_Lean_Meta_simpLocalDecl(v_mvarId_3101_, v_fvarId_3102_, v_a_3111_, v_a_3116_, v___x_3117_, v___x_3114_, v___x_3118_, v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3132_; 
v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3122_ = v___x_3119_;
v_isShared_3123_ = v_isSharedCheck_3132_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3119_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3132_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v_fst_3124_; 
v_fst_3124_ = lean_ctor_get(v_a_3120_, 0);
lean_inc(v_fst_3124_);
lean_dec(v_a_3120_);
if (lean_obj_tag(v_fst_3124_) == 1)
{
lean_object* v_val_3125_; lean_object* v_snd_3126_; lean_object* v___x_3128_; 
v_val_3125_ = lean_ctor_get(v_fst_3124_, 0);
lean_inc(v_val_3125_);
lean_dec_ref_known(v_fst_3124_, 1);
v_snd_3126_ = lean_ctor_get(v_val_3125_, 1);
lean_inc(v_snd_3126_);
lean_dec(v_val_3125_);
if (v_isShared_3123_ == 0)
{
lean_ctor_set(v___x_3122_, 0, v_snd_3126_);
v___x_3128_ = v___x_3122_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_snd_3126_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
else
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
lean_dec(v_fst_3124_);
lean_del_object(v___x_3122_);
v___x_3130_ = lean_obj_once(&l_Lean_Meta_simpIfLocalDecl___closed__1, &l_Lean_Meta_simpIfLocalDecl___closed__1_once, _init_l_Lean_Meta_simpIfLocalDecl___closed__1);
v___x_3131_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3130_, v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_);
return v___x_3131_;
}
}
}
else
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3140_; 
v_a_3133_ = lean_ctor_get(v___x_3119_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3135_ = v___x_3119_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3119_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3136_ == 0)
{
v___x_3138_ = v___x_3135_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_a_3133_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
else
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
lean_dec(v_a_3111_);
lean_dec(v_fvarId_3102_);
lean_dec(v_mvarId_3101_);
v_a_3141_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_3112_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3112_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
}
else
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3156_; 
lean_dec(v_fvarId_3102_);
lean_dec(v_mvarId_3101_);
v_a_3149_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3151_ = v___x_3110_;
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___x_3110_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3152_ == 0)
{
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfLocalDecl___boxed(lean_object* v_mvarId_3208_, lean_object* v_fvarId_3209_, lean_object* v_useNewSemantics_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_){
_start:
{
uint8_t v_useNewSemantics_boxed_3216_; lean_object* v_res_3217_; 
v_useNewSemantics_boxed_3216_ = lean_unbox(v_useNewSemantics_3210_);
v_res_3217_ = l_Lean_Meta_simpIfLocalDecl(v_mvarId_3208_, v_fvarId_3209_, v_useNewSemantics_boxed_3216_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_);
lean_dec(v_a_3214_);
lean_dec_ref(v_a_3213_);
lean_dec(v_a_3212_);
lean_dec_ref(v_a_3211_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(lean_object* v_x_x3f_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
lean_object* v___x_3224_; 
v___x_3224_ = l_Lean_Meta_saveState___redArg(v___y_3220_, v___y_3222_);
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3269_; 
v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3227_ = v___x_3224_;
v_isShared_3228_ = v_isSharedCheck_3269_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___x_3224_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3269_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___y_3230_; uint8_t v___y_3231_; lean_object* v_a_3253_; lean_object* v___x_3256_; 
lean_inc(v___y_3222_);
lean_inc_ref(v___y_3221_);
lean_inc(v___y_3220_);
lean_inc_ref(v___y_3219_);
v___x_3256_ = lean_apply_5(v_x_x3f_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, lean_box(0));
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v_a_3257_; 
v_a_3257_ = lean_ctor_get(v___x_3256_, 0);
lean_inc(v_a_3257_);
if (lean_obj_tag(v_a_3257_) == 0)
{
lean_object* v___x_3258_; 
lean_dec_ref_known(v___x_3256_, 1);
v___x_3258_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3225_, v___y_3220_, v___y_3222_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
lean_del_object(v___x_3227_);
lean_dec(v_a_3225_);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3265_ == 0)
{
lean_object* v_unused_3266_; 
v_unused_3266_ = lean_ctor_get(v___x_3258_, 0);
lean_dec(v_unused_3266_);
v___x_3260_ = v___x_3258_;
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
else
{
lean_dec(v___x_3258_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3263_; 
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 0, v_a_3257_);
v___x_3263_ = v___x_3260_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3257_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
else
{
lean_object* v_a_3267_; 
v_a_3267_ = lean_ctor_get(v___x_3258_, 0);
lean_inc(v_a_3267_);
lean_dec_ref_known(v___x_3258_, 1);
v_a_3253_ = v_a_3267_;
goto v___jp_3252_;
}
}
else
{
lean_dec_ref_known(v_a_3257_, 1);
lean_del_object(v___x_3227_);
lean_dec(v_a_3225_);
return v___x_3256_;
}
}
else
{
lean_object* v_a_3268_; 
v_a_3268_ = lean_ctor_get(v___x_3256_, 0);
lean_inc(v_a_3268_);
lean_dec_ref_known(v___x_3256_, 1);
v_a_3253_ = v_a_3268_;
goto v___jp_3252_;
}
v___jp_3229_:
{
if (v___y_3231_ == 0)
{
lean_object* v___x_3232_; 
lean_del_object(v___x_3227_);
v___x_3232_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3225_, v___y_3220_, v___y_3222_);
lean_dec(v_a_3225_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3239_; 
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3239_ == 0)
{
lean_object* v_unused_3240_; 
v_unused_3240_ = lean_ctor_get(v___x_3232_, 0);
lean_dec(v_unused_3240_);
v___x_3234_ = v___x_3232_;
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
else
{
lean_dec(v___x_3232_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3237_; 
if (v_isShared_3235_ == 0)
{
lean_ctor_set_tag(v___x_3234_, 1);
lean_ctor_set(v___x_3234_, 0, v___y_3230_);
v___x_3237_ = v___x_3234_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___y_3230_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
else
{
lean_object* v_a_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3248_; 
lean_dec_ref(v___y_3230_);
v_a_3241_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3243_ = v___x_3232_;
v_isShared_3244_ = v_isSharedCheck_3248_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_a_3241_);
lean_dec(v___x_3232_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3248_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v___x_3246_; 
if (v_isShared_3244_ == 0)
{
v___x_3246_ = v___x_3243_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_a_3241_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
}
}
else
{
lean_object* v___x_3250_; 
lean_dec(v_a_3225_);
if (v_isShared_3228_ == 0)
{
lean_ctor_set_tag(v___x_3227_, 1);
lean_ctor_set(v___x_3227_, 0, v___y_3230_);
v___x_3250_ = v___x_3227_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___y_3230_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
v___jp_3252_:
{
uint8_t v___x_3254_; 
v___x_3254_ = l_Lean_Exception_isInterrupt(v_a_3253_);
if (v___x_3254_ == 0)
{
uint8_t v___x_3255_; 
lean_inc_ref(v_a_3253_);
v___x_3255_ = l_Lean_Exception_isRuntime(v_a_3253_);
v___y_3230_ = v_a_3253_;
v___y_3231_ = v___x_3255_;
goto v___jp_3229_;
}
else
{
v___y_3230_ = v_a_3253_;
v___y_3231_ = v___x_3254_;
goto v___jp_3229_;
}
}
}
}
else
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3277_; 
lean_dec_ref(v_x_x3f_3218_);
v_a_3270_ = lean_ctor_get(v___x_3224_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3272_ = v___x_3224_;
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3224_);
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
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg___boxed(lean_object* v_x_x3f_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v_x_x3f_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0(lean_object* v_00_u03b1_3285_, lean_object* v_x_x3f_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_){
_start:
{
lean_object* v___x_3292_; 
v___x_3292_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v_x_x3f_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___boxed(lean_object* v_00_u03b1_3293_, lean_object* v_x_x3f_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0(v_00_u03b1_3293_, v_x_x3f_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
return v_res_3300_;
}
}
static lean_object* _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3305_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1));
v___x_3306_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4));
v___x_3307_ = l_Lean_Name_append(v___x_3306_, v___x_3305_);
return v___x_3307_;
}
}
static lean_object* _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3309_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__3));
v___x_3310_ = l_Lean_stringToMessageData(v___x_3309_);
return v___x_3310_;
}
}
static lean_object* _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3312_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__5));
v___x_3313_ = l_Lean_stringToMessageData(v___x_3312_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0(lean_object* v_mvarId_3314_, lean_object* v_hName_x3f_3315_, uint8_t v_useNewSemantics_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_){
_start:
{
lean_object* v___x_3325_; 
lean_inc(v_mvarId_3314_);
v___x_3325_ = l_Lean_MVarId_getType(v_mvarId_3314_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
if (lean_obj_tag(v___x_3325_) == 0)
{
lean_object* v_a_3326_; lean_object* v___x_3327_; 
v_a_3326_ = lean_ctor_get(v___x_3325_, 0);
lean_inc(v_a_3326_);
lean_dec_ref_known(v___x_3325_, 1);
v___x_3327_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(v_mvarId_3314_, v_a_3326_, v_hName_x3f_3315_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v_a_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3425_; 
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3330_ = v___x_3327_;
v_isShared_3331_ = v_isSharedCheck_3425_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_a_3328_);
lean_dec(v___x_3327_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3425_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
if (lean_obj_tag(v_a_3328_) == 1)
{
lean_object* v_val_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3420_; 
lean_del_object(v___x_3330_);
v_val_3332_ = lean_ctor_get(v_a_3328_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v_a_3328_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3334_ = v_a_3328_;
v_isShared_3335_ = v_isSharedCheck_3420_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_val_3332_);
lean_dec(v_a_3328_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3420_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v_fst_3336_; lean_object* v_snd_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3419_; 
v_fst_3336_ = lean_ctor_get(v_val_3332_, 0);
v_snd_3337_ = lean_ctor_get(v_val_3332_, 1);
v_isSharedCheck_3419_ = !lean_is_exclusive(v_val_3332_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3339_ = v_val_3332_;
v_isShared_3340_ = v_isSharedCheck_3419_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_snd_3337_);
lean_inc(v_fst_3336_);
lean_dec(v_val_3332_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3419_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v_mvarId_3341_; lean_object* v_fvarId_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3418_; 
v_mvarId_3341_ = lean_ctor_get(v_fst_3336_, 0);
v_fvarId_3342_ = lean_ctor_get(v_fst_3336_, 1);
v_isSharedCheck_3418_ = !lean_is_exclusive(v_fst_3336_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3344_ = v_fst_3336_;
v_isShared_3345_ = v_isSharedCheck_3418_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_fvarId_3342_);
lean_inc(v_mvarId_3341_);
lean_dec(v_fst_3336_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3418_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
uint8_t v___x_3346_; lean_object* v___x_3347_; 
v___x_3346_ = 0;
lean_inc(v_mvarId_3341_);
v___x_3347_ = l_Lean_Meta_simpIfTarget(v_mvarId_3341_, v___x_3346_, v_useNewSemantics_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3348_; lean_object* v_mvarId_3349_; lean_object* v_fvarId_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3409_; 
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_a_3348_);
lean_dec_ref_known(v___x_3347_, 1);
v_mvarId_3349_ = lean_ctor_get(v_snd_3337_, 0);
v_fvarId_3350_ = lean_ctor_get(v_snd_3337_, 1);
v_isSharedCheck_3409_ = !lean_is_exclusive(v_snd_3337_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3352_ = v_snd_3337_;
v_isShared_3353_ = v_isSharedCheck_3409_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_fvarId_3350_);
lean_inc(v_mvarId_3349_);
lean_dec(v_snd_3337_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3409_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3354_; 
lean_inc(v_mvarId_3349_);
v___x_3354_ = l_Lean_Meta_simpIfTarget(v_mvarId_3349_, v___x_3346_, v_useNewSemantics_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_object* v_a_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3400_; 
v_a_3355_ = lean_ctor_get(v___x_3354_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3354_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3357_ = v___x_3354_;
v_isShared_3358_ = v_isSharedCheck_3400_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_a_3355_);
lean_dec(v___x_3354_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3400_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
uint8_t v___x_3375_; 
v___x_3375_ = l_Lean_instBEqMVarId_beq(v_mvarId_3341_, v_a_3348_);
lean_dec(v_mvarId_3341_);
if (v___x_3375_ == 0)
{
lean_dec(v_mvarId_3349_);
goto v___jp_3359_;
}
else
{
uint8_t v___x_3376_; 
v___x_3376_ = l_Lean_instBEqMVarId_beq(v_mvarId_3349_, v_a_3355_);
lean_dec(v_mvarId_3349_);
if (v___x_3376_ == 0)
{
goto v___jp_3359_;
}
else
{
lean_object* v_toCold_3377_; lean_object* v_options_3378_; uint8_t v_hasTrace_3379_; 
lean_del_object(v___x_3357_);
lean_del_object(v___x_3352_);
lean_dec(v_fvarId_3350_);
lean_del_object(v___x_3344_);
lean_dec(v_fvarId_3342_);
lean_del_object(v___x_3339_);
lean_del_object(v___x_3334_);
v_toCold_3377_ = lean_ctor_get(v___y_3319_, 0);
v_options_3378_ = lean_ctor_get(v_toCold_3377_, 2);
v_hasTrace_3379_ = lean_ctor_get_uint8(v_options_3378_, sizeof(void*)*1);
if (v_hasTrace_3379_ == 0)
{
lean_dec(v_a_3355_);
lean_dec(v_a_3348_);
goto v___jp_3322_;
}
else
{
lean_object* v_inheritedTraceOptions_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; uint8_t v___x_3383_; 
v_inheritedTraceOptions_3380_ = lean_ctor_get(v_toCold_3377_, 11);
v___x_3381_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1));
v___x_3382_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2);
v___x_3383_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3380_, v_options_3378_, v___x_3382_);
if (v___x_3383_ == 0)
{
lean_dec(v_a_3355_);
lean_dec(v_a_3348_);
goto v___jp_3322_;
}
else
{
lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3384_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4);
v___x_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3385_, 0, v_a_3348_);
v___x_3386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3384_);
lean_ctor_set(v___x_3386_, 1, v___x_3385_);
v___x_3387_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6);
v___x_3388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3386_);
lean_ctor_set(v___x_3388_, 1, v___x_3387_);
v___x_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3389_, 0, v_a_3355_);
v___x_3390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3388_);
lean_ctor_set(v___x_3390_, 1, v___x_3389_);
v___x_3391_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_3381_, v___x_3390_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_dec_ref_known(v___x_3391_, 1);
goto v___jp_3322_;
}
else
{
lean_object* v_a_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3399_; 
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3394_ = v___x_3391_;
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_a_3392_);
lean_dec(v___x_3391_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3397_; 
if (v_isShared_3395_ == 0)
{
v___x_3397_ = v___x_3394_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_a_3392_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
}
}
}
}
}
v___jp_3359_:
{
lean_object* v___x_3361_; 
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 1, v_fvarId_3342_);
lean_ctor_set(v___x_3352_, 0, v_a_3348_);
v___x_3361_ = v___x_3352_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_a_3348_);
lean_ctor_set(v_reuseFailAlloc_3374_, 1, v_fvarId_3342_);
v___x_3361_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
lean_object* v___x_3363_; 
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 1, v_fvarId_3350_);
lean_ctor_set(v___x_3344_, 0, v_a_3355_);
v___x_3363_ = v___x_3344_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3355_);
lean_ctor_set(v_reuseFailAlloc_3373_, 1, v_fvarId_3350_);
v___x_3363_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
lean_object* v___x_3365_; 
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 1, v___x_3363_);
lean_ctor_set(v___x_3339_, 0, v___x_3361_);
v___x_3365_ = v___x_3339_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3361_);
lean_ctor_set(v_reuseFailAlloc_3372_, 1, v___x_3363_);
v___x_3365_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
lean_object* v___x_3367_; 
if (v_isShared_3335_ == 0)
{
lean_ctor_set(v___x_3334_, 0, v___x_3365_);
v___x_3367_ = v___x_3334_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v___x_3365_);
v___x_3367_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
lean_object* v___x_3369_; 
if (v_isShared_3358_ == 0)
{
lean_ctor_set(v___x_3357_, 0, v___x_3367_);
v___x_3369_ = v___x_3357_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v___x_3367_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
return v___x_3369_;
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
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3408_; 
lean_del_object(v___x_3352_);
lean_dec(v_fvarId_3350_);
lean_dec(v_mvarId_3349_);
lean_dec(v_a_3348_);
lean_del_object(v___x_3344_);
lean_dec(v_fvarId_3342_);
lean_dec(v_mvarId_3341_);
lean_del_object(v___x_3339_);
lean_del_object(v___x_3334_);
v_a_3401_ = lean_ctor_get(v___x_3354_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3354_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3403_ = v___x_3354_;
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3354_);
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
else
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
lean_del_object(v___x_3344_);
lean_dec(v_fvarId_3342_);
lean_dec(v_mvarId_3341_);
lean_del_object(v___x_3339_);
lean_dec(v_snd_3337_);
lean_del_object(v___x_3334_);
v_a_3410_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v___x_3347_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3347_);
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
}
}
else
{
lean_object* v___x_3421_; lean_object* v___x_3423_; 
lean_dec(v_a_3328_);
v___x_3421_ = lean_box(0);
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 0, v___x_3421_);
v___x_3423_ = v___x_3330_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___x_3421_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
}
else
{
return v___x_3327_;
}
}
else
{
lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3433_; 
lean_dec(v_hName_x3f_3315_);
lean_dec(v_mvarId_3314_);
v_a_3426_ = lean_ctor_get(v___x_3325_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3428_ = v___x_3325_;
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_dec(v___x_3325_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3431_; 
if (v_isShared_3429_ == 0)
{
v___x_3431_ = v___x_3428_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_a_3426_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
v___jp_3322_:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3323_ = lean_box(0);
v___x_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3323_);
return v___x_3324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0___boxed(lean_object* v_mvarId_3434_, lean_object* v_hName_x3f_3435_, lean_object* v_useNewSemantics_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
uint8_t v_useNewSemantics_boxed_3442_; lean_object* v_res_3443_; 
v_useNewSemantics_boxed_3442_ = lean_unbox(v_useNewSemantics_3436_);
v_res_3443_ = l_Lean_Meta_splitIfTarget_x3f___lam__0(v_mvarId_3434_, v_hName_x3f_3435_, v_useNewSemantics_boxed_3442_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f(lean_object* v_mvarId_3444_, lean_object* v_hName_x3f_3445_, uint8_t v_useNewSemantics_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_){
_start:
{
lean_object* v___x_3452_; lean_object* v___f_3453_; lean_object* v___x_3454_; 
v___x_3452_ = lean_box(v_useNewSemantics_3446_);
v___f_3453_ = lean_alloc_closure((void*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3453_, 0, v_mvarId_3444_);
lean_closure_set(v___f_3453_, 1, v_hName_x3f_3445_);
lean_closure_set(v___f_3453_, 2, v___x_3452_);
v___x_3454_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v___f_3453_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
return v___x_3454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___boxed(lean_object* v_mvarId_3455_, lean_object* v_hName_x3f_3456_, lean_object* v_useNewSemantics_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_){
_start:
{
uint8_t v_useNewSemantics_boxed_3463_; lean_object* v_res_3464_; 
v_useNewSemantics_boxed_3463_ = lean_unbox(v_useNewSemantics_3457_);
v_res_3464_ = l_Lean_Meta_splitIfTarget_x3f(v_mvarId_3455_, v_hName_x3f_3456_, v_useNewSemantics_boxed_3463_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
lean_dec(v_a_3461_);
lean_dec_ref(v_a_3460_);
lean_dec(v_a_3459_);
lean_dec_ref(v_a_3458_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___lam__0(lean_object* v___x_3465_, lean_object* v_mvarId_3466_, lean_object* v_hName_x3f_3467_, lean_object* v_fvarId_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_){
_start:
{
lean_object* v___x_3477_; 
lean_inc(v___y_3472_);
lean_inc_ref(v___y_3471_);
lean_inc(v___y_3470_);
lean_inc_ref(v___y_3469_);
v___x_3477_ = lean_infer_type(v___x_3465_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; lean_object* v___x_3479_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3478_);
lean_dec_ref_known(v___x_3477_, 1);
v___x_3479_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(v_mvarId_3466_, v_a_3478_, v_hName_x3f_3467_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_a_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3575_; 
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3482_ = v___x_3479_;
v_isShared_3483_ = v_isSharedCheck_3575_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_a_3480_);
lean_dec(v___x_3479_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3575_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
if (lean_obj_tag(v_a_3480_) == 1)
{
lean_object* v_val_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3570_; 
lean_del_object(v___x_3482_);
v_val_3484_ = lean_ctor_get(v_a_3480_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v_a_3480_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3486_ = v_a_3480_;
v_isShared_3487_ = v_isSharedCheck_3570_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_val_3484_);
lean_dec(v_a_3480_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3570_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v_fst_3488_; lean_object* v_snd_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3569_; 
v_fst_3488_ = lean_ctor_get(v_val_3484_, 0);
v_snd_3489_ = lean_ctor_get(v_val_3484_, 1);
v_isSharedCheck_3569_ = !lean_is_exclusive(v_val_3484_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3491_ = v_val_3484_;
v_isShared_3492_ = v_isSharedCheck_3569_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_snd_3489_);
lean_inc(v_fst_3488_);
lean_dec(v_val_3484_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3569_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v_mvarId_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3567_; 
v_mvarId_3493_ = lean_ctor_get(v_fst_3488_, 0);
v_isSharedCheck_3567_ = !lean_is_exclusive(v_fst_3488_);
if (v_isSharedCheck_3567_ == 0)
{
lean_object* v_unused_3568_; 
v_unused_3568_ = lean_ctor_get(v_fst_3488_, 1);
lean_dec(v_unused_3568_);
v___x_3495_ = v_fst_3488_;
v_isShared_3496_ = v_isSharedCheck_3567_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_mvarId_3493_);
lean_dec(v_fst_3488_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3567_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
uint8_t v___x_3497_; lean_object* v___x_3498_; 
v___x_3497_ = 0;
lean_inc(v_fvarId_3468_);
lean_inc(v_mvarId_3493_);
v___x_3498_ = l_Lean_Meta_simpIfLocalDecl(v_mvarId_3493_, v_fvarId_3468_, v___x_3497_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_a_3499_; lean_object* v_mvarId_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3557_; 
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
lean_inc(v_a_3499_);
lean_dec_ref_known(v___x_3498_, 1);
v_mvarId_3500_ = lean_ctor_get(v_snd_3489_, 0);
v_isSharedCheck_3557_ = !lean_is_exclusive(v_snd_3489_);
if (v_isSharedCheck_3557_ == 0)
{
lean_object* v_unused_3558_; 
v_unused_3558_ = lean_ctor_get(v_snd_3489_, 1);
lean_dec(v_unused_3558_);
v___x_3502_ = v_snd_3489_;
v_isShared_3503_ = v_isSharedCheck_3557_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_mvarId_3500_);
lean_dec(v_snd_3489_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3557_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3504_; 
lean_inc(v_mvarId_3500_);
v___x_3504_ = l_Lean_Meta_simpIfLocalDecl(v_mvarId_3500_, v_fvarId_3468_, v___x_3497_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_);
if (lean_obj_tag(v___x_3504_) == 0)
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3548_; 
v_a_3505_ = lean_ctor_get(v___x_3504_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3504_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3507_ = v___x_3504_;
v_isShared_3508_ = v_isSharedCheck_3548_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3504_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3548_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
uint8_t v___x_3519_; 
v___x_3519_ = l_Lean_instBEqMVarId_beq(v_mvarId_3493_, v_a_3499_);
lean_dec(v_mvarId_3493_);
if (v___x_3519_ == 0)
{
lean_del_object(v___x_3502_);
lean_dec(v_mvarId_3500_);
lean_del_object(v___x_3495_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
goto v___jp_3509_;
}
else
{
uint8_t v___x_3520_; 
v___x_3520_ = l_Lean_instBEqMVarId_beq(v_mvarId_3500_, v_a_3505_);
lean_dec(v_mvarId_3500_);
if (v___x_3520_ == 0)
{
lean_del_object(v___x_3502_);
lean_del_object(v___x_3495_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
goto v___jp_3509_;
}
else
{
lean_object* v_toCold_3521_; lean_object* v_options_3522_; uint8_t v_hasTrace_3523_; 
lean_del_object(v___x_3507_);
lean_del_object(v___x_3491_);
lean_del_object(v___x_3486_);
v_toCold_3521_ = lean_ctor_get(v___y_3471_, 0);
v_options_3522_ = lean_ctor_get(v_toCold_3521_, 2);
v_hasTrace_3523_ = lean_ctor_get_uint8(v_options_3522_, sizeof(void*)*1);
if (v_hasTrace_3523_ == 0)
{
lean_dec(v_a_3505_);
lean_del_object(v___x_3502_);
lean_dec(v_a_3499_);
lean_del_object(v___x_3495_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
goto v___jp_3474_;
}
else
{
lean_object* v_inheritedTraceOptions_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; uint8_t v___x_3527_; 
v_inheritedTraceOptions_3524_ = lean_ctor_get(v_toCold_3521_, 11);
v___x_3525_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1));
v___x_3526_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2);
v___x_3527_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3524_, v_options_3522_, v___x_3526_);
if (v___x_3527_ == 0)
{
lean_dec(v_a_3505_);
lean_del_object(v___x_3502_);
lean_dec(v_a_3499_);
lean_del_object(v___x_3495_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
goto v___jp_3474_;
}
else
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3531_; 
v___x_3528_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4);
v___x_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3529_, 0, v_a_3499_);
if (v_isShared_3503_ == 0)
{
lean_ctor_set_tag(v___x_3502_, 7);
lean_ctor_set(v___x_3502_, 1, v___x_3529_);
lean_ctor_set(v___x_3502_, 0, v___x_3528_);
v___x_3531_ = v___x_3502_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v___x_3528_);
lean_ctor_set(v_reuseFailAlloc_3547_, 1, v___x_3529_);
v___x_3531_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
lean_object* v___x_3532_; lean_object* v___x_3534_; 
v___x_3532_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6);
if (v_isShared_3496_ == 0)
{
lean_ctor_set_tag(v___x_3495_, 7);
lean_ctor_set(v___x_3495_, 1, v___x_3532_);
lean_ctor_set(v___x_3495_, 0, v___x_3531_);
v___x_3534_ = v___x_3495_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v___x_3531_);
lean_ctor_set(v_reuseFailAlloc_3546_, 1, v___x_3532_);
v___x_3534_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; 
v___x_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3535_, 0, v_a_3505_);
v___x_3536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3534_);
lean_ctor_set(v___x_3536_, 1, v___x_3535_);
v___x_3537_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_3525_, v___x_3536_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
if (lean_obj_tag(v___x_3537_) == 0)
{
lean_dec_ref_known(v___x_3537_, 1);
goto v___jp_3474_;
}
else
{
lean_object* v_a_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3545_; 
v_a_3538_ = lean_ctor_get(v___x_3537_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3537_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3540_ = v___x_3537_;
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_a_3538_);
lean_dec(v___x_3537_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3543_; 
if (v_isShared_3541_ == 0)
{
v___x_3543_ = v___x_3540_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3538_);
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
}
}
}
v___jp_3509_:
{
lean_object* v___x_3511_; 
if (v_isShared_3492_ == 0)
{
lean_ctor_set(v___x_3491_, 1, v_a_3505_);
lean_ctor_set(v___x_3491_, 0, v_a_3499_);
v___x_3511_ = v___x_3491_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_a_3499_);
lean_ctor_set(v_reuseFailAlloc_3518_, 1, v_a_3505_);
v___x_3511_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
lean_object* v___x_3513_; 
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 0, v___x_3511_);
v___x_3513_ = v___x_3486_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3511_);
v___x_3513_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
lean_object* v___x_3515_; 
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 0, v___x_3513_);
v___x_3515_ = v___x_3507_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3513_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
}
}
else
{
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3556_; 
lean_del_object(v___x_3502_);
lean_dec(v_mvarId_3500_);
lean_dec(v_a_3499_);
lean_del_object(v___x_3495_);
lean_dec(v_mvarId_3493_);
lean_del_object(v___x_3491_);
lean_del_object(v___x_3486_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
v_a_3549_ = lean_ctor_get(v___x_3504_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3504_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3551_ = v___x_3504_;
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_3504_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3554_; 
if (v_isShared_3552_ == 0)
{
v___x_3554_ = v___x_3551_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_a_3549_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
}
}
}
}
}
else
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
lean_del_object(v___x_3495_);
lean_dec(v_mvarId_3493_);
lean_del_object(v___x_3491_);
lean_dec(v_snd_3489_);
lean_del_object(v___x_3486_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
lean_dec(v_fvarId_3468_);
v_a_3559_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___x_3498_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3498_);
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
}
}
else
{
lean_object* v___x_3571_; lean_object* v___x_3573_; 
lean_dec(v_a_3480_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
lean_dec(v_fvarId_3468_);
v___x_3571_ = lean_box(0);
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 0, v___x_3571_);
v___x_3573_ = v___x_3482_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v___x_3571_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
}
else
{
lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3583_; 
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
lean_dec(v_fvarId_3468_);
v_a_3576_ = lean_ctor_get(v___x_3479_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3578_ = v___x_3479_;
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___x_3479_);
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
else
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3591_; 
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
lean_dec(v_fvarId_3468_);
lean_dec(v_hName_x3f_3467_);
lean_dec(v_mvarId_3466_);
v_a_3584_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3586_ = v___x_3477_;
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v___x_3477_);
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
v___jp_3474_:
{
lean_object* v___x_3475_; lean_object* v___x_3476_; 
v___x_3475_ = lean_box(0);
v___x_3476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3475_);
return v___x_3476_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___lam__0___boxed(lean_object* v___x_3592_, lean_object* v_mvarId_3593_, lean_object* v_hName_x3f_3594_, lean_object* v_fvarId_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
lean_object* v_res_3601_; 
v_res_3601_ = l_Lean_Meta_splitIfLocalDecl_x3f___lam__0(v___x_3592_, v_mvarId_3593_, v_hName_x3f_3594_, v_fvarId_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
return v_res_3601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f(lean_object* v_mvarId_3602_, lean_object* v_fvarId_3603_, lean_object* v_hName_x3f_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_){
_start:
{
lean_object* v___x_3610_; lean_object* v___f_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
lean_inc(v_fvarId_3603_);
v___x_3610_ = l_Lean_mkFVar(v_fvarId_3603_);
lean_inc(v_mvarId_3602_);
v___f_3611_ = lean_alloc_closure((void*)(l_Lean_Meta_splitIfLocalDecl_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3611_, 0, v___x_3610_);
lean_closure_set(v___f_3611_, 1, v_mvarId_3602_);
lean_closure_set(v___f_3611_, 2, v_hName_x3f_3604_);
lean_closure_set(v___f_3611_, 3, v_fvarId_3603_);
v___x_3612_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3612_, 0, lean_box(0));
lean_closure_set(v___x_3612_, 1, v_mvarId_3602_);
lean_closure_set(v___x_3612_, 2, v___f_3611_);
v___x_3613_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v___x_3612_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_);
return v___x_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___boxed(lean_object* v_mvarId_3614_, lean_object* v_fvarId_3615_, lean_object* v_hName_x3f_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_Lean_Meta_splitIfLocalDecl_x3f(v_mvarId_3614_, v_fvarId_3615_, v_hName_x3f_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_);
lean_dec(v_a_3620_);
lean_dec_ref(v_a_3619_);
lean_dec(v_a_3618_);
lean_dec_ref(v_a_3617_);
return v_res_3622_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; 
v___x_3643_ = lean_unsigned_to_nat(3526097586u);
v___x_3644_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_));
v___x_3645_ = l_Lean_Name_num___override(v___x_3644_, v___x_3643_);
return v___x_3645_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3647_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_));
v___x_3648_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3649_ = l_Lean_Name_str___override(v___x_3648_, v___x_3647_);
return v___x_3649_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3651_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_));
v___x_3652_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3653_ = l_Lean_Name_str___override(v___x_3652_, v___x_3651_);
return v___x_3653_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3654_ = lean_unsigned_to_nat(2u);
v___x_3655_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3656_ = l_Lean_Name_num___override(v___x_3655_, v___x_3654_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3658_; uint8_t v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3658_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9));
v___x_3659_ = 0;
v___x_3660_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3661_ = l_Lean_registerTraceClass(v___x_3658_, v___x_3659_, v___x_3660_);
return v___x_3661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2____boxed(lean_object* v_a_3662_){
_start:
{
lean_object* v_res_3663_; 
v_res_3663_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_();
return v_res_3663_;
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
