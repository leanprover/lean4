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
lean_object* v___x_810_; lean_object* v_env_811_; lean_object* v___x_812_; lean_object* v_mctx_813_; lean_object* v_lctx_814_; lean_object* v_options_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_810_ = lean_st_ref_get(v___y_808_);
v_env_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc_ref(v_env_811_);
lean_dec(v___x_810_);
v___x_812_ = lean_st_ref_get(v___y_806_);
v_mctx_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc_ref(v_mctx_813_);
lean_dec(v___x_812_);
v_lctx_814_ = lean_ctor_get(v___y_805_, 2);
v_options_815_ = lean_ctor_get(v___y_807_, 1);
lean_inc_ref(v_options_815_);
lean_inc_ref(v_lctx_814_);
v___x_816_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_816_, 0, v_env_811_);
lean_ctor_set(v___x_816_, 1, v_mctx_813_);
lean_ctor_set(v___x_816_, 2, v_lctx_814_);
lean_ctor_set(v___x_816_, 3, v_options_815_);
v___x_817_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
lean_ctor_set(v___x_817_, 1, v_msgData_804_);
v___x_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0___boxed(lean_object* v_msgData_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(v_msgData_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
return v_res_825_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_826_; double v___x_827_; 
v___x_826_ = lean_unsigned_to_nat(0u);
v___x_827_ = lean_float_of_nat(v___x_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(lean_object* v_cls_831_, lean_object* v_msg_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_ref_838_; lean_object* v___x_839_; lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_884_; 
v_ref_838_ = lean_ctor_get(v___y_835_, 4);
v___x_839_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(v_msg_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
v_a_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_884_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_884_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_884_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; lean_object* v_traceState_845_; lean_object* v_env_846_; lean_object* v_nextMacroScope_847_; lean_object* v_ngen_848_; lean_object* v_auxDeclNGen_849_; lean_object* v_cache_850_; lean_object* v_messages_851_; lean_object* v_infoState_852_; lean_object* v_snapshotTasks_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_883_; 
v___x_844_ = lean_st_ref_take(v___y_836_);
v_traceState_845_ = lean_ctor_get(v___x_844_, 4);
v_env_846_ = lean_ctor_get(v___x_844_, 0);
v_nextMacroScope_847_ = lean_ctor_get(v___x_844_, 1);
v_ngen_848_ = lean_ctor_get(v___x_844_, 2);
v_auxDeclNGen_849_ = lean_ctor_get(v___x_844_, 3);
v_cache_850_ = lean_ctor_get(v___x_844_, 5);
v_messages_851_ = lean_ctor_get(v___x_844_, 6);
v_infoState_852_ = lean_ctor_get(v___x_844_, 7);
v_snapshotTasks_853_ = lean_ctor_get(v___x_844_, 8);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_883_ == 0)
{
v___x_855_ = v___x_844_;
v_isShared_856_ = v_isSharedCheck_883_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_snapshotTasks_853_);
lean_inc(v_infoState_852_);
lean_inc(v_messages_851_);
lean_inc(v_cache_850_);
lean_inc(v_traceState_845_);
lean_inc(v_auxDeclNGen_849_);
lean_inc(v_ngen_848_);
lean_inc(v_nextMacroScope_847_);
lean_inc(v_env_846_);
lean_dec(v___x_844_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_883_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
uint64_t v_tid_857_; lean_object* v_traces_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_882_; 
v_tid_857_ = lean_ctor_get_uint64(v_traceState_845_, sizeof(void*)*1);
v_traces_858_ = lean_ctor_get(v_traceState_845_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v_traceState_845_);
if (v_isSharedCheck_882_ == 0)
{
v___x_860_ = v_traceState_845_;
v_isShared_861_ = v_isSharedCheck_882_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_traces_858_);
lean_dec(v_traceState_845_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_882_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_862_; double v___x_863_; uint8_t v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_862_ = lean_box(0);
v___x_863_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0);
v___x_864_ = 0;
v___x_865_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__1));
v___x_866_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_866_, 0, v_cls_831_);
lean_ctor_set(v___x_866_, 1, v___x_862_);
lean_ctor_set(v___x_866_, 2, v___x_865_);
lean_ctor_set_float(v___x_866_, sizeof(void*)*3, v___x_863_);
lean_ctor_set_float(v___x_866_, sizeof(void*)*3 + 8, v___x_863_);
lean_ctor_set_uint8(v___x_866_, sizeof(void*)*3 + 16, v___x_864_);
v___x_867_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__2));
v___x_868_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_868_, 0, v___x_866_);
lean_ctor_set(v___x_868_, 1, v_a_840_);
lean_ctor_set(v___x_868_, 2, v___x_867_);
lean_inc(v_ref_838_);
v___x_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_869_, 0, v_ref_838_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = l_Lean_PersistentArray_push___redArg(v_traces_858_, v___x_869_);
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 0, v___x_870_);
v___x_872_ = v___x_860_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_870_);
lean_ctor_set_uint64(v_reuseFailAlloc_881_, sizeof(void*)*1, v_tid_857_);
v___x_872_ = v_reuseFailAlloc_881_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_874_; 
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 4, v___x_872_);
v___x_874_ = v___x_855_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_env_846_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v_nextMacroScope_847_);
lean_ctor_set(v_reuseFailAlloc_880_, 2, v_ngen_848_);
lean_ctor_set(v_reuseFailAlloc_880_, 3, v_auxDeclNGen_849_);
lean_ctor_set(v_reuseFailAlloc_880_, 4, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_880_, 5, v_cache_850_);
lean_ctor_set(v_reuseFailAlloc_880_, 6, v_messages_851_);
lean_ctor_set(v_reuseFailAlloc_880_, 7, v_infoState_852_);
lean_ctor_set(v_reuseFailAlloc_880_, 8, v_snapshotTasks_853_);
v___x_874_ = v_reuseFailAlloc_880_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_875_ = lean_st_ref_put(v___y_836_, v___x_874_);
v___x_876_ = lean_box(0);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_876_);
v___x_878_ = v___x_842_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___boxed(lean_object* v_cls_885_, lean_object* v_msg_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v_cls_885_, v_msg_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
return v_res_892_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_901_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__2));
v___x_902_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4));
v___x_903_ = l_Lean_Name_append(v___x_902_, v___x_901_);
return v___x_903_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__6));
v___x_906_ = l_Lean_stringToMessageData(v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f(uint8_t v_kind_907_, lean_object* v_exceptionSet_908_, lean_object* v_e_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_915_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_915_, 0, v_exceptionSet_908_);
lean_ctor_set_uint8(v___x_915_, sizeof(void*)*1, v_kind_907_);
v___x_916_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0);
v___x_917_ = l_Lean_Meta_FindSplitImpl_visit(v_e_909_, v___x_915_, v___x_916_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
lean_dec_ref_known(v___x_915_, 1);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_965_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_965_ == 0)
{
v___x_920_ = v___x_917_;
v_isShared_921_ = v_isSharedCheck_965_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_917_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_965_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v_fst_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_963_; 
v_fst_922_ = lean_ctor_get(v_a_918_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v_a_918_);
if (v_isSharedCheck_963_ == 0)
{
lean_object* v_unused_964_; 
v_unused_964_ = lean_ctor_get(v_a_918_, 1);
lean_dec(v_unused_964_);
v___x_924_ = v_a_918_;
v_isShared_925_ = v_isSharedCheck_963_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_fst_922_);
lean_dec(v_a_918_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_963_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
if (lean_obj_tag(v_fst_922_) == 1)
{
lean_object* v_options_926_; lean_object* v_val_927_; lean_object* v_toCold_928_; uint8_t v_hasTrace_929_; lean_object* v___x_931_; 
v_options_926_ = lean_ctor_get(v_a_912_, 1);
v_val_927_ = lean_ctor_get(v_fst_922_, 0);
v_toCold_928_ = lean_ctor_get(v_a_912_, 0);
v_hasTrace_929_ = lean_ctor_get_uint8(v_options_926_, sizeof(void*)*1);
lean_inc_ref(v_fst_922_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v_fst_922_);
v___x_931_ = v___x_920_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_fst_922_);
v___x_931_ = v_reuseFailAlloc_958_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
if (v_hasTrace_929_ == 0)
{
lean_dec_ref_known(v_fst_922_, 1);
lean_del_object(v___x_924_);
return v___x_931_;
}
else
{
lean_object* v_inheritedTraceOptions_932_; lean_object* v___x_933_; lean_object* v___x_934_; uint8_t v___x_935_; 
v_inheritedTraceOptions_932_ = lean_ctor_get(v_toCold_928_, 4);
v___x_933_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__2));
v___x_934_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5);
v___x_935_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_932_, v_options_926_, v___x_934_);
if (v___x_935_ == 0)
{
lean_dec_ref_known(v_fst_922_, 1);
lean_del_object(v___x_924_);
return v___x_931_;
}
else
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_939_; 
lean_dec_ref(v___x_931_);
v___x_936_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7);
lean_inc(v_val_927_);
v___x_937_ = l_Lean_indentExpr(v_val_927_);
if (v_isShared_925_ == 0)
{
lean_ctor_set_tag(v___x_924_, 7);
lean_ctor_set(v___x_924_, 1, v___x_937_);
lean_ctor_set(v___x_924_, 0, v___x_936_);
v___x_939_ = v___x_924_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_936_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v___x_937_);
v___x_939_ = v_reuseFailAlloc_957_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_940_; 
v___x_940_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_933_, v___x_939_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_947_ == 0)
{
lean_object* v_unused_948_; 
v_unused_948_ = lean_ctor_get(v___x_940_, 0);
lean_dec(v_unused_948_);
v___x_942_ = v___x_940_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_dec(v___x_940_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v_fst_922_);
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_fst_922_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec_ref_known(v_fst_922_, 1);
v_a_949_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_940_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_940_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
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
lean_object* v___x_959_; lean_object* v___x_961_; 
lean_del_object(v___x_924_);
lean_dec(v_fst_922_);
v___x_959_ = lean_box(0);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v___x_959_);
v___x_961_ = v___x_920_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_959_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
v_a_966_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_917_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_917_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___boxed(lean_object* v_kind_974_, lean_object* v_exceptionSet_975_, lean_object* v_e_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_){
_start:
{
uint8_t v_kind_boxed_982_; lean_object* v_res_983_; 
v_kind_boxed_982_ = lean_unbox(v_kind_974_);
v_res_983_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f(v_kind_boxed_982_, v_exceptionSet_975_, v_e_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(uint8_t v_kind_984_, lean_object* v_exceptionSet_985_, lean_object* v_e_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_){
_start:
{
lean_object* v___y_993_; lean_object* v___x_996_; 
lean_inc_ref(v_exceptionSet_985_);
v___x_996_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f(v_kind_984_, v_exceptionSet_985_, v_e_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_a_997_);
if (lean_obj_tag(v_a_997_) == 1)
{
lean_object* v_val_998_; uint8_t v___y_1000_; uint8_t v___x_1006_; 
v_val_998_ = lean_ctor_get(v_a_997_, 0);
lean_inc(v_val_998_);
lean_dec_ref_known(v_a_997_, 1);
v___x_1006_ = l_Lean_Expr_isIte(v_val_998_);
if (v___x_1006_ == 0)
{
uint8_t v___x_1007_; 
v___x_1007_ = l_Lean_Expr_isDIte(v_val_998_);
v___y_1000_ = v___x_1007_;
goto v___jp_999_;
}
else
{
v___y_1000_ = v___x_1006_;
goto v___jp_999_;
}
v___jp_999_:
{
if (v___y_1000_ == 0)
{
lean_dec(v_val_998_);
lean_dec_ref(v_exceptionSet_985_);
return v___x_996_;
}
else
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_dec_ref_known(v___x_996_, 1);
v___x_1001_ = lean_unsigned_to_nat(3u);
v___x_1002_ = l_Lean_Expr_getRevArg_x21(v_val_998_, v___x_1001_);
v___x_1003_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(v_kind_984_, v_exceptionSet_985_, v___x_1002_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
if (lean_obj_tag(v_a_1004_) == 0)
{
v___y_993_ = v_val_998_;
goto v___jp_992_;
}
else
{
lean_object* v_val_1005_; 
lean_dec(v_val_998_);
v_val_1005_ = lean_ctor_get(v_a_1004_, 0);
lean_inc(v_val_1005_);
lean_dec_ref_known(v_a_1004_, 1);
v___y_993_ = v_val_1005_;
goto v___jp_992_;
}
}
else
{
lean_dec(v_val_998_);
return v___x_1003_;
}
}
}
}
else
{
lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1015_; 
lean_dec(v_a_997_);
lean_dec_ref(v_exceptionSet_985_);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1015_ == 0)
{
lean_object* v_unused_1016_; 
v_unused_1016_ = lean_ctor_get(v___x_996_, 0);
lean_dec(v_unused_1016_);
v___x_1009_ = v___x_996_;
v_isShared_1010_ = v_isSharedCheck_1015_;
goto v_resetjp_1008_;
}
else
{
lean_dec(v___x_996_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1015_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v___x_1013_; 
v___x_1011_ = lean_box(0);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1011_);
v___x_1013_ = v___x_1009_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
else
{
lean_dec_ref(v_exceptionSet_985_);
return v___x_996_;
}
v___jp_992_:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_994_, 0, v___y_993_);
v___x_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go___boxed(lean_object* v_kind_1017_, lean_object* v_exceptionSet_1018_, lean_object* v_e_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
uint8_t v_kind_boxed_1025_; lean_object* v_res_1026_; 
v_kind_boxed_1025_ = lean_unbox(v_kind_1017_);
v_res_1026_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(v_kind_boxed_1025_, v_exceptionSet_1018_, v_e_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
lean_dec(v_a_1023_);
lean_dec_ref(v_a_1022_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(lean_object* v_e_1027_, lean_object* v___y_1028_){
_start:
{
uint8_t v___x_1030_; 
v___x_1030_ = l_Lean_Expr_hasMVar(v_e_1027_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; 
v___x_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1031_, 0, v_e_1027_);
return v___x_1031_;
}
else
{
lean_object* v___x_1032_; lean_object* v_mctx_1033_; lean_object* v___x_1034_; lean_object* v_fst_1035_; lean_object* v_snd_1036_; lean_object* v___x_1037_; lean_object* v_cache_1038_; lean_object* v_zetaDeltaFVarIds_1039_; lean_object* v_postponed_1040_; lean_object* v_diag_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1050_; 
v___x_1032_ = lean_st_ref_get(v___y_1028_);
v_mctx_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc_ref(v_mctx_1033_);
lean_dec(v___x_1032_);
v___x_1034_ = l_Lean_instantiateMVarsCore(v_mctx_1033_, v_e_1027_);
v_fst_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_fst_1035_);
v_snd_1036_ = lean_ctor_get(v___x_1034_, 1);
lean_inc(v_snd_1036_);
lean_dec_ref(v___x_1034_);
v___x_1037_ = lean_st_ref_take(v___y_1028_);
v_cache_1038_ = lean_ctor_get(v___x_1037_, 1);
v_zetaDeltaFVarIds_1039_ = lean_ctor_get(v___x_1037_, 2);
v_postponed_1040_ = lean_ctor_get(v___x_1037_, 3);
v_diag_1041_ = lean_ctor_get(v___x_1037_, 4);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1050_ == 0)
{
lean_object* v_unused_1051_; 
v_unused_1051_ = lean_ctor_get(v___x_1037_, 0);
lean_dec(v_unused_1051_);
v___x_1043_ = v___x_1037_;
v_isShared_1044_ = v_isSharedCheck_1050_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_diag_1041_);
lean_inc(v_postponed_1040_);
lean_inc(v_zetaDeltaFVarIds_1039_);
lean_inc(v_cache_1038_);
lean_dec(v___x_1037_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1050_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 0, v_snd_1036_);
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_snd_1036_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_cache_1038_);
lean_ctor_set(v_reuseFailAlloc_1049_, 2, v_zetaDeltaFVarIds_1039_);
lean_ctor_set(v_reuseFailAlloc_1049_, 3, v_postponed_1040_);
lean_ctor_set(v_reuseFailAlloc_1049_, 4, v_diag_1041_);
v___x_1046_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = lean_st_ref_put(v___y_1028_, v___x_1046_);
v___x_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1048_, 0, v_fst_1035_);
return v___x_1048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg___boxed(lean_object* v_e_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_1052_, v___y_1053_);
lean_dec(v___y_1053_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0(lean_object* v_e_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_1056_, v___y_1058_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___boxed(lean_object* v_e_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0(v_e_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f(lean_object* v_e_1070_, uint8_t v_kind_1071_, lean_object* v_exceptionSet_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v___x_1078_; lean_object* v_a_1079_; lean_object* v___x_1080_; 
v___x_1078_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_1070_, v_a_1074_);
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1079_);
lean_dec_ref(v___x_1078_);
v___x_1080_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(v_kind_1071_, v_exceptionSet_1072_, v_a_1079_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f___boxed(lean_object* v_e_1081_, lean_object* v_kind_1082_, lean_object* v_exceptionSet_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
uint8_t v_kind_boxed_1089_; lean_object* v_res_1090_; 
v_kind_boxed_1089_ = lean_unbox(v_kind_1082_);
v_res_1090_ = l_Lean_Meta_findSplit_x3f(v_e_1081_, v_kind_boxed_1089_, v_exceptionSet_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
lean_dec(v_a_1087_);
lean_dec_ref(v_a_1086_);
lean_dec(v_a_1085_);
lean_dec_ref(v_a_1084_);
return v_res_1090_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = lean_box(0);
v___x_1092_ = lean_unsigned_to_nat(16u);
v___x_1093_ = lean_mk_array(v___x_1092_, v___x_1091_);
return v___x_1093_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1094_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0);
v___x_1095_ = lean_unsigned_to_nat(0u);
v___x_1096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
lean_ctor_set(v___x_1096_, 1, v___x_1094_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(lean_object* v_e_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_){
_start:
{
uint8_t v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1103_ = 0;
v___x_1104_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1);
v___x_1105_ = l_Lean_Meta_findSplit_x3f(v_e_1097_, v___x_1103_, v___x_1104_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1130_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1108_ = v___x_1105_;
v_isShared_1109_ = v_isSharedCheck_1130_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1105_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1130_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
if (lean_obj_tag(v_a_1106_) == 1)
{
lean_object* v_val_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1125_; 
v_val_1110_ = lean_ctor_get(v_a_1106_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_a_1106_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1112_ = v_a_1106_;
v_isShared_1113_ = v_isSharedCheck_1125_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_val_1110_);
lean_dec(v_a_1106_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1125_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1120_; 
v___x_1114_ = lean_unsigned_to_nat(3u);
v___x_1115_ = l_Lean_Expr_getRevArg_x21(v_val_1110_, v___x_1114_);
v___x_1116_ = lean_unsigned_to_nat(2u);
v___x_1117_ = l_Lean_Expr_getRevArg_x21(v_val_1110_, v___x_1116_);
lean_dec(v_val_1110_);
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1115_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v___x_1118_);
v___x_1120_ = v___x_1112_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v___x_1122_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v___x_1120_);
v___x_1122_ = v___x_1108_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
else
{
lean_object* v___x_1126_; lean_object* v___x_1128_; 
lean_dec(v_a_1106_);
v___x_1126_ = lean_box(0);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v___x_1126_);
v___x_1128_ = v___x_1108_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1126_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
v_a_1131_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1105_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1105_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___boxed(lean_object* v_e_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(v_e_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(lean_object* v_name_1146_, lean_object* v_decl_1147_, lean_object* v_ref_1148_){
_start:
{
lean_object* v_defValue_1150_; lean_object* v_descr_1151_; lean_object* v_deprecation_x3f_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v_defValue_1150_ = lean_ctor_get(v_decl_1147_, 0);
v_descr_1151_ = lean_ctor_get(v_decl_1147_, 1);
v_deprecation_x3f_1152_ = lean_ctor_get(v_decl_1147_, 2);
v___x_1153_ = lean_alloc_ctor(1, 0, 1);
v___x_1154_ = lean_unbox(v_defValue_1150_);
lean_ctor_set_uint8(v___x_1153_, 0, v___x_1154_);
lean_inc(v_deprecation_x3f_1152_);
lean_inc_ref(v_descr_1151_);
lean_inc_n(v_name_1146_, 2);
v___x_1155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1155_, 0, v_name_1146_);
lean_ctor_set(v___x_1155_, 1, v_ref_1148_);
lean_ctor_set(v___x_1155_, 2, v___x_1153_);
lean_ctor_set(v___x_1155_, 3, v_descr_1151_);
lean_ctor_set(v___x_1155_, 4, v_deprecation_x3f_1152_);
v___x_1156_ = lean_register_option(v_name_1146_, v___x_1155_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1164_; 
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1164_ == 0)
{
lean_object* v_unused_1165_; 
v_unused_1165_ = lean_ctor_get(v___x_1156_, 0);
lean_dec(v_unused_1165_);
v___x_1158_ = v___x_1156_;
v_isShared_1159_ = v_isSharedCheck_1164_;
goto v_resetjp_1157_;
}
else
{
lean_dec(v___x_1156_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1164_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1160_; lean_object* v___x_1162_; 
lean_inc(v_defValue_1150_);
v___x_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1160_, 0, v_name_1146_);
lean_ctor_set(v___x_1160_, 1, v_defValue_1150_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 0, v___x_1160_);
v___x_1162_ = v___x_1158_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1160_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
lean_dec(v_name_1146_);
v_a_1166_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1156_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1156_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1174_, lean_object* v_decl_1175_, lean_object* v_ref_1176_, lean_object* v_a_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(v_name_1174_, v_decl_1175_, v_ref_1176_);
lean_dec_ref(v_decl_1175_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1197_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_));
v___x_1198_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_));
v___x_1199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_));
v___x_1200_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(v___x_1197_, v___x_1198_, v___x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4____boxed(lean_object* v_a_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_();
return v_res_1202_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1203_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0);
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0(lean_object* v_00_u03b2_1206_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1);
return v___x_1207_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1208_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0);
v___x_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1(lean_object* v_00_u03b2_1211_){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1);
return v___x_1212_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__0(void){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_1213_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__1(void){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0(lean_box(0));
return v___x_1214_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__2(void){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1(lean_box(0));
return v___x_1215_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__3(void){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1216_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__4(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__3, &l_Lean_Meta_SplitIf_getSimpContext___closed__3_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__3);
v___x_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
return v___x_1218_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__5(void){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v_s_1223_; 
v___x_1219_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__4, &l_Lean_Meta_SplitIf_getSimpContext___closed__4_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__4);
v___x_1220_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__2, &l_Lean_Meta_SplitIf_getSimpContext___closed__2_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__2);
v___x_1221_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__1, &l_Lean_Meta_SplitIf_getSimpContext___closed__1_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__1);
v___x_1222_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__0, &l_Lean_Meta_SplitIf_getSimpContext___closed__0_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__0);
v_s_1223_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_s_1223_, 0, v___x_1222_);
lean_ctor_set(v_s_1223_, 1, v___x_1222_);
lean_ctor_set(v_s_1223_, 2, v___x_1221_);
lean_ctor_set(v_s_1223_, 3, v___x_1220_);
lean_ctor_set(v_s_1223_, 4, v___x_1221_);
lean_ctor_set(v_s_1223_, 5, v___x_1219_);
return v_s_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_getSimpContext(lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v_s_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; uint8_t v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v_s_1241_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__5, &l_Lean_Meta_SplitIf_getSimpContext___closed__5_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__5);
v___x_1242_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__7));
v___x_1243_ = 1;
v___x_1244_ = 0;
v___x_1245_ = lean_unsigned_to_nat(1000u);
v___x_1246_ = l_Lean_Meta_SimpTheorems_addConst(v_s_1241_, v___x_1242_, v___x_1243_, v___x_1244_, v___x_1245_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref_known(v___x_1246_, 1);
v___x_1248_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__9));
v___x_1249_ = l_Lean_Meta_SimpTheorems_addConst(v_a_1247_, v___x_1248_, v___x_1243_, v___x_1244_, v___x_1245_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1250_);
lean_dec_ref_known(v___x_1249_, 1);
v___x_1251_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__11));
v___x_1252_ = l_Lean_Meta_SimpTheorems_addConst(v_a_1250_, v___x_1251_, v___x_1243_, v___x_1244_, v___x_1245_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_a_1253_);
lean_dec_ref_known(v___x_1252_, 1);
v___x_1254_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__13));
v___x_1255_ = l_Lean_Meta_SimpTheorems_addConst(v_a_1253_, v___x_1254_, v___x_1243_, v___x_1244_, v___x_1245_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_a_1256_; lean_object* v___x_1257_; 
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_a_1256_);
lean_dec_ref_known(v___x_1255_, 1);
v___x_1257_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_1239_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; lean_object* v___x_1259_; lean_object* v_maxSteps_1260_; lean_object* v_maxDischargeDepth_1261_; uint8_t v_contextual_1262_; uint8_t v_memoize_1263_; uint8_t v_singlePass_1264_; uint8_t v_zeta_1265_; uint8_t v_beta_1266_; uint8_t v_eta_1267_; uint8_t v_etaStruct_1268_; uint8_t v_iota_1269_; uint8_t v_proj_1270_; uint8_t v_decide_1271_; uint8_t v_arith_1272_; uint8_t v_autoUnfold_1273_; uint8_t v_failIfUnchanged_1274_; uint8_t v_ground_1275_; uint8_t v_unfoldPartialApp_1276_; uint8_t v_zetaDelta_1277_; uint8_t v_index_1278_; uint8_t v_implicitDefEqProofs_1279_; uint8_t v_zetaUnused_1280_; uint8_t v_catchRuntime_1281_; uint8_t v_zetaHave_1282_; uint8_t v_congrConsts_1283_; uint8_t v_bitVecOfNat_1284_; uint8_t v_warnExponents_1285_; uint8_t v_suggestions_1286_; lean_object* v_maxSuggestions_1287_; uint8_t v_locals_1288_; uint8_t v_instances_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_a_1258_);
lean_dec_ref_known(v___x_1257_, 1);
v___x_1259_ = l_Lean_Meta_Simp_neutralConfig;
v_maxSteps_1260_ = lean_ctor_get(v___x_1259_, 0);
v_maxDischargeDepth_1261_ = lean_ctor_get(v___x_1259_, 1);
v_contextual_1262_ = lean_ctor_get_uint8(v___x_1259_, sizeof(void*)*3);
v_memoize_1263_ = lean_ctor_get_uint8(v___x_1259_, sizeof(void*)*3 + 1);
v_singlePass_1264_ = lean_ctor_get_uint8(v___x_1259_, sizeof(void*)*3 + 2);
v_zeta_1265_ = lean_ctor_get_uint8(v___x_1259_, sizeof(void*)*3 + 3);
v_beta_1266_ = lean_ctor_get_uint8(v___x_1259_, sizeof(void*)*3 + 4);
v_eta_1267_ = lean_ctor_get_uint8(v___x_1259_, sizeof(void*)*3 + 5);
v_etaStruct_1268_ = lean_ctor_get_uint8(v___x_1259_, sizeof(void*)*3 + 6);
v_iota_1269_ = lean_ctor_get_uint8(v___x_1259_, sizeof(void*)*3 + 7);
v_proj_1270_ = lean_ctor_get_uint8(v___x_1259_, sizeof(void*)*3 + 8);
v_decide_1271_ = lean_ctor_get_uint8(v___x_1259_, sizeof(void*)*3 + 9);
v_arith_1272_ = lean_ctor_get_uint8(v___x_1259_, sizeof(void*)*3 + 10);
v_autoUnfold_1273_ = lean_ctor_get_uint8(v___x_1259_, sizeof(void*)*3 + 11);
v_failIfUnchanged_1274_ = lean_ctor_get_uint8(v___x_1259_, sizeof(void*)*3 + 13);
v_ground_1275_ = lean_ctor_get_uint8(v___x_1259_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_1276_ = lean_ctor_get_uint8(v___x_1259_, sizeof(void*)*3 + 15);
v_zetaDelta_1277_ = lean_ctor_get_uint8(v___x_1259_, sizeof(void*)*3 + 16);
v_index_1278_ = lean_ctor_get_uint8(v___x_1259_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_1279_ = lean_ctor_get_uint8(v___x_1259_, sizeof(void*)*3 + 18);
v_zetaUnused_1280_ = lean_ctor_get_uint8(v___x_1259_, sizeof(void*)*3 + 19);
v_catchRuntime_1281_ = lean_ctor_get_uint8(v___x_1259_, sizeof(void*)*3 + 20);
v_zetaHave_1282_ = lean_ctor_get_uint8(v___x_1259_, sizeof(void*)*3 + 21);
v_congrConsts_1283_ = lean_ctor_get_uint8(v___x_1259_, sizeof(void*)*3 + 23);
v_bitVecOfNat_1284_ = lean_ctor_get_uint8(v___x_1259_, sizeof(void*)*3 + 24);
v_warnExponents_1285_ = lean_ctor_get_uint8(v___x_1259_, sizeof(void*)*3 + 25);
v_suggestions_1286_ = lean_ctor_get_uint8(v___x_1259_, sizeof(void*)*3 + 26);
v_maxSuggestions_1287_ = lean_ctor_get(v___x_1259_, 2);
v_locals_1288_ = lean_ctor_get_uint8(v___x_1259_, sizeof(void*)*3 + 27);
v_instances_1289_ = lean_ctor_get_uint8(v___x_1259_, sizeof(void*)*3 + 28);
lean_inc(v_maxSuggestions_1287_);
lean_inc(v_maxDischargeDepth_1261_);
lean_inc(v_maxSteps_1260_);
v___x_1290_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1290_, 0, v_maxSteps_1260_);
lean_ctor_set(v___x_1290_, 1, v_maxDischargeDepth_1261_);
lean_ctor_set(v___x_1290_, 2, v_maxSuggestions_1287_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3, v_contextual_1262_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3 + 1, v_memoize_1263_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3 + 2, v_singlePass_1264_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3 + 3, v_zeta_1265_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3 + 4, v_beta_1266_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3 + 5, v_eta_1267_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3 + 6, v_etaStruct_1268_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3 + 7, v_iota_1269_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3 + 8, v_proj_1270_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3 + 9, v_decide_1271_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3 + 10, v_arith_1272_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3 + 11, v_autoUnfold_1273_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3 + 12, v___x_1244_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3 + 13, v_failIfUnchanged_1274_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3 + 14, v_ground_1275_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3 + 15, v_unfoldPartialApp_1276_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3 + 16, v_zetaDelta_1277_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3 + 17, v_index_1278_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_1279_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3 + 19, v_zetaUnused_1280_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3 + 20, v_catchRuntime_1281_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3 + 21, v_zetaHave_1282_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3 + 22, v___x_1243_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3 + 23, v_congrConsts_1283_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3 + 24, v_bitVecOfNat_1284_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3 + 25, v_warnExponents_1285_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3 + 26, v_suggestions_1286_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3 + 27, v_locals_1288_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3 + 28, v_instances_1289_);
v___x_1291_ = lean_unsigned_to_nat(1u);
v___x_1292_ = lean_mk_empty_array_with_capacity(v___x_1291_);
v___x_1293_ = lean_array_push(v___x_1292_, v_a_1256_);
v___x_1294_ = l_Lean_Options_empty;
v___x_1295_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1290_, v___x_1293_, v_a_1258_, v___x_1294_, v_a_1236_, v_a_1238_, v_a_1239_);
return v___x_1295_;
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec(v_a_1256_);
v_a_1296_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1257_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1257_);
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
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
v_a_1304_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1255_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1255_);
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
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
v_a_1312_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1252_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1252_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
v_a_1320_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1249_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1249_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
v_a_1328_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1246_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1246_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_getSimpContext___boxed(lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_);
lean_dec(v_a_1339_);
lean_dec_ref(v_a_1338_);
lean_dec(v_a_1337_);
lean_dec_ref(v_a_1336_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_){
_start:
{
lean_object* v___x_1348_; 
v___x_1348_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_1346_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1350_; lean_object* v_maxSteps_1351_; lean_object* v_maxDischargeDepth_1352_; uint8_t v_contextual_1353_; uint8_t v_memoize_1354_; uint8_t v_singlePass_1355_; uint8_t v_zeta_1356_; uint8_t v_beta_1357_; uint8_t v_eta_1358_; uint8_t v_etaStruct_1359_; uint8_t v_iota_1360_; uint8_t v_proj_1361_; uint8_t v_decide_1362_; uint8_t v_arith_1363_; uint8_t v_autoUnfold_1364_; uint8_t v_failIfUnchanged_1365_; uint8_t v_ground_1366_; uint8_t v_unfoldPartialApp_1367_; uint8_t v_zetaDelta_1368_; uint8_t v_index_1369_; uint8_t v_implicitDefEqProofs_1370_; uint8_t v_zetaUnused_1371_; uint8_t v_catchRuntime_1372_; uint8_t v_zetaHave_1373_; uint8_t v_congrConsts_1374_; uint8_t v_bitVecOfNat_1375_; uint8_t v_warnExponents_1376_; uint8_t v_suggestions_1377_; lean_object* v_maxSuggestions_1378_; uint8_t v_locals_1379_; uint8_t v_instances_1380_; uint8_t v___x_1381_; uint8_t v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_a_1349_);
lean_dec_ref_known(v___x_1348_, 1);
v___x_1350_ = l_Lean_Meta_Simp_neutralConfig;
v_maxSteps_1351_ = lean_ctor_get(v___x_1350_, 0);
v_maxDischargeDepth_1352_ = lean_ctor_get(v___x_1350_, 1);
v_contextual_1353_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*3);
v_memoize_1354_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*3 + 1);
v_singlePass_1355_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*3 + 2);
v_zeta_1356_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*3 + 3);
v_beta_1357_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*3 + 4);
v_eta_1358_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*3 + 5);
v_etaStruct_1359_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*3 + 6);
v_iota_1360_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*3 + 7);
v_proj_1361_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*3 + 8);
v_decide_1362_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*3 + 9);
v_arith_1363_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*3 + 10);
v_autoUnfold_1364_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*3 + 11);
v_failIfUnchanged_1365_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*3 + 13);
v_ground_1366_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_1367_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*3 + 15);
v_zetaDelta_1368_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*3 + 16);
v_index_1369_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_1370_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*3 + 18);
v_zetaUnused_1371_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*3 + 19);
v_catchRuntime_1372_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*3 + 20);
v_zetaHave_1373_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*3 + 21);
v_congrConsts_1374_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*3 + 23);
v_bitVecOfNat_1375_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*3 + 24);
v_warnExponents_1376_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*3 + 25);
v_suggestions_1377_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*3 + 26);
v_maxSuggestions_1378_ = lean_ctor_get(v___x_1350_, 2);
v_locals_1379_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*3 + 27);
v_instances_1380_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*3 + 28);
v___x_1381_ = 0;
v___x_1382_ = 1;
lean_inc(v_maxSuggestions_1378_);
lean_inc(v_maxDischargeDepth_1352_);
lean_inc(v_maxSteps_1351_);
v___x_1383_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1383_, 0, v_maxSteps_1351_);
lean_ctor_set(v___x_1383_, 1, v_maxDischargeDepth_1352_);
lean_ctor_set(v___x_1383_, 2, v_maxSuggestions_1378_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3, v_contextual_1353_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 1, v_memoize_1354_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 2, v_singlePass_1355_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 3, v_zeta_1356_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 4, v_beta_1357_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 5, v_eta_1358_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 6, v_etaStruct_1359_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 7, v_iota_1360_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 8, v_proj_1361_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 9, v_decide_1362_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 10, v_arith_1363_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 11, v_autoUnfold_1364_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 12, v___x_1381_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 13, v_failIfUnchanged_1365_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 14, v_ground_1366_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 15, v_unfoldPartialApp_1367_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 16, v_zetaDelta_1368_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 17, v_index_1369_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_1370_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 19, v_zetaUnused_1371_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 20, v_catchRuntime_1372_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 21, v_zetaHave_1373_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 22, v___x_1382_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 23, v_congrConsts_1374_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 24, v_bitVecOfNat_1375_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 25, v_warnExponents_1376_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 26, v_suggestions_1377_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 27, v_locals_1379_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 28, v_instances_1380_);
v___x_1384_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg___closed__0));
v___x_1385_ = l_Lean_Options_empty;
v___x_1386_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1383_, v___x_1384_, v_a_1349_, v___x_1385_, v_a_1344_, v_a_1345_, v_a_1346_);
return v___x_1386_;
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
v_a_1387_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1348_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1348_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg___boxed(lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_1395_, v_a_1396_, v_a_1397_);
lean_dec(v_a_1397_);
lean_dec_ref(v_a_1396_);
lean_dec_ref(v_a_1395_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27(lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_){
_start:
{
lean_object* v___x_1405_; 
v___x_1405_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_1400_, v_a_1402_, v_a_1403_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___boxed(lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27(v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_);
lean_dec(v_a_1409_);
lean_dec_ref(v_a_1408_);
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(lean_object* v_e_1412_, lean_object* v___y_1413_){
_start:
{
uint8_t v___x_1415_; 
v___x_1415_ = l_Lean_Expr_hasMVar(v_e_1412_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; 
v___x_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1416_, 0, v_e_1412_);
return v___x_1416_;
}
else
{
lean_object* v___x_1417_; lean_object* v_mctx_1418_; lean_object* v___x_1419_; lean_object* v_fst_1420_; lean_object* v_snd_1421_; lean_object* v___x_1422_; lean_object* v_cache_1423_; lean_object* v_zetaDeltaFVarIds_1424_; lean_object* v_postponed_1425_; lean_object* v_diag_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1435_; 
v___x_1417_ = lean_st_ref_get(v___y_1413_);
v_mctx_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc_ref(v_mctx_1418_);
lean_dec(v___x_1417_);
v___x_1419_ = l_Lean_instantiateMVarsCore(v_mctx_1418_, v_e_1412_);
v_fst_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_fst_1420_);
v_snd_1421_ = lean_ctor_get(v___x_1419_, 1);
lean_inc(v_snd_1421_);
lean_dec_ref(v___x_1419_);
v___x_1422_ = lean_st_ref_take(v___y_1413_);
v_cache_1423_ = lean_ctor_get(v___x_1422_, 1);
v_zetaDeltaFVarIds_1424_ = lean_ctor_get(v___x_1422_, 2);
v_postponed_1425_ = lean_ctor_get(v___x_1422_, 3);
v_diag_1426_ = lean_ctor_get(v___x_1422_, 4);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1435_ == 0)
{
lean_object* v_unused_1436_; 
v_unused_1436_ = lean_ctor_get(v___x_1422_, 0);
lean_dec(v_unused_1436_);
v___x_1428_ = v___x_1422_;
v_isShared_1429_ = v_isSharedCheck_1435_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_diag_1426_);
lean_inc(v_postponed_1425_);
lean_inc(v_zetaDeltaFVarIds_1424_);
lean_inc(v_cache_1423_);
lean_dec(v___x_1422_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1435_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 0, v_snd_1421_);
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_snd_1421_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_cache_1423_);
lean_ctor_set(v_reuseFailAlloc_1434_, 2, v_zetaDeltaFVarIds_1424_);
lean_ctor_set(v_reuseFailAlloc_1434_, 3, v_postponed_1425_);
lean_ctor_set(v_reuseFailAlloc_1434_, 4, v_diag_1426_);
v___x_1431_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1432_ = lean_st_ref_put(v___y_1413_, v___x_1431_);
v___x_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1433_, 0, v_fst_1420_);
return v___x_1433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg___boxed(lean_object* v_e_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_e_1437_, v___y_1438_);
lean_dec(v___y_1438_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0(lean_object* v_e_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_e_1441_, v___y_1446_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___boxed(lean_object* v_e_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0(v_e_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(lean_object* v_cls_1461_, lean_object* v_msg_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v_ref_1468_; lean_object* v___x_1469_; lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1514_; 
v_ref_1468_ = lean_ctor_get(v___y_1465_, 4);
v___x_1469_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(v_msg_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1472_ = v___x_1469_;
v_isShared_1473_ = v_isSharedCheck_1514_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1469_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1514_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1474_; lean_object* v_traceState_1475_; lean_object* v_env_1476_; lean_object* v_nextMacroScope_1477_; lean_object* v_ngen_1478_; lean_object* v_auxDeclNGen_1479_; lean_object* v_cache_1480_; lean_object* v_messages_1481_; lean_object* v_infoState_1482_; lean_object* v_snapshotTasks_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1513_; 
v___x_1474_ = lean_st_ref_take(v___y_1466_);
v_traceState_1475_ = lean_ctor_get(v___x_1474_, 4);
v_env_1476_ = lean_ctor_get(v___x_1474_, 0);
v_nextMacroScope_1477_ = lean_ctor_get(v___x_1474_, 1);
v_ngen_1478_ = lean_ctor_get(v___x_1474_, 2);
v_auxDeclNGen_1479_ = lean_ctor_get(v___x_1474_, 3);
v_cache_1480_ = lean_ctor_get(v___x_1474_, 5);
v_messages_1481_ = lean_ctor_get(v___x_1474_, 6);
v_infoState_1482_ = lean_ctor_get(v___x_1474_, 7);
v_snapshotTasks_1483_ = lean_ctor_get(v___x_1474_, 8);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1485_ = v___x_1474_;
v_isShared_1486_ = v_isSharedCheck_1513_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_snapshotTasks_1483_);
lean_inc(v_infoState_1482_);
lean_inc(v_messages_1481_);
lean_inc(v_cache_1480_);
lean_inc(v_traceState_1475_);
lean_inc(v_auxDeclNGen_1479_);
lean_inc(v_ngen_1478_);
lean_inc(v_nextMacroScope_1477_);
lean_inc(v_env_1476_);
lean_dec(v___x_1474_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1513_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
uint64_t v_tid_1487_; lean_object* v_traces_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1512_; 
v_tid_1487_ = lean_ctor_get_uint64(v_traceState_1475_, sizeof(void*)*1);
v_traces_1488_ = lean_ctor_get(v_traceState_1475_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_traceState_1475_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1490_ = v_traceState_1475_;
v_isShared_1491_ = v_isSharedCheck_1512_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_traces_1488_);
lean_dec(v_traceState_1475_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1512_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1492_; double v___x_1493_; uint8_t v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1502_; 
v___x_1492_ = lean_box(0);
v___x_1493_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0);
v___x_1494_ = 0;
v___x_1495_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__1));
v___x_1496_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1496_, 0, v_cls_1461_);
lean_ctor_set(v___x_1496_, 1, v___x_1492_);
lean_ctor_set(v___x_1496_, 2, v___x_1495_);
lean_ctor_set_float(v___x_1496_, sizeof(void*)*3, v___x_1493_);
lean_ctor_set_float(v___x_1496_, sizeof(void*)*3 + 8, v___x_1493_);
lean_ctor_set_uint8(v___x_1496_, sizeof(void*)*3 + 16, v___x_1494_);
v___x_1497_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__2));
v___x_1498_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1496_);
lean_ctor_set(v___x_1498_, 1, v_a_1470_);
lean_ctor_set(v___x_1498_, 2, v___x_1497_);
lean_inc(v_ref_1468_);
v___x_1499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1499_, 0, v_ref_1468_);
lean_ctor_set(v___x_1499_, 1, v___x_1498_);
v___x_1500_ = l_Lean_PersistentArray_push___redArg(v_traces_1488_, v___x_1499_);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 0, v___x_1500_);
v___x_1502_ = v___x_1490_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1500_);
lean_ctor_set_uint64(v_reuseFailAlloc_1511_, sizeof(void*)*1, v_tid_1487_);
v___x_1502_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
lean_object* v___x_1504_; 
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 4, v___x_1502_);
v___x_1504_ = v___x_1485_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_env_1476_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_nextMacroScope_1477_);
lean_ctor_set(v_reuseFailAlloc_1510_, 2, v_ngen_1478_);
lean_ctor_set(v_reuseFailAlloc_1510_, 3, v_auxDeclNGen_1479_);
lean_ctor_set(v_reuseFailAlloc_1510_, 4, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1510_, 5, v_cache_1480_);
lean_ctor_set(v_reuseFailAlloc_1510_, 6, v_messages_1481_);
lean_ctor_set(v_reuseFailAlloc_1510_, 7, v_infoState_1482_);
lean_ctor_set(v_reuseFailAlloc_1510_, 8, v_snapshotTasks_1483_);
v___x_1504_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1508_; 
v___x_1505_ = lean_st_ref_put(v___y_1466_, v___x_1504_);
v___x_1506_ = lean_box(0);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 0, v___x_1506_);
v___x_1508_ = v___x_1472_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1506_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg___boxed(lean_object* v_cls_1515_, lean_object* v_msg_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v_cls_1515_, v_msg_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
return v_res_1522_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1529_ = lean_box(0);
v___x_1530_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__3));
v___x_1531_ = l_Lean_mkConst(v___x_1530_, v___x_1529_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(lean_object* v_numIndices_1532_, lean_object* v_a_1533_, lean_object* v_as_1534_, lean_object* v_i_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v_zero_1541_; uint8_t v_isZero_1542_; 
v_zero_1541_ = lean_unsigned_to_nat(0u);
v_isZero_1542_ = lean_nat_dec_eq(v_i_1535_, v_zero_1541_);
if (v_isZero_1542_ == 1)
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
lean_dec(v_i_1535_);
lean_dec_ref(v_a_1533_);
v___x_1543_ = lean_box(0);
v___x_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
return v___x_1544_;
}
else
{
lean_object* v_one_1545_; lean_object* v_n_1546_; lean_object* v___x_1547_; 
v_one_1545_ = lean_unsigned_to_nat(1u);
v_n_1546_ = lean_nat_sub(v_i_1535_, v_one_1545_);
lean_dec(v_i_1535_);
v___x_1547_ = lean_array_fget(v_as_1534_, v_n_1546_);
if (lean_obj_tag(v___x_1547_) == 0)
{
v_i_1535_ = v_n_1546_;
goto _start;
}
else
{
lean_object* v_val_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1613_; 
v_val_1549_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1551_ = v___x_1547_;
v_isShared_1552_ = v_isSharedCheck_1613_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_val_1549_);
lean_dec(v___x_1547_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1613_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1553_; uint8_t v___x_1554_; 
v___x_1553_ = l_Lean_LocalDecl_index(v_val_1549_);
v___x_1554_ = lean_nat_dec_le(v_numIndices_1532_, v___x_1553_);
lean_dec(v___x_1553_);
if (v___x_1554_ == 0)
{
uint8_t v___x_1555_; 
v___x_1555_ = l_Lean_LocalDecl_isAuxDecl(v_val_1549_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = l_Lean_LocalDecl_type(v_val_1549_);
lean_inc_ref(v___x_1556_);
lean_inc_ref(v_a_1533_);
v___x_1557_ = l_Lean_Meta_isExprDefEq(v_a_1533_, v___x_1556_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1602_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1560_ = v___x_1557_;
v_isShared_1561_ = v_isSharedCheck_1602_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1557_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1602_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
uint8_t v___x_1562_; 
v___x_1562_ = lean_unbox(v_a_1558_);
lean_dec(v_a_1558_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; uint8_t v___x_1564_; 
lean_del_object(v___x_1560_);
v___x_1563_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__1));
v___x_1564_ = l_Lean_Expr_isAppOfArity(v_a_1533_, v___x_1563_, v_one_1545_);
if (v___x_1564_ == 0)
{
lean_dec_ref(v___x_1556_);
lean_del_object(v___x_1551_);
lean_dec(v_val_1549_);
v_i_1535_ = v_n_1546_;
goto _start;
}
else
{
lean_object* v___x_1566_; uint8_t v___x_1567_; 
v___x_1566_ = l_Lean_Expr_appArg_x21(v_a_1533_);
v___x_1567_ = l_Lean_Expr_isAppOfArity(v___x_1566_, v___x_1563_, v_one_1545_);
if (v___x_1567_ == 0)
{
lean_dec_ref(v___x_1566_);
lean_dec_ref(v___x_1556_);
lean_del_object(v___x_1551_);
lean_dec(v_val_1549_);
v_i_1535_ = v_n_1546_;
goto _start;
}
else
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = l_Lean_Expr_appArg_x21(v___x_1566_);
lean_dec_ref(v___x_1566_);
lean_inc_ref(v___x_1569_);
v___x_1570_ = l_Lean_Meta_isExprDefEq(v___x_1569_, v___x_1556_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1586_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1573_ = v___x_1570_;
v_isShared_1574_ = v_isSharedCheck_1586_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1570_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1586_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
uint8_t v___x_1575_; 
v___x_1575_ = lean_unbox(v_a_1571_);
lean_dec(v_a_1571_);
if (v___x_1575_ == 0)
{
lean_del_object(v___x_1573_);
lean_dec_ref(v___x_1569_);
lean_del_object(v___x_1551_);
lean_dec(v_val_1549_);
v_i_1535_ = v_n_1546_;
goto _start;
}
else
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1581_; 
lean_dec(v_n_1546_);
lean_dec_ref(v_a_1533_);
v___x_1577_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4);
v___x_1578_ = l_Lean_LocalDecl_toExpr(v_val_1549_);
v___x_1579_ = l_Lean_mkAppB(v___x_1577_, v___x_1569_, v___x_1578_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v___x_1579_);
v___x_1581_ = v___x_1551_;
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
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v___x_1581_);
v___x_1583_ = v___x_1573_;
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
lean_dec_ref(v___x_1569_);
lean_del_object(v___x_1551_);
lean_dec(v_val_1549_);
lean_dec(v_n_1546_);
lean_dec_ref(v_a_1533_);
v_a_1587_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1570_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1570_);
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
}
}
else
{
lean_object* v___x_1595_; lean_object* v___x_1597_; 
lean_dec_ref(v___x_1556_);
lean_dec(v_n_1546_);
lean_dec_ref(v_a_1533_);
v___x_1595_ = l_Lean_LocalDecl_toExpr(v_val_1549_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v___x_1595_);
v___x_1597_ = v___x_1551_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1599_; 
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 0, v___x_1597_);
v___x_1599_ = v___x_1560_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1597_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_dec_ref(v___x_1556_);
lean_del_object(v___x_1551_);
lean_dec(v_val_1549_);
lean_dec(v_n_1546_);
lean_dec_ref(v_a_1533_);
v_a_1603_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1557_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1557_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
else
{
lean_del_object(v___x_1551_);
lean_dec(v_val_1549_);
v_i_1535_ = v_n_1546_;
goto _start;
}
}
else
{
lean_del_object(v___x_1551_);
lean_dec(v_val_1549_);
v_i_1535_ = v_n_1546_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_numIndices_1614_, lean_object* v_a_1615_, lean_object* v_as_1616_, lean_object* v_i_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_numIndices_1614_, v_a_1615_, v_as_1616_, v_i_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec_ref(v_as_1616_);
lean_dec(v_numIndices_1614_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(lean_object* v_numIndices_1624_, lean_object* v_a_1625_, lean_object* v_as_1626_, lean_object* v_i_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v_zero_1636_; uint8_t v_isZero_1637_; 
v_zero_1636_ = lean_unsigned_to_nat(0u);
v_isZero_1637_ = lean_nat_dec_eq(v_i_1627_, v_zero_1636_);
if (v_isZero_1637_ == 1)
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
lean_dec(v_i_1627_);
lean_dec_ref(v_a_1625_);
v___x_1638_ = lean_box(0);
v___x_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
return v___x_1639_;
}
else
{
lean_object* v_one_1640_; lean_object* v_n_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v_one_1640_ = lean_unsigned_to_nat(1u);
v_n_1641_ = lean_nat_sub(v_i_1627_, v_one_1640_);
lean_dec(v_i_1627_);
v___x_1642_ = lean_array_fget_borrowed(v_as_1626_, v_n_1641_);
lean_inc_ref(v_a_1625_);
v___x_1643_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_numIndices_1624_, v_a_1625_, v___x_1642_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_a_1644_);
if (lean_obj_tag(v_a_1644_) == 0)
{
lean_dec_ref_known(v___x_1643_, 1);
v_i_1627_ = v_n_1641_;
goto _start;
}
else
{
lean_dec_ref_known(v_a_1644_, 1);
lean_dec(v_n_1641_);
lean_dec_ref(v_a_1625_);
return v___x_1643_;
}
}
else
{
lean_dec(v_n_1641_);
lean_dec_ref(v_a_1625_);
return v___x_1643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(lean_object* v_numIndices_1646_, lean_object* v_a_1647_, lean_object* v_x_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
if (lean_obj_tag(v_x_1648_) == 0)
{
lean_object* v_cs_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v_cs_1657_ = lean_ctor_get(v_x_1648_, 0);
v___x_1658_ = lean_array_get_size(v_cs_1657_);
v___x_1659_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_numIndices_1646_, v_a_1647_, v_cs_1657_, v___x_1658_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
return v___x_1659_;
}
else
{
lean_object* v_vs_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v_vs_1660_ = lean_ctor_get(v_x_1648_, 0);
v___x_1661_ = lean_array_get_size(v_vs_1660_);
v___x_1662_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_numIndices_1646_, v_a_1647_, v_vs_1660_, v___x_1661_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
return v___x_1662_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3___boxed(lean_object* v_numIndices_1663_, lean_object* v_a_1664_, lean_object* v_x_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_numIndices_1663_, v_a_1664_, v_x_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v_x_1665_);
lean_dec(v_numIndices_1663_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_numIndices_1675_, lean_object* v_a_1676_, lean_object* v_as_1677_, lean_object* v_i_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_numIndices_1675_, v_a_1676_, v_as_1677_, v_i_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v_as_1677_);
lean_dec(v_numIndices_1675_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(lean_object* v_numIndices_1688_, lean_object* v_a_1689_, lean_object* v_t_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v_root_1699_; lean_object* v_tail_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v_root_1699_ = lean_ctor_get(v_t_1690_, 0);
v_tail_1700_ = lean_ctor_get(v_t_1690_, 1);
v___x_1701_ = lean_array_get_size(v_tail_1700_);
lean_inc_ref(v_a_1689_);
v___x_1702_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_numIndices_1688_, v_a_1689_, v_tail_1700_, v___x_1701_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
if (lean_obj_tag(v_a_1703_) == 0)
{
lean_object* v___x_1704_; 
lean_dec_ref_known(v___x_1702_, 1);
v___x_1704_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_numIndices_1688_, v_a_1689_, v_root_1699_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
return v___x_1704_;
}
else
{
lean_dec_ref_known(v_a_1703_, 1);
lean_dec_ref(v_a_1689_);
return v___x_1702_;
}
}
else
{
lean_dec_ref(v_a_1689_);
return v___x_1702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1___boxed(lean_object* v_numIndices_1705_, lean_object* v_a_1706_, lean_object* v_t_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(v_numIndices_1705_, v_a_1706_, v_t_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec_ref(v_t_1707_);
lean_dec(v_numIndices_1705_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(lean_object* v_numIndices_1717_, lean_object* v_a_1718_, lean_object* v_lctx_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v_decls_1728_; lean_object* v___x_1729_; 
v_decls_1728_ = lean_ctor_get(v_lctx_1719_, 1);
v___x_1729_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(v_numIndices_1717_, v_a_1718_, v_decls_1728_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1___boxed(lean_object* v_numIndices_1730_, lean_object* v_a_1731_, lean_object* v_lctx_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(v_numIndices_1730_, v_a_1731_, v_lctx_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec_ref(v_lctx_1732_);
lean_dec(v_numIndices_1730_);
return v_res_1741_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3(void){
_start:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1747_ = lean_box(0);
v___x_1748_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2));
v___x_1749_ = l_Lean_mkConst(v___x_1748_, v___x_1747_);
return v___x_1749_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6(void){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1753_ = lean_box(0);
v___x_1754_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__5));
v___x_1755_ = l_Lean_mkConst(v___x_1754_, v___x_1753_);
return v___x_1755_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10(void){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1762_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9));
v___x_1763_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4));
v___x_1764_ = l_Lean_Name_append(v___x_1763_, v___x_1762_);
return v___x_1764_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11));
v___x_1767_ = l_Lean_stringToMessageData(v___x_1766_);
return v___x_1767_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14(void){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13));
v___x_1770_ = l_Lean_stringToMessageData(v___x_1769_);
return v___x_1770_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17(void){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__16));
v___x_1775_ = l_Lean_MessageData_ofFormat(v___x_1774_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(lean_object* v_numIndices_1776_, uint8_t v_useDecide_1777_, lean_object* v_prop_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_){
_start:
{
lean_object* v___x_1787_; lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1922_; 
v___x_1787_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_prop_1778_, v_a_1783_);
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1790_ = v___x_1787_;
v_isShared_1791_ = v_isSharedCheck_1922_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1787_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1922_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v_options_1889_; uint8_t v_hasTrace_1890_; 
v_options_1889_ = lean_ctor_get(v_a_1784_, 1);
v_hasTrace_1890_ = lean_ctor_get_uint8(v_options_1889_, sizeof(void*)*1);
if (v_hasTrace_1890_ == 0)
{
v___y_1849_ = v_a_1779_;
v___y_1850_ = v_a_1780_;
v___y_1851_ = v_a_1781_;
v___y_1852_ = v_a_1782_;
v___y_1853_ = v_a_1783_;
v___y_1854_ = v_a_1784_;
v___y_1855_ = v_a_1785_;
goto v___jp_1848_;
}
else
{
lean_object* v_toCold_1891_; lean_object* v_inheritedTraceOptions_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; uint8_t v___x_1895_; 
v_toCold_1891_ = lean_ctor_get(v_a_1784_, 0);
v_inheritedTraceOptions_1892_ = lean_ctor_get(v_toCold_1891_, 4);
v___x_1893_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9));
v___x_1894_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10);
v___x_1895_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1892_, v_options_1889_, v___x_1894_);
if (v___x_1895_ == 0)
{
v___y_1849_ = v_a_1779_;
v___y_1850_ = v_a_1780_;
v___y_1851_ = v_a_1781_;
v___y_1852_ = v_a_1782_;
v___y_1853_ = v_a_1783_;
v___y_1854_ = v_a_1784_;
v___y_1855_ = v_a_1785_;
goto v___jp_1848_;
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___y_1902_; lean_object* v___x_1915_; lean_object* v___x_1916_; uint8_t v___x_1917_; 
v___x_1896_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12);
lean_inc(v_a_1788_);
v___x_1897_ = l_Lean_MessageData_ofExpr(v_a_1788_);
v___x_1898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1896_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
v___x_1899_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14);
v___x_1900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1898_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
v___x_1915_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__1));
v___x_1916_ = lean_unsigned_to_nat(1u);
v___x_1917_ = l_Lean_Expr_isAppOfArity(v_a_1788_, v___x_1915_, v___x_1916_);
if (v___x_1917_ == 0)
{
goto v___jp_1913_;
}
else
{
lean_object* v___x_1918_; uint8_t v___x_1919_; 
v___x_1918_ = l_Lean_Expr_appArg_x21(v_a_1788_);
v___x_1919_ = l_Lean_Expr_isAppOfArity(v___x_1918_, v___x_1915_, v___x_1916_);
if (v___x_1919_ == 0)
{
lean_dec_ref(v___x_1918_);
goto v___jp_1913_;
}
else
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1920_ = l_Lean_Expr_appArg_x21(v___x_1918_);
lean_dec_ref(v___x_1918_);
v___x_1921_ = l_Lean_MessageData_ofExpr(v___x_1920_);
v___y_1902_ = v___x_1921_;
goto v___jp_1901_;
}
}
v___jp_1901_:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1900_);
lean_ctor_set(v___x_1903_, 1, v___y_1902_);
v___x_1904_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v___x_1893_, v___x_1903_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_dec_ref_known(v___x_1904_, 1);
v___y_1849_ = v_a_1779_;
v___y_1850_ = v_a_1780_;
v___y_1851_ = v_a_1781_;
v___y_1852_ = v_a_1782_;
v___y_1853_ = v_a_1783_;
v___y_1854_ = v_a_1784_;
v___y_1855_ = v_a_1785_;
goto v___jp_1848_;
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
lean_del_object(v___x_1790_);
lean_dec(v_a_1788_);
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
v___jp_1913_:
{
lean_object* v___x_1914_; 
v___x_1914_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17);
v___y_1902_ = v___x_1914_;
goto v___jp_1901_;
}
}
}
v___jp_1792_:
{
lean_object* v_lctx_1800_; lean_object* v___x_1801_; 
v_lctx_1800_ = lean_ctor_get(v___y_1796_, 2);
v___x_1801_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(v_numIndices_1776_, v_a_1788_, v_lctx_1800_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
return v___x_1801_;
}
v___jp_1802_:
{
if (lean_obj_tag(v___y_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1814_; uint8_t v___x_1815_; 
v_a_1813_ = lean_ctor_get(v___y_1812_, 0);
lean_inc(v_a_1813_);
lean_dec_ref_known(v___y_1812_, 1);
v___x_1814_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2));
v___x_1815_ = l_Lean_Expr_isConstOf(v_a_1813_, v___x_1814_);
lean_dec(v_a_1813_);
if (v___x_1815_ == 0)
{
lean_dec_ref(v___y_1811_);
lean_dec_ref(v___y_1808_);
lean_del_object(v___x_1790_);
v___y_1793_ = v___y_1806_;
v___y_1794_ = v___y_1804_;
v___y_1795_ = v___y_1803_;
v___y_1796_ = v___y_1805_;
v___y_1797_ = v___y_1810_;
v___y_1798_ = v___y_1807_;
v___y_1799_ = v___y_1809_;
goto v___jp_1792_;
}
else
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
lean_dec(v_a_1788_);
v___x_1816_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3);
v___x_1817_ = l_Lean_Meta_mkEqRefl(v___x_1816_, v___y_1805_, v___y_1810_, v___y_1807_, v___y_1809_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1831_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1820_ = v___x_1817_;
v_isShared_1821_ = v_isSharedCheck_1831_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1817_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1831_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1826_; 
v___x_1822_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6);
v___x_1823_ = l_Lean_Expr_appArg_x21(v___y_1808_);
lean_dec_ref(v___y_1808_);
v___x_1824_ = l_Lean_mkApp3(v___x_1822_, v___y_1811_, v___x_1823_, v_a_1818_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set_tag(v___x_1790_, 1);
lean_ctor_set(v___x_1790_, 0, v___x_1824_);
v___x_1826_ = v___x_1790_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1824_);
v___x_1826_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
lean_object* v___x_1828_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1826_);
v___x_1828_ = v___x_1820_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1826_);
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
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
lean_dec_ref(v___y_1811_);
lean_dec_ref(v___y_1808_);
lean_del_object(v___x_1790_);
v_a_1832_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1817_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1817_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
lean_dec_ref(v___y_1811_);
lean_dec_ref(v___y_1808_);
lean_del_object(v___x_1790_);
lean_dec(v_a_1788_);
v_a_1840_ = lean_ctor_get(v___y_1812_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___y_1812_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___y_1812_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___y_1812_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
v___jp_1848_:
{
if (v_useDecide_1777_ == 0)
{
lean_del_object(v___x_1790_);
v___y_1793_ = v___y_1849_;
v___y_1794_ = v___y_1850_;
v___y_1795_ = v___y_1851_;
v___y_1796_ = v___y_1852_;
v___y_1797_ = v___y_1853_;
v___y_1798_ = v___y_1854_;
v___y_1799_ = v___y_1855_;
goto v___jp_1792_;
}
else
{
lean_object* v___x_1856_; lean_object* v_a_1857_; uint8_t v___x_1858_; 
lean_inc(v_a_1788_);
v___x_1856_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_a_1788_, v___y_1853_);
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_a_1857_);
lean_dec_ref(v___x_1856_);
v___x_1858_ = l_Lean_Expr_hasFVar(v_a_1857_);
if (v___x_1858_ == 0)
{
uint8_t v___x_1859_; 
v___x_1859_ = l_Lean_Expr_hasMVar(v_a_1857_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; 
lean_inc(v_a_1857_);
v___x_1860_ = l_Lean_Meta_mkDecide(v_a_1857_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1862_; uint8_t v_transparency_1863_; uint8_t v___x_1864_; uint8_t v___x_1865_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_a_1861_);
lean_dec_ref_known(v___x_1860_, 1);
v___x_1862_ = l_Lean_Meta_Context_config(v___y_1852_);
v_transparency_1863_ = lean_ctor_get_uint8(v___x_1862_, 9);
lean_dec_ref(v___x_1862_);
v___x_1864_ = 1;
v___x_1865_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1863_, v___x_1864_);
if (v___x_1865_ == 0)
{
lean_object* v_keyedConfig_1866_; uint8_t v_trackZetaDelta_1867_; lean_object* v_zetaDeltaSet_1868_; lean_object* v_lctx_1869_; lean_object* v_localInstances_1870_; lean_object* v_defEqCtx_x3f_1871_; lean_object* v_synthPendingDepth_1872_; lean_object* v_customCanUnfoldPredicate_x3f_1873_; uint8_t v_univApprox_1874_; uint8_t v_inTypeClassResolution_1875_; uint8_t v_cacheInferType_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v_keyedConfig_1866_ = lean_ctor_get(v___y_1852_, 0);
v_trackZetaDelta_1867_ = lean_ctor_get_uint8(v___y_1852_, sizeof(void*)*7);
v_zetaDeltaSet_1868_ = lean_ctor_get(v___y_1852_, 1);
v_lctx_1869_ = lean_ctor_get(v___y_1852_, 2);
v_localInstances_1870_ = lean_ctor_get(v___y_1852_, 3);
v_defEqCtx_x3f_1871_ = lean_ctor_get(v___y_1852_, 4);
v_synthPendingDepth_1872_ = lean_ctor_get(v___y_1852_, 5);
v_customCanUnfoldPredicate_x3f_1873_ = lean_ctor_get(v___y_1852_, 6);
v_univApprox_1874_ = lean_ctor_get_uint8(v___y_1852_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1875_ = lean_ctor_get_uint8(v___y_1852_, sizeof(void*)*7 + 2);
v_cacheInferType_1876_ = lean_ctor_get_uint8(v___y_1852_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1866_);
v___x_1877_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1864_, v_keyedConfig_1866_);
lean_inc(v_customCanUnfoldPredicate_x3f_1873_);
lean_inc(v_synthPendingDepth_1872_);
lean_inc(v_defEqCtx_x3f_1871_);
lean_inc_ref(v_localInstances_1870_);
lean_inc_ref(v_lctx_1869_);
lean_inc(v_zetaDeltaSet_1868_);
v___x_1878_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
lean_ctor_set(v___x_1878_, 1, v_zetaDeltaSet_1868_);
lean_ctor_set(v___x_1878_, 2, v_lctx_1869_);
lean_ctor_set(v___x_1878_, 3, v_localInstances_1870_);
lean_ctor_set(v___x_1878_, 4, v_defEqCtx_x3f_1871_);
lean_ctor_set(v___x_1878_, 5, v_synthPendingDepth_1872_);
lean_ctor_set(v___x_1878_, 6, v_customCanUnfoldPredicate_x3f_1873_);
lean_ctor_set_uint8(v___x_1878_, sizeof(void*)*7, v_trackZetaDelta_1867_);
lean_ctor_set_uint8(v___x_1878_, sizeof(void*)*7 + 1, v_univApprox_1874_);
lean_ctor_set_uint8(v___x_1878_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1875_);
lean_ctor_set_uint8(v___x_1878_, sizeof(void*)*7 + 3, v_cacheInferType_1876_);
lean_inc(v___y_1855_);
lean_inc_ref(v___y_1854_);
lean_inc(v___y_1853_);
lean_inc(v_a_1861_);
v___x_1879_ = lean_whnf(v_a_1861_, v___x_1878_, v___y_1853_, v___y_1854_, v___y_1855_);
v___y_1803_ = v___y_1851_;
v___y_1804_ = v___y_1850_;
v___y_1805_ = v___y_1852_;
v___y_1806_ = v___y_1849_;
v___y_1807_ = v___y_1854_;
v___y_1808_ = v_a_1861_;
v___y_1809_ = v___y_1855_;
v___y_1810_ = v___y_1853_;
v___y_1811_ = v_a_1857_;
v___y_1812_ = v___x_1879_;
goto v___jp_1802_;
}
else
{
lean_object* v___x_1880_; 
lean_inc(v___y_1855_);
lean_inc_ref(v___y_1854_);
lean_inc(v___y_1853_);
lean_inc_ref(v___y_1852_);
lean_inc(v_a_1861_);
v___x_1880_ = lean_whnf(v_a_1861_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
v___y_1803_ = v___y_1851_;
v___y_1804_ = v___y_1850_;
v___y_1805_ = v___y_1852_;
v___y_1806_ = v___y_1849_;
v___y_1807_ = v___y_1854_;
v___y_1808_ = v_a_1861_;
v___y_1809_ = v___y_1855_;
v___y_1810_ = v___y_1853_;
v___y_1811_ = v_a_1857_;
v___y_1812_ = v___x_1880_;
goto v___jp_1802_;
}
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
lean_dec(v_a_1857_);
lean_del_object(v___x_1790_);
lean_dec(v_a_1788_);
v_a_1881_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v___x_1860_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1860_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1881_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
else
{
lean_dec(v_a_1857_);
lean_del_object(v___x_1790_);
v___y_1793_ = v___y_1849_;
v___y_1794_ = v___y_1850_;
v___y_1795_ = v___y_1851_;
v___y_1796_ = v___y_1852_;
v___y_1797_ = v___y_1853_;
v___y_1798_ = v___y_1854_;
v___y_1799_ = v___y_1855_;
goto v___jp_1792_;
}
}
else
{
lean_dec(v_a_1857_);
lean_del_object(v___x_1790_);
v___y_1793_ = v___y_1849_;
v___y_1794_ = v___y_1850_;
v___y_1795_ = v___y_1851_;
v___y_1796_ = v___y_1852_;
v___y_1797_ = v___y_1853_;
v___y_1798_ = v___y_1854_;
v___y_1799_ = v___y_1855_;
goto v___jp_1792_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___boxed(lean_object* v_numIndices_1923_, lean_object* v_useDecide_1924_, lean_object* v_prop_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
uint8_t v_useDecide_boxed_1934_; lean_object* v_res_1935_; 
v_useDecide_boxed_1934_ = lean_unbox(v_useDecide_1924_);
v_res_1935_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_1923_, v_useDecide_boxed_1934_, v_prop_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_);
lean_dec(v_a_1932_);
lean_dec_ref(v_a_1931_);
lean_dec(v_a_1930_);
lean_dec_ref(v_a_1929_);
lean_dec(v_a_1928_);
lean_dec_ref(v_a_1927_);
lean_dec(v_a_1926_);
lean_dec(v_numIndices_1923_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2(lean_object* v_cls_1936_, lean_object* v_msg_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v_cls_1936_, v_msg_1937_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___boxed(lean_object* v_cls_1947_, lean_object* v_msg_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2(v_cls_1947_, v_msg_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2(lean_object* v_numIndices_1958_, lean_object* v_a_1959_, lean_object* v_as_1960_, lean_object* v_i_1961_, lean_object* v_a_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v___x_1971_; 
v___x_1971_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_numIndices_1958_, v_a_1959_, v_as_1960_, v_i_1961_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_numIndices_1972_, lean_object* v_a_1973_, lean_object* v_as_1974_, lean_object* v_i_1975_, lean_object* v_a_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2(v_numIndices_1972_, v_a_1973_, v_as_1974_, v_i_1975_, v_a_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec(v___y_1977_);
lean_dec_ref(v_as_1974_);
lean_dec(v_numIndices_1972_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5(lean_object* v_numIndices_1986_, lean_object* v_a_1987_, lean_object* v_as_1988_, lean_object* v_i_1989_, lean_object* v_a_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_numIndices_1986_, v_a_1987_, v_as_1988_, v_i_1989_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_numIndices_2000_, lean_object* v_a_2001_, lean_object* v_as_2002_, lean_object* v_i_2003_, lean_object* v_a_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5(v_numIndices_2000_, v_a_2001_, v_as_2002_, v_i_2003_, v_a_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v___y_2005_);
lean_dec_ref(v_as_2002_);
lean_dec(v_numIndices_2000_);
return v_res_2013_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3(void){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2019_ = lean_box(0);
v___x_2020_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__2));
v___x_2021_ = l_Lean_mkConst(v___x_2020_, v___x_2019_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27(lean_object* v_numIndices_2025_, uint8_t v_useDecideBool_2026_, lean_object* v_e_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_){
_start:
{
lean_object* v___x_2036_; 
lean_inc_ref(v_e_2027_);
v___x_2036_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2027_, v_a_2032_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2217_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2039_ = v___x_2036_;
v_isShared_2040_ = v_isSharedCheck_2217_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2036_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2217_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2046_; uint8_t v___x_2047_; 
v___x_2046_ = l_Lean_Expr_cleanupAnnotations(v_a_2037_);
v___x_2047_ = l_Lean_Expr_isApp(v___x_2046_);
if (v___x_2047_ == 0)
{
lean_dec_ref(v___x_2046_);
lean_dec_ref(v_e_2027_);
goto v___jp_2041_;
}
else
{
lean_object* v_arg_2048_; lean_object* v___x_2049_; uint8_t v___x_2050_; 
v_arg_2048_ = lean_ctor_get(v___x_2046_, 1);
lean_inc_ref(v_arg_2048_);
v___x_2049_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2046_);
v___x_2050_ = l_Lean_Expr_isApp(v___x_2049_);
if (v___x_2050_ == 0)
{
lean_dec_ref(v___x_2049_);
lean_dec_ref(v_arg_2048_);
lean_dec_ref(v_e_2027_);
goto v___jp_2041_;
}
else
{
lean_object* v_arg_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; 
v_arg_2051_ = lean_ctor_get(v___x_2049_, 1);
lean_inc_ref(v_arg_2051_);
v___x_2052_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2049_);
v___x_2053_ = l_Lean_Expr_isApp(v___x_2052_);
if (v___x_2053_ == 0)
{
lean_dec_ref(v___x_2052_);
lean_dec_ref(v_arg_2051_);
lean_dec_ref(v_arg_2048_);
lean_dec_ref(v_e_2027_);
goto v___jp_2041_;
}
else
{
lean_object* v_arg_2054_; lean_object* v___x_2055_; uint8_t v___x_2056_; 
v_arg_2054_ = lean_ctor_get(v___x_2052_, 1);
lean_inc_ref(v_arg_2054_);
v___x_2055_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2052_);
v___x_2056_ = l_Lean_Expr_isApp(v___x_2055_);
if (v___x_2056_ == 0)
{
lean_dec_ref(v___x_2055_);
lean_dec_ref(v_arg_2054_);
lean_dec_ref(v_arg_2051_);
lean_dec_ref(v_arg_2048_);
lean_dec_ref(v_e_2027_);
goto v___jp_2041_;
}
else
{
lean_object* v_arg_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; 
v_arg_2057_ = lean_ctor_get(v___x_2055_, 1);
lean_inc_ref(v_arg_2057_);
v___x_2058_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2055_);
v___x_2059_ = l_Lean_Expr_isApp(v___x_2058_);
if (v___x_2059_ == 0)
{
lean_dec_ref(v___x_2058_);
lean_dec_ref(v_arg_2057_);
lean_dec_ref(v_arg_2054_);
lean_dec_ref(v_arg_2051_);
lean_dec_ref(v_arg_2048_);
lean_dec_ref(v_e_2027_);
goto v___jp_2041_;
}
else
{
lean_object* v_arg_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; 
v_arg_2060_ = lean_ctor_get(v___x_2058_, 1);
lean_inc_ref(v_arg_2060_);
v___x_2061_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2058_);
v___x_2062_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__2));
v___x_2063_ = l_Lean_Expr_isConstOf(v___x_2061_, v___x_2062_);
if (v___x_2063_ == 0)
{
lean_dec_ref(v___x_2061_);
lean_dec_ref(v_arg_2060_);
lean_dec_ref(v_arg_2057_);
lean_dec_ref(v_arg_2054_);
lean_dec_ref(v_arg_2051_);
lean_dec_ref(v_arg_2048_);
lean_dec_ref(v_e_2027_);
goto v___jp_2041_;
}
else
{
lean_object* v___x_2064_; 
lean_del_object(v___x_2039_);
lean_inc_ref(v_arg_2057_);
v___x_2064_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2025_, v_useDecideBool_2026_, v_arg_2057_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2208_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2067_ = v___x_2064_;
v_isShared_2068_ = v_isSharedCheck_2208_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2064_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2208_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2069_; 
v___x_2069_ = l_Lean_Expr_constLevels_x21(v___x_2061_);
if (lean_obj_tag(v_a_2065_) == 1)
{
lean_object* v_val_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2085_; 
lean_dec_ref(v___x_2061_);
lean_dec_ref(v_e_2027_);
v_val_2070_ = lean_ctor_get(v_a_2065_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v_a_2065_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2072_ = v_a_2065_;
v_isShared_2073_ = v_isSharedCheck_2085_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_val_2070_);
lean_dec(v_a_2065_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2085_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2078_; 
v___x_2074_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__7));
v___x_2075_ = l_Lean_mkConst(v___x_2074_, v___x_2069_);
lean_inc_ref(v_arg_2051_);
v___x_2076_ = l_Lean_mkApp6(v___x_2075_, v_arg_2057_, v_arg_2054_, v_val_2070_, v_arg_2060_, v_arg_2051_, v_arg_2048_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 0, v___x_2076_);
v___x_2078_ = v___x_2072_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2076_);
v___x_2078_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2082_; 
v___x_2079_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2079_, 0, v_arg_2051_);
lean_ctor_set(v___x_2079_, 1, v___x_2078_);
lean_ctor_set_uint8(v___x_2079_, sizeof(void*)*2, v___x_2063_);
v___x_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 0, v___x_2080_);
v___x_2082_ = v___x_2067_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
else
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
lean_del_object(v___x_2067_);
lean_dec(v_a_2065_);
lean_inc_ref(v_arg_2057_);
v___x_2086_ = l_Lean_mkNot(v_arg_2057_);
v___x_2087_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2025_, v_useDecideBool_2026_, v___x_2086_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2199_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2090_ = v___x_2087_;
v_isShared_2091_ = v_isSharedCheck_2199_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2087_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2199_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
if (lean_obj_tag(v_a_2088_) == 1)
{
lean_object* v_val_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2107_; 
lean_dec_ref(v___x_2061_);
lean_dec_ref(v_e_2027_);
v_val_2092_ = lean_ctor_get(v_a_2088_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v_a_2088_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2094_ = v_a_2088_;
v_isShared_2095_ = v_isSharedCheck_2107_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_val_2092_);
lean_dec(v_a_2088_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2107_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2100_; 
v___x_2096_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__9));
v___x_2097_ = l_Lean_mkConst(v___x_2096_, v___x_2069_);
lean_inc_ref(v_arg_2048_);
v___x_2098_ = l_Lean_mkApp6(v___x_2097_, v_arg_2057_, v_arg_2054_, v_val_2092_, v_arg_2060_, v_arg_2051_, v_arg_2048_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v___x_2098_);
v___x_2100_ = v___x_2094_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2098_);
v___x_2100_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2104_; 
v___x_2101_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2101_, 0, v_arg_2048_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
lean_ctor_set_uint8(v___x_2101_, sizeof(void*)*2, v___x_2063_);
v___x_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 0, v___x_2102_);
v___x_2104_ = v___x_2090_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_2102_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
else
{
lean_object* v___x_2108_; 
lean_del_object(v___x_2090_);
lean_dec(v_a_2088_);
lean_inc(v_a_2034_);
lean_inc_ref(v_a_2033_);
lean_inc(v_a_2032_);
lean_inc_ref(v_a_2031_);
lean_inc(v_a_2030_);
lean_inc_ref(v_a_2029_);
lean_inc(v_a_2028_);
lean_inc_ref(v_arg_2057_);
v___x_2108_ = lean_simp(v_arg_2057_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2190_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2111_ = v___x_2108_;
v_isShared_2112_ = v_isSharedCheck_2190_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2108_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2190_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v_expr_2113_; uint8_t v___x_2114_; 
v_expr_2113_ = lean_ctor_get(v_a_2109_, 0);
v___x_2114_ = lean_expr_eqv(v_expr_2113_, v_arg_2057_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
lean_del_object(v___x_2111_);
v___x_2115_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3);
lean_inc_ref(v_expr_2113_);
v___x_2116_ = l_Lean_Expr_app___override(v___x_2115_, v_expr_2113_);
v___x_2117_ = lean_box(0);
v___x_2118_ = l_Lean_Meta_trySynthInstance(v___x_2116_, v___x_2117_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2167_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2121_ = v___x_2118_;
v_isShared_2122_ = v_isSharedCheck_2167_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2118_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2167_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
if (lean_obj_tag(v_a_2119_) == 1)
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2153_; 
lean_inc_ref(v_expr_2113_);
lean_del_object(v___x_2121_);
lean_dec_ref(v_e_2027_);
v_a_2123_ = lean_ctor_get(v_a_2119_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v_a_2119_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2125_ = v_a_2119_;
v_isShared_2126_ = v_isSharedCheck_2153_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v_a_2119_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2153_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2127_; 
v___x_2127_ = l_Lean_Meta_Simp_Result_getProof(v_a_2109_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2144_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2130_ = v___x_2127_;
v_isShared_2131_ = v_isSharedCheck_2144_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2127_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2144_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2137_; 
v___x_2132_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__5));
v___x_2133_ = l_Lean_mkConst(v___x_2132_, v___x_2069_);
lean_inc_ref(v_arg_2048_);
lean_inc_ref(v_arg_2051_);
lean_inc(v_a_2123_);
lean_inc_ref(v_expr_2113_);
lean_inc_ref(v_arg_2060_);
v___x_2134_ = l_Lean_mkApp8(v___x_2133_, v_arg_2060_, v_arg_2057_, v_expr_2113_, v_arg_2054_, v_a_2123_, v_arg_2051_, v_arg_2048_, v_a_2128_);
v___x_2135_ = l_Lean_mkApp5(v___x_2061_, v_arg_2060_, v_expr_2113_, v_a_2123_, v_arg_2051_, v_arg_2048_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 0, v___x_2134_);
v___x_2137_ = v___x_2125_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2134_);
v___x_2137_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2141_; 
v___x_2138_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2138_, 0, v___x_2135_);
lean_ctor_set(v___x_2138_, 1, v___x_2137_);
lean_ctor_set_uint8(v___x_2138_, sizeof(void*)*2, v___x_2063_);
v___x_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2138_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 0, v___x_2139_);
v___x_2141_ = v___x_2130_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2139_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_del_object(v___x_2125_);
lean_dec(v_a_2123_);
lean_dec_ref(v_expr_2113_);
lean_dec(v___x_2069_);
lean_dec_ref(v___x_2061_);
lean_dec_ref(v_arg_2060_);
lean_dec_ref(v_arg_2057_);
lean_dec_ref(v_arg_2054_);
lean_dec_ref(v_arg_2051_);
lean_dec_ref(v_arg_2048_);
v_a_2145_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2127_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2127_);
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
}
else
{
lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2164_; 
lean_dec(v_a_2119_);
lean_dec(v___x_2069_);
lean_dec_ref(v___x_2061_);
lean_dec_ref(v_arg_2060_);
lean_dec_ref(v_arg_2057_);
lean_dec_ref(v_arg_2054_);
lean_dec_ref(v_arg_2051_);
lean_dec_ref(v_arg_2048_);
v_isSharedCheck_2164_ = !lean_is_exclusive(v_a_2109_);
if (v_isSharedCheck_2164_ == 0)
{
lean_object* v_unused_2165_; lean_object* v_unused_2166_; 
v_unused_2165_ = lean_ctor_get(v_a_2109_, 1);
lean_dec(v_unused_2165_);
v_unused_2166_ = lean_ctor_get(v_a_2109_, 0);
lean_dec(v_unused_2166_);
v___x_2155_ = v_a_2109_;
v_isShared_2156_ = v_isSharedCheck_2164_;
goto v_resetjp_2154_;
}
else
{
lean_dec(v_a_2109_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2164_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 1, v___x_2117_);
lean_ctor_set(v___x_2155_, 0, v_e_2027_);
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_e_2027_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v___x_2117_);
v___x_2158_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2159_; lean_object* v___x_2161_; 
lean_ctor_set_uint8(v___x_2158_, sizeof(void*)*2, v___x_2063_);
v___x_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2159_);
v___x_2161_ = v___x_2121_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
}
}
else
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
lean_dec(v_a_2109_);
lean_dec(v___x_2069_);
lean_dec_ref(v___x_2061_);
lean_dec_ref(v_arg_2060_);
lean_dec_ref(v_arg_2057_);
lean_dec_ref(v_arg_2054_);
lean_dec_ref(v_arg_2051_);
lean_dec_ref(v_arg_2048_);
lean_dec_ref(v_e_2027_);
v_a_2168_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v___x_2118_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2118_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
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
lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2187_; 
lean_dec(v___x_2069_);
lean_dec_ref(v___x_2061_);
lean_dec_ref(v_arg_2060_);
lean_dec_ref(v_arg_2057_);
lean_dec_ref(v_arg_2054_);
lean_dec_ref(v_arg_2051_);
lean_dec_ref(v_arg_2048_);
v_isSharedCheck_2187_ = !lean_is_exclusive(v_a_2109_);
if (v_isSharedCheck_2187_ == 0)
{
lean_object* v_unused_2188_; lean_object* v_unused_2189_; 
v_unused_2188_ = lean_ctor_get(v_a_2109_, 1);
lean_dec(v_unused_2188_);
v_unused_2189_ = lean_ctor_get(v_a_2109_, 0);
lean_dec(v_unused_2189_);
v___x_2177_ = v_a_2109_;
v_isShared_2178_ = v_isSharedCheck_2187_;
goto v_resetjp_2176_;
}
else
{
lean_dec(v_a_2109_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2187_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2179_; lean_object* v___x_2181_; 
v___x_2179_ = lean_box(0);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 1, v___x_2179_);
lean_ctor_set(v___x_2177_, 0, v_e_2027_);
v___x_2181_ = v___x_2177_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_e_2027_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v___x_2179_);
v___x_2181_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
lean_object* v___x_2182_; lean_object* v___x_2184_; 
lean_ctor_set_uint8(v___x_2181_, sizeof(void*)*2, v___x_2063_);
v___x_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 0, v___x_2182_);
v___x_2184_ = v___x_2111_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2182_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
lean_dec(v___x_2069_);
lean_dec_ref(v___x_2061_);
lean_dec_ref(v_arg_2060_);
lean_dec_ref(v_arg_2057_);
lean_dec_ref(v_arg_2054_);
lean_dec_ref(v_arg_2051_);
lean_dec_ref(v_arg_2048_);
lean_dec_ref(v_e_2027_);
v_a_2191_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2108_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2108_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_dec(v___x_2069_);
lean_dec_ref(v___x_2061_);
lean_dec_ref(v_arg_2060_);
lean_dec_ref(v_arg_2057_);
lean_dec_ref(v_arg_2054_);
lean_dec_ref(v_arg_2051_);
lean_dec_ref(v_arg_2048_);
lean_dec_ref(v_e_2027_);
v_a_2200_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2087_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2087_);
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
}
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
lean_dec_ref(v___x_2061_);
lean_dec_ref(v_arg_2060_);
lean_dec_ref(v_arg_2057_);
lean_dec_ref(v_arg_2054_);
lean_dec_ref(v_arg_2051_);
lean_dec_ref(v_arg_2048_);
lean_dec_ref(v_e_2027_);
v_a_2209_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2064_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2064_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
}
}
}
}
}
v___jp_2041_:
{
lean_object* v___x_2042_; lean_object* v___x_2044_; 
v___x_2042_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__0));
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v___x_2042_);
v___x_2044_ = v___x_2039_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2042_);
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
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec_ref(v_e_2027_);
v_a_2218_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2036_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2036_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___boxed(lean_object* v_numIndices_2226_, lean_object* v_useDecideBool_2227_, lean_object* v_e_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_){
_start:
{
uint8_t v_useDecideBool_boxed_2237_; lean_object* v_res_2238_; 
v_useDecideBool_boxed_2237_ = lean_unbox(v_useDecideBool_2227_);
v_res_2238_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27(v_numIndices_2226_, v_useDecideBool_boxed_2237_, v_e_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_);
lean_dec(v_a_2235_);
lean_dec_ref(v_a_2234_);
lean_dec(v_a_2233_);
lean_dec_ref(v_a_2232_);
lean_dec(v_a_2231_);
lean_dec_ref(v_a_2230_);
lean_dec(v_a_2229_);
lean_dec(v_numIndices_2226_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(lean_object* v_e_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_){
_start:
{
if (lean_obj_tag(v_e_2242_) == 6)
{
lean_object* v_binderName_2246_; lean_object* v___x_2247_; 
v_binderName_2246_ = lean_ctor_get(v_e_2242_, 0);
lean_inc(v_binderName_2246_);
v___x_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2247_, 0, v_binderName_2246_);
return v___x_2247_;
}
else
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__1));
v___x_2249_ = l_Lean_Core_mkFreshUserName(v___x_2248_, v_a_2243_, v_a_2244_);
return v___x_2249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___boxed(lean_object* v_e_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_e_2250_, v_a_2251_, v_a_2252_);
lean_dec(v_a_2252_);
lean_dec_ref(v_a_2251_);
lean_dec_ref(v_e_2250_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName(lean_object* v_e_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_){
_start:
{
lean_object* v___x_2261_; 
v___x_2261_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_e_2255_, v_a_2258_, v_a_2259_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___boxed(lean_object* v_e_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName(v_e_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
lean_dec(v_a_2266_);
lean_dec_ref(v_a_2265_);
lean_dec(v_a_2264_);
lean_dec_ref(v_a_2263_);
lean_dec_ref(v_e_2262_);
return v_res_2268_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3(void){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2274_ = lean_box(0);
v___x_2275_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__2));
v___x_2276_ = l_Lean_mkConst(v___x_2275_, v___x_2274_);
return v___x_2276_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4(void){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2277_ = lean_unsigned_to_nat(0u);
v___x_2278_ = l_Lean_mkBVar(v___x_2277_);
return v___x_2278_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7(void){
_start:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2283_ = lean_box(0);
v___x_2284_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__6));
v___x_2285_ = l_Lean_mkConst(v___x_2284_, v___x_2283_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27(lean_object* v_numIndices_2289_, uint8_t v_useDecideBool_2290_, lean_object* v_e_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_){
_start:
{
lean_object* v___x_2300_; 
lean_inc_ref(v_e_2291_);
v___x_2300_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2291_, v_a_2296_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2510_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2303_ = v___x_2300_;
v_isShared_2304_ = v_isSharedCheck_2510_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2300_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2510_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2310_; uint8_t v___x_2311_; 
v___x_2310_ = l_Lean_Expr_cleanupAnnotations(v_a_2301_);
v___x_2311_ = l_Lean_Expr_isApp(v___x_2310_);
if (v___x_2311_ == 0)
{
lean_dec_ref(v___x_2310_);
lean_dec_ref(v_e_2291_);
goto v___jp_2305_;
}
else
{
lean_object* v_arg_2312_; lean_object* v___x_2313_; uint8_t v___x_2314_; 
v_arg_2312_ = lean_ctor_get(v___x_2310_, 1);
lean_inc_ref(v_arg_2312_);
v___x_2313_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2310_);
v___x_2314_ = l_Lean_Expr_isApp(v___x_2313_);
if (v___x_2314_ == 0)
{
lean_dec_ref(v___x_2313_);
lean_dec_ref(v_arg_2312_);
lean_dec_ref(v_e_2291_);
goto v___jp_2305_;
}
else
{
lean_object* v_arg_2315_; lean_object* v___x_2316_; uint8_t v___x_2317_; 
v_arg_2315_ = lean_ctor_get(v___x_2313_, 1);
lean_inc_ref(v_arg_2315_);
v___x_2316_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2313_);
v___x_2317_ = l_Lean_Expr_isApp(v___x_2316_);
if (v___x_2317_ == 0)
{
lean_dec_ref(v___x_2316_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v_arg_2312_);
lean_dec_ref(v_e_2291_);
goto v___jp_2305_;
}
else
{
lean_object* v_arg_2318_; lean_object* v___x_2319_; uint8_t v___x_2320_; 
v_arg_2318_ = lean_ctor_get(v___x_2316_, 1);
lean_inc_ref(v_arg_2318_);
v___x_2319_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2316_);
v___x_2320_ = l_Lean_Expr_isApp(v___x_2319_);
if (v___x_2320_ == 0)
{
lean_dec_ref(v___x_2319_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v_arg_2312_);
lean_dec_ref(v_e_2291_);
goto v___jp_2305_;
}
else
{
lean_object* v_arg_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; 
v_arg_2321_ = lean_ctor_get(v___x_2319_, 1);
lean_inc_ref(v_arg_2321_);
v___x_2322_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2319_);
v___x_2323_ = l_Lean_Expr_isApp(v___x_2322_);
if (v___x_2323_ == 0)
{
lean_dec_ref(v___x_2322_);
lean_dec_ref(v_arg_2321_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v_arg_2312_);
lean_dec_ref(v_e_2291_);
goto v___jp_2305_;
}
else
{
lean_object* v_arg_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; uint8_t v___x_2327_; 
v_arg_2324_ = lean_ctor_get(v___x_2322_, 1);
lean_inc_ref(v_arg_2324_);
v___x_2325_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2322_);
v___x_2326_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__4));
v___x_2327_ = l_Lean_Expr_isConstOf(v___x_2325_, v___x_2326_);
if (v___x_2327_ == 0)
{
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_arg_2324_);
lean_dec_ref(v_arg_2321_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v_arg_2312_);
lean_dec_ref(v_e_2291_);
goto v___jp_2305_;
}
else
{
lean_object* v___x_2328_; 
lean_del_object(v___x_2303_);
lean_inc_ref(v_arg_2321_);
v___x_2328_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2289_, v_useDecideBool_2290_, v_arg_2321_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2501_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2331_ = v___x_2328_;
v_isShared_2332_ = v_isSharedCheck_2501_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2328_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2501_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2333_; 
v___x_2333_ = l_Lean_Expr_constLevels_x21(v___x_2325_);
if (lean_obj_tag(v_a_2329_) == 1)
{
lean_object* v_val_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2351_; 
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_e_2291_);
v_val_2334_ = lean_ctor_get(v_a_2329_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v_a_2329_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2336_ = v_a_2329_;
v_isShared_2337_ = v_isSharedCheck_2351_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_val_2334_);
lean_dec(v_a_2329_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2351_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2344_; 
lean_inc(v_val_2334_);
lean_inc_ref(v_arg_2315_);
v___x_2338_ = l_Lean_Expr_app___override(v_arg_2315_, v_val_2334_);
v___x_2339_ = l_Lean_Expr_headBeta(v___x_2338_);
v___x_2340_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__11));
v___x_2341_ = l_Lean_mkConst(v___x_2340_, v___x_2333_);
v___x_2342_ = l_Lean_mkApp6(v___x_2341_, v_arg_2321_, v_arg_2318_, v_val_2334_, v_arg_2324_, v_arg_2315_, v_arg_2312_);
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 0, v___x_2342_);
v___x_2344_ = v___x_2336_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2342_);
v___x_2344_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2348_; 
v___x_2345_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2345_, 0, v___x_2339_);
lean_ctor_set(v___x_2345_, 1, v___x_2344_);
lean_ctor_set_uint8(v___x_2345_, sizeof(void*)*2, v___x_2327_);
v___x_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2345_);
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 0, v___x_2346_);
v___x_2348_ = v___x_2331_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___x_2346_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
else
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
lean_del_object(v___x_2331_);
lean_dec(v_a_2329_);
lean_inc_ref(v_arg_2321_);
v___x_2352_ = l_Lean_mkNot(v_arg_2321_);
v___x_2353_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2289_, v_useDecideBool_2290_, v___x_2352_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2492_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2356_ = v___x_2353_;
v_isShared_2357_ = v_isSharedCheck_2492_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2353_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2492_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
if (lean_obj_tag(v_a_2354_) == 1)
{
lean_object* v_val_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2375_; 
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_e_2291_);
v_val_2358_ = lean_ctor_get(v_a_2354_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v_a_2354_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2360_ = v_a_2354_;
v_isShared_2361_ = v_isSharedCheck_2375_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_val_2358_);
lean_dec(v_a_2354_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2375_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2368_; 
lean_inc(v_val_2358_);
lean_inc_ref(v_arg_2312_);
v___x_2362_ = l_Lean_Expr_app___override(v_arg_2312_, v_val_2358_);
v___x_2363_ = l_Lean_Expr_headBeta(v___x_2362_);
v___x_2364_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__13));
v___x_2365_ = l_Lean_mkConst(v___x_2364_, v___x_2333_);
v___x_2366_ = l_Lean_mkApp6(v___x_2365_, v_arg_2321_, v_arg_2318_, v_val_2358_, v_arg_2324_, v_arg_2315_, v_arg_2312_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 0, v___x_2366_);
v___x_2368_ = v___x_2360_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2366_);
v___x_2368_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2372_; 
v___x_2369_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2369_, 0, v___x_2363_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
lean_ctor_set_uint8(v___x_2369_, sizeof(void*)*2, v___x_2327_);
v___x_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 0, v___x_2370_);
v___x_2372_ = v___x_2356_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2370_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
else
{
lean_object* v___x_2376_; 
lean_del_object(v___x_2356_);
lean_dec(v_a_2354_);
lean_inc(v_a_2298_);
lean_inc_ref(v_a_2297_);
lean_inc(v_a_2296_);
lean_inc_ref(v_a_2295_);
lean_inc(v_a_2294_);
lean_inc_ref(v_a_2293_);
lean_inc(v_a_2292_);
lean_inc_ref(v_arg_2321_);
v___x_2376_ = lean_simp(v_arg_2321_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2483_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2379_ = v___x_2376_;
v_isShared_2380_ = v_isSharedCheck_2483_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2376_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2483_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v_expr_2381_; uint8_t v___x_2382_; 
v_expr_2381_ = lean_ctor_get(v_a_2377_, 0);
v___x_2382_ = lean_expr_eqv(v_expr_2381_, v_arg_2321_);
if (v___x_2382_ == 0)
{
lean_object* v___x_2383_; 
lean_inc_ref(v_expr_2381_);
lean_del_object(v___x_2379_);
v___x_2383_ = l_Lean_Meta_Simp_Result_getProof(v_a_2377_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v_a_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_a_2384_);
lean_dec_ref_known(v___x_2383_, 1);
v___x_2385_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3);
lean_inc_ref(v_expr_2381_);
v___x_2386_ = l_Lean_Expr_app___override(v___x_2385_, v_expr_2381_);
v___x_2387_ = lean_box(0);
v___x_2388_ = l_Lean_Meta_trySynthInstance(v___x_2386_, v___x_2387_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2452_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2391_ = v___x_2388_;
v_isShared_2392_ = v_isSharedCheck_2452_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2388_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2452_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
if (lean_obj_tag(v_a_2389_) == 1)
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2446_; 
lean_del_object(v___x_2391_);
lean_dec_ref(v_e_2291_);
v_a_2393_ = lean_ctor_get(v_a_2389_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v_a_2389_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2395_ = v_a_2389_;
v_isShared_2396_ = v_isSharedCheck_2446_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v_a_2389_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2446_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2397_; 
v___x_2397_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_arg_2315_, v_a_2297_, v_a_2298_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v_a_2398_; lean_object* v___x_2399_; 
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
lean_inc(v_a_2398_);
lean_dec_ref_known(v___x_2397_, 1);
v___x_2399_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_arg_2312_, v_a_2297_, v_a_2298_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2429_; 
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2402_ = v___x_2399_;
v_isShared_2403_ = v_isSharedCheck_2429_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2399_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2429_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; uint8_t v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2422_; 
v___x_2404_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3);
v___x_2405_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4);
lean_inc_n(v_a_2384_, 2);
lean_inc_ref_n(v_expr_2381_, 5);
lean_inc_ref_n(v_arg_2321_, 2);
v___x_2406_ = l_Lean_mkApp4(v___x_2404_, v_arg_2321_, v_expr_2381_, v_a_2384_, v___x_2405_);
lean_inc_ref(v_arg_2315_);
v___x_2407_ = l_Lean_Expr_app___override(v_arg_2315_, v___x_2406_);
v___x_2408_ = l_Lean_Expr_headBeta(v___x_2407_);
v___x_2409_ = 0;
v___x_2410_ = l_Lean_mkLambda(v_a_2398_, v___x_2409_, v_expr_2381_, v___x_2408_);
v___x_2411_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7);
v___x_2412_ = l_Lean_mkApp4(v___x_2411_, v_arg_2321_, v_expr_2381_, v_a_2384_, v___x_2405_);
lean_inc_ref(v_arg_2312_);
v___x_2413_ = l_Lean_Expr_app___override(v_arg_2312_, v___x_2412_);
v___x_2414_ = l_Lean_Expr_headBeta(v___x_2413_);
v___x_2415_ = l_Lean_mkNot(v_expr_2381_);
v___x_2416_ = l_Lean_mkLambda(v_a_2400_, v___x_2409_, v___x_2415_, v___x_2414_);
lean_inc(v_a_2393_);
lean_inc_ref(v_arg_2324_);
v___x_2417_ = l_Lean_mkApp5(v___x_2325_, v_arg_2324_, v_expr_2381_, v_a_2393_, v___x_2410_, v___x_2416_);
v___x_2418_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__9));
v___x_2419_ = l_Lean_mkConst(v___x_2418_, v___x_2333_);
v___x_2420_ = l_Lean_mkApp8(v___x_2419_, v_arg_2324_, v_arg_2321_, v_expr_2381_, v_arg_2318_, v_a_2393_, v_arg_2315_, v_arg_2312_, v_a_2384_);
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 0, v___x_2420_);
v___x_2422_ = v___x_2395_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2420_);
v___x_2422_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2426_; 
v___x_2423_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2423_, 0, v___x_2417_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
lean_ctor_set_uint8(v___x_2423_, sizeof(void*)*2, v___x_2327_);
v___x_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 0, v___x_2424_);
v___x_2426_ = v___x_2402_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2424_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
lean_dec(v_a_2398_);
lean_del_object(v___x_2395_);
lean_dec(v_a_2393_);
lean_dec(v_a_2384_);
lean_dec_ref(v_expr_2381_);
lean_dec(v___x_2333_);
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_arg_2324_);
lean_dec_ref(v_arg_2321_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v_arg_2312_);
v_a_2430_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2399_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2399_);
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
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2445_; 
lean_del_object(v___x_2395_);
lean_dec(v_a_2393_);
lean_dec(v_a_2384_);
lean_dec_ref(v_expr_2381_);
lean_dec(v___x_2333_);
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_arg_2324_);
lean_dec_ref(v_arg_2321_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v_arg_2312_);
v_a_2438_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2440_ = v___x_2397_;
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2397_);
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
else
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2450_; 
lean_dec(v_a_2389_);
lean_dec(v_a_2384_);
lean_dec_ref(v_expr_2381_);
lean_dec(v___x_2333_);
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_arg_2324_);
lean_dec_ref(v_arg_2321_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v_arg_2312_);
v___x_2447_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2447_, 0, v_e_2291_);
lean_ctor_set(v___x_2447_, 1, v___x_2387_);
lean_ctor_set_uint8(v___x_2447_, sizeof(void*)*2, v___x_2327_);
v___x_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
if (v_isShared_2392_ == 0)
{
lean_ctor_set(v___x_2391_, 0, v___x_2448_);
v___x_2450_ = v___x_2391_;
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
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2460_; 
lean_dec(v_a_2384_);
lean_dec_ref(v_expr_2381_);
lean_dec(v___x_2333_);
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_arg_2324_);
lean_dec_ref(v_arg_2321_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v_arg_2312_);
lean_dec_ref(v_e_2291_);
v_a_2453_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2455_ = v___x_2388_;
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2388_);
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
else
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
lean_dec_ref(v_expr_2381_);
lean_dec(v___x_2333_);
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_arg_2324_);
lean_dec_ref(v_arg_2321_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v_arg_2312_);
lean_dec_ref(v_e_2291_);
v_a_2461_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2383_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2383_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
else
{
lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2480_; 
lean_dec(v___x_2333_);
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_arg_2324_);
lean_dec_ref(v_arg_2321_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v_arg_2312_);
v_isSharedCheck_2480_ = !lean_is_exclusive(v_a_2377_);
if (v_isSharedCheck_2480_ == 0)
{
lean_object* v_unused_2481_; lean_object* v_unused_2482_; 
v_unused_2481_ = lean_ctor_get(v_a_2377_, 1);
lean_dec(v_unused_2481_);
v_unused_2482_ = lean_ctor_get(v_a_2377_, 0);
lean_dec(v_unused_2482_);
v___x_2470_ = v_a_2377_;
v_isShared_2471_ = v_isSharedCheck_2480_;
goto v_resetjp_2469_;
}
else
{
lean_dec(v_a_2377_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2480_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2472_; lean_object* v___x_2474_; 
v___x_2472_ = lean_box(0);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 1, v___x_2472_);
lean_ctor_set(v___x_2470_, 0, v_e_2291_);
v___x_2474_ = v___x_2470_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_e_2291_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v___x_2472_);
v___x_2474_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
lean_object* v___x_2475_; lean_object* v___x_2477_; 
lean_ctor_set_uint8(v___x_2474_, sizeof(void*)*2, v___x_2327_);
v___x_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2474_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v___x_2475_);
v___x_2477_ = v___x_2379_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2475_);
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
}
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
lean_dec(v___x_2333_);
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_arg_2324_);
lean_dec_ref(v_arg_2321_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v_arg_2312_);
lean_dec_ref(v_e_2291_);
v_a_2484_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2376_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2376_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
}
}
}
else
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
lean_dec(v___x_2333_);
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_arg_2324_);
lean_dec_ref(v_arg_2321_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v_arg_2312_);
lean_dec_ref(v_e_2291_);
v_a_2493_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2495_ = v___x_2353_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2353_);
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
}
}
else
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2509_; 
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_arg_2324_);
lean_dec_ref(v_arg_2321_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v_arg_2312_);
lean_dec_ref(v_e_2291_);
v_a_2502_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2504_ = v___x_2328_;
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___x_2328_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2507_; 
if (v_isShared_2505_ == 0)
{
v___x_2507_ = v___x_2504_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_a_2502_);
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
}
}
}
v___jp_2305_:
{
lean_object* v___x_2306_; lean_object* v___x_2308_; 
v___x_2306_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__0));
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 0, v___x_2306_);
v___x_2308_ = v___x_2303_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2306_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
else
{
lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2518_; 
lean_dec_ref(v_e_2291_);
v_a_2511_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2513_ = v___x_2300_;
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v___x_2300_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2516_; 
if (v_isShared_2514_ == 0)
{
v___x_2516_ = v___x_2513_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_a_2511_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___boxed(lean_object* v_numIndices_2519_, lean_object* v_useDecideBool_2520_, lean_object* v_e_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_){
_start:
{
uint8_t v_useDecideBool_boxed_2530_; lean_object* v_res_2531_; 
v_useDecideBool_boxed_2530_ = lean_unbox(v_useDecideBool_2520_);
v_res_2531_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27(v_numIndices_2519_, v_useDecideBool_boxed_2530_, v_e_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_);
lean_dec(v_a_2528_);
lean_dec_ref(v_a_2527_);
lean_dec(v_a_2526_);
lean_dec_ref(v_a_2525_);
lean_dec(v_a_2524_);
lean_dec_ref(v_a_2523_);
lean_dec(v_a_2522_);
lean_dec(v_numIndices_2519_);
return v_res_2531_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0(void){
_start:
{
lean_object* v___x_2532_; 
v___x_2532_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_2532_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1(void){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v_s_2535_; 
v___x_2533_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__2, &l_Lean_Meta_SplitIf_getSimpContext___closed__2_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__2);
v___x_2534_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0);
v_s_2535_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_s_2535_, 0, v___x_2534_);
lean_ctor_set(v_s_2535_, 1, v___x_2534_);
lean_ctor_set(v_s_2535_, 2, v___x_2533_);
lean_ctor_set(v_s_2535_, 3, v___x_2533_);
return v_s_2535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(lean_object* v_numIndices_2599_, uint8_t v_useDecide_2600_){
_start:
{
lean_object* v_s_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; uint8_t v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v_s_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v_s_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v_s_2602_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1);
v___x_2603_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__3));
v___x_2604_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__16));
v___x_2605_ = 0;
v___x_2606_ = lean_box(v_useDecide_2600_);
lean_inc(v_numIndices_2599_);
v___x_2607_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___boxed), 11, 2);
lean_closure_set(v___x_2607_, 0, v_numIndices_2599_);
lean_closure_set(v___x_2607_, 1, v___x_2606_);
v___x_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2607_);
v_s_2609_ = l_Lean_Meta_Simp_Simprocs_addCore(v_s_2602_, v___x_2603_, v___x_2604_, v___x_2605_, v___x_2608_);
v___x_2610_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__18));
v___x_2611_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__20));
v___x_2612_ = lean_box(v_useDecide_2600_);
v___x_2613_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___boxed), 11, 2);
lean_closure_set(v___x_2613_, 0, v_numIndices_2599_);
lean_closure_set(v___x_2613_, 1, v___x_2612_);
v___x_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2613_);
v_s_2615_ = l_Lean_Meta_Simp_Simprocs_addCore(v_s_2609_, v___x_2610_, v___x_2611_, v___x_2605_, v___x_2614_);
v___x_2616_ = lean_unsigned_to_nat(1u);
v___x_2617_ = lean_mk_empty_array_with_capacity(v___x_2616_);
v___x_2618_ = lean_array_push(v___x_2617_, v_s_2615_);
v___x_2619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2618_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___boxed(lean_object* v_numIndices_2620_, lean_object* v_useDecide_2621_, lean_object* v_a_2622_){
_start:
{
uint8_t v_useDecide_boxed_2623_; lean_object* v_res_2624_; 
v_useDecide_boxed_2623_ = lean_unbox(v_useDecide_2621_);
v_res_2624_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_numIndices_2620_, v_useDecide_boxed_2623_);
return v_res_2624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs(lean_object* v_numIndices_2625_, uint8_t v_useDecide_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_numIndices_2625_, v_useDecide_2626_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___boxed(lean_object* v_numIndices_2633_, lean_object* v_useDecide_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_){
_start:
{
uint8_t v_useDecide_boxed_2640_; lean_object* v_res_2641_; 
v_useDecide_boxed_2640_ = lean_unbox(v_useDecide_2634_);
v_res_2641_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs(v_numIndices_2633_, v_useDecide_boxed_2640_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_);
lean_dec(v_a_2638_);
lean_dec_ref(v_a_2637_);
lean_dec(v_a_2636_);
lean_dec_ref(v_a_2635_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(uint8_t v_useDecide_2642_, lean_object* v_a_2643_){
_start:
{
lean_object* v_lctx_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v_lctx_2645_ = lean_ctor_get(v_a_2643_, 2);
lean_inc_ref(v_lctx_2645_);
v___x_2646_ = lean_local_ctx_num_indices(v_lctx_2645_);
v___x_2647_ = lean_box(v_useDecide_2642_);
v___x_2648_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___boxed), 11, 2);
lean_closure_set(v___x_2648_, 0, v___x_2646_);
lean_closure_set(v___x_2648_, 1, v___x_2647_);
v___x_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2648_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg___boxed(lean_object* v_useDecide_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_){
_start:
{
uint8_t v_useDecide_boxed_2653_; lean_object* v_res_2654_; 
v_useDecide_boxed_2653_ = lean_unbox(v_useDecide_2650_);
v_res_2654_ = l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(v_useDecide_boxed_2653_, v_a_2651_);
lean_dec_ref(v_a_2651_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f(uint8_t v_useDecide_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(v_useDecide_2655_, v_a_2656_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed(lean_object* v_useDecide_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_){
_start:
{
uint8_t v_useDecide_boxed_2668_; lean_object* v_res_2669_; 
v_useDecide_boxed_2668_ = lean_unbox(v_useDecide_2662_);
v_res_2669_ = l_Lean_Meta_SplitIf_mkDischarge_x3f(v_useDecide_boxed_2668_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_);
lean_dec(v_a_2666_);
lean_dec_ref(v_a_2665_);
lean_dec(v_a_2664_);
lean_dec_ref(v_a_2663_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(lean_object* v_mvarId_2670_, lean_object* v_x_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_){
_start:
{
lean_object* v___x_2677_; 
v___x_2677_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2670_, v_x_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2680_ = v___x_2677_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2677_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2678_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
else
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
v_a_2686_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___x_2677_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2677_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_2694_, lean_object* v_x_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2694_, v_x_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0(lean_object* v_00_u03b1_2702_, lean_object* v_mvarId_2703_, lean_object* v_x_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v___x_2710_; 
v___x_2710_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2703_, v_x_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___boxed(lean_object* v_00_u03b1_2711_, lean_object* v_mvarId_2712_, lean_object* v_x_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0(v_00_u03b1_2711_, v_mvarId_2712_, v_x_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
return v_res_2719_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2721_ = ((lean_object*)(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__0));
v___x_2722_ = l_Lean_stringToMessageData(v___x_2721_);
return v___x_2722_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2724_ = ((lean_object*)(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__2));
v___x_2725_ = l_Lean_stringToMessageData(v___x_2724_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0(lean_object* v_e_2726_, lean_object* v_mvarId_2727_, lean_object* v_hName_x3f_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
lean_object* v___x_2737_; lean_object* v_a_2738_; lean_object* v___x_2739_; 
v___x_2737_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_2726_, v___y_2730_);
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
lean_inc_n(v_a_2738_, 2);
lean_dec_ref(v___x_2737_);
v___x_2739_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(v_a_2738_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v_a_2740_; 
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
lean_inc(v_a_2740_);
lean_dec_ref_known(v___x_2739_, 1);
if (lean_obj_tag(v_a_2740_) == 1)
{
lean_object* v_val_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2816_; 
lean_dec(v_a_2738_);
v_val_2741_ = lean_ctor_get(v_a_2740_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v_a_2740_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2743_ = v_a_2740_;
v_isShared_2744_ = v_isSharedCheck_2816_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_val_2741_);
lean_dec(v_a_2740_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2816_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v_fst_2745_; lean_object* v_snd_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2815_; 
v_fst_2745_ = lean_ctor_get(v_val_2741_, 0);
v_snd_2746_ = lean_ctor_get(v_val_2741_, 1);
v_isSharedCheck_2815_ = !lean_is_exclusive(v_val_2741_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2748_ = v_val_2741_;
v_isShared_2749_ = v_isSharedCheck_2815_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_snd_2746_);
lean_inc(v_fst_2745_);
lean_dec(v_val_2741_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2815_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v_hName_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; 
if (lean_obj_tag(v_hName_x3f_2728_) == 0)
{
lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2803_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__1));
v___x_2804_ = l_Lean_Core_mkFreshUserName(v___x_2803_, v___y_2731_, v___y_2732_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v_a_2805_; 
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v_a_2805_);
lean_dec_ref_known(v___x_2804_, 1);
v_hName_2777_ = v_a_2805_;
v___y_2778_ = v___y_2729_;
v___y_2779_ = v___y_2730_;
v___y_2780_ = v___y_2731_;
v___y_2781_ = v___y_2732_;
goto v___jp_2776_;
}
else
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2813_; 
lean_del_object(v___x_2748_);
lean_dec(v_snd_2746_);
lean_dec(v_fst_2745_);
lean_del_object(v___x_2743_);
lean_dec(v_mvarId_2727_);
v_a_2806_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2808_ = v___x_2804_;
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2804_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2811_; 
if (v_isShared_2809_ == 0)
{
v___x_2811_ = v___x_2808_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_a_2806_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
}
else
{
lean_object* v_val_2814_; 
v_val_2814_ = lean_ctor_get(v_hName_x3f_2728_, 0);
lean_inc(v_val_2814_);
lean_dec_ref_known(v_hName_x3f_2728_, 1);
v_hName_2777_ = v_val_2814_;
v___y_2778_ = v___y_2729_;
v___y_2779_ = v___y_2730_;
v___y_2780_ = v___y_2731_;
v___y_2781_ = v___y_2732_;
goto v___jp_2776_;
}
v___jp_2750_:
{
lean_object* v___x_2756_; 
v___x_2756_ = l_Lean_MVarId_byCasesDec(v_mvarId_2727_, v_fst_2745_, v_snd_2746_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2767_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2759_ = v___x_2756_;
v_isShared_2760_ = v_isSharedCheck_2767_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2756_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2767_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 0, v_a_2757_);
v___x_2762_ = v___x_2743_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2757_);
v___x_2762_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
lean_object* v___x_2764_; 
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 0, v___x_2762_);
v___x_2764_ = v___x_2759_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2762_);
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
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_del_object(v___x_2743_);
v_a_2768_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2756_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2756_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
v___jp_2776_:
{
lean_object* v_options_2782_; uint8_t v_hasTrace_2783_; 
v_options_2782_ = lean_ctor_get(v___y_2780_, 1);
v_hasTrace_2783_ = lean_ctor_get_uint8(v_options_2782_, sizeof(void*)*1);
if (v_hasTrace_2783_ == 0)
{
lean_del_object(v___x_2748_);
v___y_2751_ = v_hName_2777_;
v___y_2752_ = v___y_2778_;
v___y_2753_ = v___y_2779_;
v___y_2754_ = v___y_2780_;
v___y_2755_ = v___y_2781_;
goto v___jp_2750_;
}
else
{
lean_object* v_toCold_2784_; lean_object* v_inheritedTraceOptions_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; uint8_t v___x_2788_; 
v_toCold_2784_ = lean_ctor_get(v___y_2780_, 0);
v_inheritedTraceOptions_2785_ = lean_ctor_get(v_toCold_2784_, 4);
v___x_2786_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9));
v___x_2787_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10);
v___x_2788_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2785_, v_options_2782_, v___x_2787_);
if (v___x_2788_ == 0)
{
lean_del_object(v___x_2748_);
v___y_2751_ = v_hName_2777_;
v___y_2752_ = v___y_2778_;
v___y_2753_ = v___y_2779_;
v___y_2754_ = v___y_2780_;
v___y_2755_ = v___y_2781_;
goto v___jp_2750_;
}
else
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2792_; 
v___x_2789_ = lean_obj_once(&l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1, &l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1_once, _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1);
lean_inc(v_snd_2746_);
v___x_2790_ = l_Lean_MessageData_ofExpr(v_snd_2746_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set_tag(v___x_2748_, 7);
lean_ctor_set(v___x_2748_, 1, v___x_2790_);
lean_ctor_set(v___x_2748_, 0, v___x_2789_);
v___x_2792_ = v___x_2748_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2789_);
lean_ctor_set(v_reuseFailAlloc_2802_, 1, v___x_2790_);
v___x_2792_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
lean_object* v___x_2793_; 
v___x_2793_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_2786_, v___x_2792_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_dec_ref_known(v___x_2793_, 1);
v___y_2751_ = v_hName_2777_;
v___y_2752_ = v___y_2778_;
v___y_2753_ = v___y_2779_;
v___y_2754_ = v___y_2780_;
v___y_2755_ = v___y_2781_;
goto v___jp_2750_;
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
lean_dec(v_hName_2777_);
lean_dec(v_snd_2746_);
lean_dec(v_fst_2745_);
lean_del_object(v___x_2743_);
lean_dec(v_mvarId_2727_);
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2793_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2793_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2794_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
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
lean_object* v_options_2817_; uint8_t v_hasTrace_2818_; 
lean_dec(v_a_2740_);
lean_dec(v_hName_x3f_2728_);
lean_dec(v_mvarId_2727_);
v_options_2817_ = lean_ctor_get(v___y_2731_, 1);
v_hasTrace_2818_ = lean_ctor_get_uint8(v_options_2817_, sizeof(void*)*1);
if (v_hasTrace_2818_ == 0)
{
lean_dec(v_a_2738_);
goto v___jp_2734_;
}
else
{
lean_object* v_toCold_2819_; lean_object* v_inheritedTraceOptions_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; uint8_t v___x_2823_; 
v_toCold_2819_ = lean_ctor_get(v___y_2731_, 0);
v_inheritedTraceOptions_2820_ = lean_ctor_get(v_toCold_2819_, 4);
v___x_2821_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9));
v___x_2822_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10);
v___x_2823_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2820_, v_options_2817_, v___x_2822_);
if (v___x_2823_ == 0)
{
lean_dec(v_a_2738_);
goto v___jp_2734_;
}
else
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2824_ = lean_obj_once(&l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3, &l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3_once, _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3);
v___x_2825_ = l_Lean_indentExpr(v_a_2738_);
v___x_2826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2824_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
v___x_2827_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_2821_, v___x_2826_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_dec_ref_known(v___x_2827_, 1);
goto v___jp_2734_;
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2827_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2827_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
lean_dec(v_a_2738_);
lean_dec(v_hName_x3f_2728_);
lean_dec(v_mvarId_2727_);
v_a_2836_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2838_ = v___x_2739_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2739_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
if (v_isShared_2839_ == 0)
{
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_a_2836_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
v___jp_2734_:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2735_ = lean_box(0);
v___x_2736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2735_);
return v___x_2736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___boxed(lean_object* v_e_2844_, lean_object* v_mvarId_2845_, lean_object* v_hName_x3f_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0(v_e_2844_, v_mvarId_2845_, v_hName_x3f_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f(lean_object* v_mvarId_2853_, lean_object* v_e_2854_, lean_object* v_hName_x3f_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_){
_start:
{
lean_object* v___f_2861_; lean_object* v___x_2862_; 
lean_inc(v_mvarId_2853_);
v___f_2861_ = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2861_, 0, v_e_2854_);
lean_closure_set(v___f_2861_, 1, v_mvarId_2853_);
lean_closure_set(v___f_2861_, 2, v_hName_x3f_2855_);
v___x_2862_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2853_, v___f_2861_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___boxed(lean_object* v_mvarId_2863_, lean_object* v_e_2864_, lean_object* v_hName_x3f_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(v_mvarId_2863_, v_e_2864_, v_hName_x3f_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
lean_dec(v_a_2869_);
lean_dec_ref(v_a_2868_);
lean_dec(v_a_2867_);
lean_dec_ref(v_a_2866_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0(lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v_lctx_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v_lctx_2877_ = lean_ctor_get(v___y_2872_, 2);
lean_inc_ref(v_lctx_2877_);
lean_dec_ref(v___y_2872_);
v___x_2878_ = lean_local_ctx_num_indices(v_lctx_2877_);
v___x_2879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0___boxed(lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0(v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec(v___y_2881_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(lean_object* v_mvarId_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_){
_start:
{
lean_object* v___f_2893_; lean_object* v___x_2894_; 
v___f_2893_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___closed__0));
v___x_2894_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2887_, v___f_2893_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___boxed(lean_object* v_mvarId_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(v_mvarId_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_);
lean_dec(v_a_2899_);
lean_dec_ref(v_a_2898_);
lean_dec(v_a_2897_);
lean_dec_ref(v_a_2896_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_simpIfTarget_spec__0(lean_object* v_msg_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_){
_start:
{
lean_object* v___f_2909_; lean_object* v___x_1602__overap_2910_; lean_object* v___x_2911_; 
v___f_2909_ = ((lean_object*)(l_panic___at___00Lean_Meta_simpIfTarget_spec__0___closed__0));
v___x_1602__overap_2910_ = lean_panic_fn_borrowed(v___f_2909_, v_msg_2903_);
lean_inc(v___y_2907_);
lean_inc_ref(v___y_2906_);
lean_inc(v___y_2905_);
lean_inc_ref(v___y_2904_);
v___x_2911_ = lean_apply_5(v___x_1602__overap_2910_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, lean_box(0));
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_simpIfTarget_spec__0___boxed(lean_object* v_msg_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v_msg_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
return v_res_2918_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(lean_object* v_opts_2919_, lean_object* v_opt_2920_){
_start:
{
lean_object* v_name_2921_; lean_object* v_defValue_2922_; lean_object* v_map_2923_; lean_object* v___x_2924_; 
v_name_2921_ = lean_ctor_get(v_opt_2920_, 0);
v_defValue_2922_ = lean_ctor_get(v_opt_2920_, 1);
v_map_2923_ = lean_ctor_get(v_opts_2919_, 0);
v___x_2924_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2923_, v_name_2921_);
if (lean_obj_tag(v___x_2924_) == 0)
{
uint8_t v___x_2925_; 
v___x_2925_ = lean_unbox(v_defValue_2922_);
return v___x_2925_;
}
else
{
lean_object* v_val_2926_; 
v_val_2926_ = lean_ctor_get(v___x_2924_, 0);
lean_inc(v_val_2926_);
lean_dec_ref_known(v___x_2924_, 1);
if (lean_obj_tag(v_val_2926_) == 1)
{
uint8_t v_v_2927_; 
v_v_2927_ = lean_ctor_get_uint8(v_val_2926_, 0);
lean_dec_ref_known(v_val_2926_, 0);
return v_v_2927_;
}
else
{
uint8_t v___x_2928_; 
lean_dec(v_val_2926_);
v___x_2928_ = lean_unbox(v_defValue_2922_);
return v___x_2928_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1___boxed(lean_object* v_opts_2929_, lean_object* v_opt_2930_){
_start:
{
uint8_t v_res_2931_; lean_object* v_r_2932_; 
v_res_2931_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v_opts_2929_, v_opt_2930_);
lean_dec_ref(v_opt_2930_);
lean_dec_ref(v_opts_2929_);
v_r_2932_ = lean_box(v_res_2931_);
return v_r_2932_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__0(void){
_start:
{
lean_object* v___x_2933_; 
v___x_2933_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2933_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__1(void){
_start:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2934_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__0, &l_Lean_Meta_simpIfTarget___closed__0_once, _init_l_Lean_Meta_simpIfTarget___closed__0);
v___x_2935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2934_);
return v___x_2935_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__2(void){
_start:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2936_ = lean_unsigned_to_nat(0u);
v___x_2937_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__1, &l_Lean_Meta_simpIfTarget___closed__1_once, _init_l_Lean_Meta_simpIfTarget___closed__1);
v___x_2938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
lean_ctor_set(v___x_2938_, 1, v___x_2936_);
return v___x_2938_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__3(void){
_start:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2939_ = lean_unsigned_to_nat(32u);
v___x_2940_ = lean_mk_empty_array_with_capacity(v___x_2939_);
v___x_2941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
return v___x_2941_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__4(void){
_start:
{
size_t v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2942_ = ((size_t)5ULL);
v___x_2943_ = lean_unsigned_to_nat(0u);
v___x_2944_ = lean_unsigned_to_nat(32u);
v___x_2945_ = lean_mk_empty_array_with_capacity(v___x_2944_);
v___x_2946_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__3, &l_Lean_Meta_simpIfTarget___closed__3_once, _init_l_Lean_Meta_simpIfTarget___closed__3);
v___x_2947_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2947_, 0, v___x_2946_);
lean_ctor_set(v___x_2947_, 1, v___x_2945_);
lean_ctor_set(v___x_2947_, 2, v___x_2943_);
lean_ctor_set(v___x_2947_, 3, v___x_2943_);
lean_ctor_set_usize(v___x_2947_, 4, v___x_2942_);
return v___x_2947_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__5(void){
_start:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2948_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__4, &l_Lean_Meta_simpIfTarget___closed__4_once, _init_l_Lean_Meta_simpIfTarget___closed__4);
v___x_2949_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__1, &l_Lean_Meta_simpIfTarget___closed__1_once, _init_l_Lean_Meta_simpIfTarget___closed__1);
v___x_2950_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
lean_ctor_set(v___x_2950_, 1, v___x_2949_);
lean_ctor_set(v___x_2950_, 2, v___x_2949_);
lean_ctor_set(v___x_2950_, 3, v___x_2948_);
return v___x_2950_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__6(void){
_start:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2951_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__5, &l_Lean_Meta_simpIfTarget___closed__5_once, _init_l_Lean_Meta_simpIfTarget___closed__5);
v___x_2952_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__2, &l_Lean_Meta_simpIfTarget___closed__2_once, _init_l_Lean_Meta_simpIfTarget___closed__2);
v___x_2953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2952_);
lean_ctor_set(v___x_2953_, 1, v___x_2951_);
return v___x_2953_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__10(void){
_start:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2957_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__9));
v___x_2958_ = lean_unsigned_to_nat(78u);
v___x_2959_ = lean_unsigned_to_nat(289u);
v___x_2960_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__8));
v___x_2961_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_2962_ = l_mkPanicMessageWithDecl(v___x_2961_, v___x_2960_, v___x_2959_, v___x_2958_, v___x_2957_);
return v___x_2962_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__12(void){
_start:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2965_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__9));
v___x_2966_ = lean_unsigned_to_nat(128u);
v___x_2967_ = lean_unsigned_to_nat(293u);
v___x_2968_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__8));
v___x_2969_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_2970_ = l_mkPanicMessageWithDecl(v___x_2969_, v___x_2968_, v___x_2967_, v___x_2966_, v___x_2965_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfTarget(lean_object* v_mvarId_2971_, uint8_t v_useDecide_2972_, uint8_t v_useNewSemantics_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_){
_start:
{
if (v_useNewSemantics_2973_ == 0)
{
lean_object* v_options_3026_; lean_object* v___x_3027_; uint8_t v___x_3028_; 
v_options_3026_ = lean_ctor_get(v_a_2976_, 1);
v___x_3027_ = l_Lean_Meta_backward_split;
v___x_3028_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v_options_3026_, v___x_3027_);
if (v___x_3028_ == 0)
{
goto v___jp_2979_;
}
else
{
lean_object* v___x_3029_; 
v___x_3029_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_object* v_a_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_a_3030_);
lean_dec_ref_known(v___x_3029_, 1);
v___x_3031_ = lean_box(v_useDecide_2972_);
v___x_3032_ = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed), 6, 1);
lean_closure_set(v___x_3032_, 0, v___x_3031_);
lean_inc(v_mvarId_2971_);
v___x_3033_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2971_, v___x_3032_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_object* v_a_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
lean_inc(v_a_3034_);
lean_dec_ref_known(v___x_3033_, 1);
v___x_3035_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__11));
v___x_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3036_, 0, v_a_3034_);
v___x_3037_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__6, &l_Lean_Meta_simpIfTarget___closed__6_once, _init_l_Lean_Meta_simpIfTarget___closed__6);
v___x_3038_ = l_Lean_Meta_simpTarget(v_mvarId_2971_, v_a_3030_, v___x_3035_, v___x_3036_, v_useNewSemantics_2973_, v___x_3037_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3050_; 
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3041_ = v___x_3038_;
v_isShared_3042_ = v_isSharedCheck_3050_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_3038_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3050_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v_fst_3043_; 
v_fst_3043_ = lean_ctor_get(v_a_3039_, 0);
lean_inc(v_fst_3043_);
lean_dec(v_a_3039_);
if (lean_obj_tag(v_fst_3043_) == 1)
{
lean_object* v_val_3044_; lean_object* v___x_3046_; 
v_val_3044_ = lean_ctor_get(v_fst_3043_, 0);
lean_inc(v_val_3044_);
lean_dec_ref_known(v_fst_3043_, 1);
if (v_isShared_3042_ == 0)
{
lean_ctor_set(v___x_3041_, 0, v_val_3044_);
v___x_3046_ = v___x_3041_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_val_3044_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
else
{
lean_object* v___x_3048_; lean_object* v___x_3049_; 
lean_dec(v_fst_3043_);
lean_del_object(v___x_3041_);
v___x_3048_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__12, &l_Lean_Meta_simpIfTarget___closed__12_once, _init_l_Lean_Meta_simpIfTarget___closed__12);
v___x_3049_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3048_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_);
return v___x_3049_;
}
}
}
else
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
v_a_3051_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_3038_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3038_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
else
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3066_; 
lean_dec(v_a_3030_);
lean_dec(v_mvarId_2971_);
v_a_3059_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3061_ = v___x_3033_;
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_3033_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3064_; 
if (v_isShared_3062_ == 0)
{
v___x_3064_ = v___x_3061_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_a_3059_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
else
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
lean_dec(v_mvarId_2971_);
v_a_3067_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3069_ = v___x_3029_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_3029_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3067_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
}
}
else
{
goto v___jp_2979_;
}
v___jp_2979_:
{
lean_object* v___x_2980_; 
v___x_2980_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_2974_, v_a_2976_, v_a_2977_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v___x_2982_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref_known(v___x_2980_, 1);
lean_inc(v_mvarId_2971_);
v___x_2982_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(v_mvarId_2971_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v___x_2984_; lean_object* v_a_2985_; lean_object* v___x_2986_; uint8_t v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2983_);
lean_dec_ref_known(v___x_2982_, 1);
v___x_2984_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_a_2983_, v_useDecide_2972_);
v_a_2985_ = lean_ctor_get(v___x_2984_, 0);
lean_inc(v_a_2985_);
lean_dec_ref(v___x_2984_);
v___x_2986_ = lean_box(0);
v___x_2987_ = 0;
v___x_2988_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__6, &l_Lean_Meta_simpIfTarget___closed__6_once, _init_l_Lean_Meta_simpIfTarget___closed__6);
v___x_2989_ = l_Lean_Meta_simpTarget(v_mvarId_2971_, v_a_2981_, v_a_2985_, v___x_2986_, v___x_2987_, v___x_2988_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3001_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2992_ = v___x_2989_;
v_isShared_2993_ = v_isSharedCheck_3001_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2989_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3001_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v_fst_2994_; 
v_fst_2994_ = lean_ctor_get(v_a_2990_, 0);
lean_inc(v_fst_2994_);
lean_dec(v_a_2990_);
if (lean_obj_tag(v_fst_2994_) == 1)
{
lean_object* v_val_2995_; lean_object* v___x_2997_; 
v_val_2995_ = lean_ctor_get(v_fst_2994_, 0);
lean_inc(v_val_2995_);
lean_dec_ref_known(v_fst_2994_, 1);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 0, v_val_2995_);
v___x_2997_ = v___x_2992_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_val_2995_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
else
{
lean_object* v___x_2999_; lean_object* v___x_3000_; 
lean_dec(v_fst_2994_);
lean_del_object(v___x_2992_);
v___x_2999_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__10, &l_Lean_Meta_simpIfTarget___closed__10_once, _init_l_Lean_Meta_simpIfTarget___closed__10);
v___x_3000_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_2999_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_);
return v___x_3000_;
}
}
}
else
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3009_; 
v_a_3002_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3004_ = v___x_2989_;
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_2989_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3007_; 
if (v_isShared_3005_ == 0)
{
v___x_3007_ = v___x_3004_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_a_3002_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
else
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3017_; 
lean_dec(v_a_2981_);
lean_dec(v_mvarId_2971_);
v_a_3010_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3012_ = v___x_2982_;
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_2982_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
if (v_isShared_3013_ == 0)
{
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_a_3010_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
}
else
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
lean_dec(v_mvarId_2971_);
v_a_3018_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v___x_2980_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_2980_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3018_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfTarget___boxed(lean_object* v_mvarId_3075_, lean_object* v_useDecide_3076_, lean_object* v_useNewSemantics_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_){
_start:
{
uint8_t v_useDecide_boxed_3083_; uint8_t v_useNewSemantics_boxed_3084_; lean_object* v_res_3085_; 
v_useDecide_boxed_3083_ = lean_unbox(v_useDecide_3076_);
v_useNewSemantics_boxed_3084_ = lean_unbox(v_useNewSemantics_3077_);
v_res_3085_ = l_Lean_Meta_simpIfTarget(v_mvarId_3075_, v_useDecide_boxed_3083_, v_useNewSemantics_boxed_3084_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_);
lean_dec(v_a_3081_);
lean_dec_ref(v_a_3080_);
lean_dec(v_a_3079_);
lean_dec_ref(v_a_3078_);
return v_res_3085_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfLocalDecl___closed__1(void){
_start:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3087_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__9));
v___x_3088_ = lean_unsigned_to_nat(93u);
v___x_3089_ = lean_unsigned_to_nat(305u);
v___x_3090_ = ((lean_object*)(l_Lean_Meta_simpIfLocalDecl___closed__0));
v___x_3091_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_3092_ = l_mkPanicMessageWithDecl(v___x_3091_, v___x_3090_, v___x_3089_, v___x_3088_, v___x_3087_);
return v___x_3092_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfLocalDecl___closed__2(void){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3093_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__9));
v___x_3094_ = lean_unsigned_to_nat(133u);
v___x_3095_ = lean_unsigned_to_nat(309u);
v___x_3096_ = ((lean_object*)(l_Lean_Meta_simpIfLocalDecl___closed__0));
v___x_3097_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_3098_ = l_mkPanicMessageWithDecl(v___x_3097_, v___x_3096_, v___x_3095_, v___x_3094_, v___x_3093_);
return v___x_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfLocalDecl(lean_object* v_mvarId_3099_, lean_object* v_fvarId_3100_, uint8_t v_useNewSemantics_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_){
_start:
{
if (v_useNewSemantics_3101_ == 0)
{
lean_object* v_options_3155_; lean_object* v___x_3156_; uint8_t v___x_3157_; 
v_options_3155_ = lean_ctor_get(v_a_3104_, 1);
v___x_3156_ = l_Lean_Meta_backward_split;
v___x_3157_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v_options_3155_, v___x_3156_);
if (v___x_3157_ == 0)
{
goto v___jp_3107_;
}
else
{
lean_object* v___x_3158_; 
v___x_3158_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v_a_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
lean_inc(v_a_3159_);
lean_dec_ref_known(v___x_3158_, 1);
v___x_3160_ = lean_box(v_useNewSemantics_3101_);
v___x_3161_ = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed), 6, 1);
lean_closure_set(v___x_3161_, 0, v___x_3160_);
lean_inc(v_mvarId_3099_);
v___x_3162_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_3099_, v___x_3161_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_a_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_a_3163_);
lean_dec_ref_known(v___x_3162_, 1);
v___x_3164_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__11));
v___x_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3165_, 0, v_a_3163_);
v___x_3166_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__6, &l_Lean_Meta_simpIfTarget___closed__6_once, _init_l_Lean_Meta_simpIfTarget___closed__6);
v___x_3167_ = l_Lean_Meta_simpLocalDecl(v_mvarId_3099_, v_fvarId_3100_, v_a_3159_, v___x_3164_, v___x_3165_, v_useNewSemantics_3101_, v___x_3166_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3180_; 
v_a_3168_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3170_ = v___x_3167_;
v_isShared_3171_ = v_isSharedCheck_3180_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3167_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3180_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v_fst_3172_; 
v_fst_3172_ = lean_ctor_get(v_a_3168_, 0);
lean_inc(v_fst_3172_);
lean_dec(v_a_3168_);
if (lean_obj_tag(v_fst_3172_) == 1)
{
lean_object* v_val_3173_; lean_object* v_snd_3174_; lean_object* v___x_3176_; 
v_val_3173_ = lean_ctor_get(v_fst_3172_, 0);
lean_inc(v_val_3173_);
lean_dec_ref_known(v_fst_3172_, 1);
v_snd_3174_ = lean_ctor_get(v_val_3173_, 1);
lean_inc(v_snd_3174_);
lean_dec(v_val_3173_);
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 0, v_snd_3174_);
v___x_3176_ = v___x_3170_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_snd_3174_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
else
{
lean_object* v___x_3178_; lean_object* v___x_3179_; 
lean_dec(v_fst_3172_);
lean_del_object(v___x_3170_);
v___x_3178_ = lean_obj_once(&l_Lean_Meta_simpIfLocalDecl___closed__2, &l_Lean_Meta_simpIfLocalDecl___closed__2_once, _init_l_Lean_Meta_simpIfLocalDecl___closed__2);
v___x_3179_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3178_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_);
return v___x_3179_;
}
}
}
else
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
v_a_3181_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___x_3167_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3167_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3186_; 
if (v_isShared_3184_ == 0)
{
v___x_3186_ = v___x_3183_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3181_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
}
else
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
lean_dec(v_a_3159_);
lean_dec(v_fvarId_3100_);
lean_dec(v_mvarId_3099_);
v_a_3189_ = lean_ctor_get(v___x_3162_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_3162_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3162_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_3189_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
else
{
lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3204_; 
lean_dec(v_fvarId_3100_);
lean_dec(v_mvarId_3099_);
v_a_3197_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_3158_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3158_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
if (v_isShared_3200_ == 0)
{
v___x_3202_ = v___x_3199_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_a_3197_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
}
else
{
goto v___jp_3107_;
}
v___jp_3107_:
{
lean_object* v___x_3108_; 
v___x_3108_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_3102_, v_a_3104_, v_a_3105_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v_a_3109_; lean_object* v___x_3110_; 
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
lean_inc(v_a_3109_);
lean_dec_ref_known(v___x_3108_, 1);
lean_inc(v_mvarId_3099_);
v___x_3110_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(v_mvarId_3099_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v_a_3111_; uint8_t v___x_3112_; lean_object* v___x_3113_; lean_object* v_a_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v_a_3111_ = lean_ctor_get(v___x_3110_, 0);
lean_inc(v_a_3111_);
lean_dec_ref_known(v___x_3110_, 1);
v___x_3112_ = 0;
v___x_3113_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_a_3111_, v___x_3112_);
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_a_3114_);
lean_dec_ref(v___x_3113_);
v___x_3115_ = lean_box(0);
v___x_3116_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__6, &l_Lean_Meta_simpIfTarget___closed__6_once, _init_l_Lean_Meta_simpIfTarget___closed__6);
v___x_3117_ = l_Lean_Meta_simpLocalDecl(v_mvarId_3099_, v_fvarId_3100_, v_a_3109_, v_a_3114_, v___x_3115_, v___x_3112_, v___x_3116_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3130_; 
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3120_ = v___x_3117_;
v_isShared_3121_ = v_isSharedCheck_3130_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3117_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3130_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v_fst_3122_; 
v_fst_3122_ = lean_ctor_get(v_a_3118_, 0);
lean_inc(v_fst_3122_);
lean_dec(v_a_3118_);
if (lean_obj_tag(v_fst_3122_) == 1)
{
lean_object* v_val_3123_; lean_object* v_snd_3124_; lean_object* v___x_3126_; 
v_val_3123_ = lean_ctor_get(v_fst_3122_, 0);
lean_inc(v_val_3123_);
lean_dec_ref_known(v_fst_3122_, 1);
v_snd_3124_ = lean_ctor_get(v_val_3123_, 1);
lean_inc(v_snd_3124_);
lean_dec(v_val_3123_);
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 0, v_snd_3124_);
v___x_3126_ = v___x_3120_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_snd_3124_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
else
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
lean_dec(v_fst_3122_);
lean_del_object(v___x_3120_);
v___x_3128_ = lean_obj_once(&l_Lean_Meta_simpIfLocalDecl___closed__1, &l_Lean_Meta_simpIfLocalDecl___closed__1_once, _init_l_Lean_Meta_simpIfLocalDecl___closed__1);
v___x_3129_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3128_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_);
return v___x_3129_;
}
}
}
else
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
v_a_3131_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_3117_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3117_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
else
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3146_; 
lean_dec(v_a_3109_);
lean_dec(v_fvarId_3100_);
lean_dec(v_mvarId_3099_);
v_a_3139_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3141_ = v___x_3110_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3110_);
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
else
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
lean_dec(v_fvarId_3100_);
lean_dec(v_mvarId_3099_);
v_a_3147_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3149_ = v___x_3108_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3108_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3152_; 
if (v_isShared_3150_ == 0)
{
v___x_3152_ = v___x_3149_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3147_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfLocalDecl___boxed(lean_object* v_mvarId_3205_, lean_object* v_fvarId_3206_, lean_object* v_useNewSemantics_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_){
_start:
{
uint8_t v_useNewSemantics_boxed_3213_; lean_object* v_res_3214_; 
v_useNewSemantics_boxed_3213_ = lean_unbox(v_useNewSemantics_3207_);
v_res_3214_ = l_Lean_Meta_simpIfLocalDecl(v_mvarId_3205_, v_fvarId_3206_, v_useNewSemantics_boxed_3213_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_);
lean_dec(v_a_3211_);
lean_dec_ref(v_a_3210_);
lean_dec(v_a_3209_);
lean_dec_ref(v_a_3208_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(lean_object* v_x_x3f_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
lean_object* v___x_3221_; 
v___x_3221_ = l_Lean_Meta_saveState___redArg(v___y_3217_, v___y_3219_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3266_; 
v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3224_ = v___x_3221_;
v_isShared_3225_ = v_isSharedCheck_3266_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_a_3222_);
lean_dec(v___x_3221_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3266_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___y_3227_; uint8_t v___y_3228_; lean_object* v_a_3250_; lean_object* v___x_3253_; 
lean_inc(v___y_3219_);
lean_inc_ref(v___y_3218_);
lean_inc(v___y_3217_);
lean_inc_ref(v___y_3216_);
v___x_3253_ = lean_apply_5(v_x_x3f_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, lean_box(0));
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v_a_3254_; 
v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
lean_inc(v_a_3254_);
if (lean_obj_tag(v_a_3254_) == 0)
{
lean_object* v___x_3255_; 
lean_dec_ref_known(v___x_3253_, 1);
v___x_3255_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3222_, v___y_3217_, v___y_3219_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3262_; 
lean_del_object(v___x_3224_);
lean_dec(v_a_3222_);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3262_ == 0)
{
lean_object* v_unused_3263_; 
v_unused_3263_ = lean_ctor_get(v___x_3255_, 0);
lean_dec(v_unused_3263_);
v___x_3257_ = v___x_3255_;
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
else
{
lean_dec(v___x_3255_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3258_ == 0)
{
lean_ctor_set(v___x_3257_, 0, v_a_3254_);
v___x_3260_ = v___x_3257_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3254_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
else
{
lean_object* v_a_3264_; 
v_a_3264_ = lean_ctor_get(v___x_3255_, 0);
lean_inc(v_a_3264_);
lean_dec_ref_known(v___x_3255_, 1);
v_a_3250_ = v_a_3264_;
goto v___jp_3249_;
}
}
else
{
lean_dec_ref_known(v_a_3254_, 1);
lean_del_object(v___x_3224_);
lean_dec(v_a_3222_);
return v___x_3253_;
}
}
else
{
lean_object* v_a_3265_; 
v_a_3265_ = lean_ctor_get(v___x_3253_, 0);
lean_inc(v_a_3265_);
lean_dec_ref_known(v___x_3253_, 1);
v_a_3250_ = v_a_3265_;
goto v___jp_3249_;
}
v___jp_3226_:
{
if (v___y_3228_ == 0)
{
lean_object* v___x_3229_; 
lean_del_object(v___x_3224_);
v___x_3229_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3222_, v___y_3217_, v___y_3219_);
lean_dec(v_a_3222_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3236_; 
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3236_ == 0)
{
lean_object* v_unused_3237_; 
v_unused_3237_ = lean_ctor_get(v___x_3229_, 0);
lean_dec(v_unused_3237_);
v___x_3231_ = v___x_3229_;
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
else
{
lean_dec(v___x_3229_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3234_; 
if (v_isShared_3232_ == 0)
{
lean_ctor_set_tag(v___x_3231_, 1);
lean_ctor_set(v___x_3231_, 0, v___y_3227_);
v___x_3234_ = v___x_3231_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v___y_3227_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
}
else
{
lean_object* v_a_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3245_; 
lean_dec_ref(v___y_3227_);
v_a_3238_ = lean_ctor_get(v___x_3229_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3240_ = v___x_3229_;
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_a_3238_);
lean_dec(v___x_3229_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3243_; 
if (v_isShared_3241_ == 0)
{
v___x_3243_ = v___x_3240_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_a_3238_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
return v___x_3243_;
}
}
}
}
else
{
lean_object* v___x_3247_; 
lean_dec(v_a_3222_);
if (v_isShared_3225_ == 0)
{
lean_ctor_set_tag(v___x_3224_, 1);
lean_ctor_set(v___x_3224_, 0, v___y_3227_);
v___x_3247_ = v___x_3224_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___y_3227_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
v___jp_3249_:
{
uint8_t v___x_3251_; 
v___x_3251_ = l_Lean_Exception_isInterrupt(v_a_3250_);
if (v___x_3251_ == 0)
{
uint8_t v___x_3252_; 
lean_inc_ref(v_a_3250_);
v___x_3252_ = l_Lean_Exception_isRuntime(v_a_3250_);
v___y_3227_ = v_a_3250_;
v___y_3228_ = v___x_3252_;
goto v___jp_3226_;
}
else
{
v___y_3227_ = v_a_3250_;
v___y_3228_ = v___x_3251_;
goto v___jp_3226_;
}
}
}
}
else
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3274_; 
lean_dec_ref(v_x_x3f_3215_);
v_a_3267_ = lean_ctor_get(v___x_3221_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3269_ = v___x_3221_;
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v___x_3221_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3272_; 
if (v_isShared_3270_ == 0)
{
v___x_3272_ = v___x_3269_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_a_3267_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg___boxed(lean_object* v_x_x3f_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
lean_object* v_res_3281_; 
v_res_3281_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v_x_x3f_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0(lean_object* v_00_u03b1_3282_, lean_object* v_x_x3f_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v_x_x3f_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___boxed(lean_object* v_00_u03b1_3290_, lean_object* v_x_x3f_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0(v_00_u03b1_3290_, v_x_x3f_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
return v_res_3297_;
}
}
static lean_object* _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3302_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1));
v___x_3303_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4));
v___x_3304_ = l_Lean_Name_append(v___x_3303_, v___x_3302_);
return v___x_3304_;
}
}
static lean_object* _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3306_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__3));
v___x_3307_ = l_Lean_stringToMessageData(v___x_3306_);
return v___x_3307_;
}
}
static lean_object* _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3309_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__5));
v___x_3310_ = l_Lean_stringToMessageData(v___x_3309_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0(lean_object* v_mvarId_3311_, lean_object* v_hName_x3f_3312_, uint8_t v_useNewSemantics_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_){
_start:
{
lean_object* v___x_3322_; 
lean_inc(v_mvarId_3311_);
v___x_3322_ = l_Lean_MVarId_getType(v_mvarId_3311_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v_a_3323_; lean_object* v___x_3324_; 
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_a_3323_);
lean_dec_ref_known(v___x_3322_, 1);
v___x_3324_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(v_mvarId_3311_, v_a_3323_, v_hName_x3f_3312_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3422_; 
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3327_ = v___x_3324_;
v_isShared_3328_ = v_isSharedCheck_3422_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v___x_3324_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3422_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
if (lean_obj_tag(v_a_3325_) == 1)
{
lean_object* v_val_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3417_; 
lean_del_object(v___x_3327_);
v_val_3329_ = lean_ctor_get(v_a_3325_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v_a_3325_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3331_ = v_a_3325_;
v_isShared_3332_ = v_isSharedCheck_3417_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_val_3329_);
lean_dec(v_a_3325_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3417_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v_fst_3333_; lean_object* v_snd_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3416_; 
v_fst_3333_ = lean_ctor_get(v_val_3329_, 0);
v_snd_3334_ = lean_ctor_get(v_val_3329_, 1);
v_isSharedCheck_3416_ = !lean_is_exclusive(v_val_3329_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3336_ = v_val_3329_;
v_isShared_3337_ = v_isSharedCheck_3416_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_snd_3334_);
lean_inc(v_fst_3333_);
lean_dec(v_val_3329_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3416_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v_mvarId_3338_; lean_object* v_fvarId_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3415_; 
v_mvarId_3338_ = lean_ctor_get(v_fst_3333_, 0);
v_fvarId_3339_ = lean_ctor_get(v_fst_3333_, 1);
v_isSharedCheck_3415_ = !lean_is_exclusive(v_fst_3333_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3341_ = v_fst_3333_;
v_isShared_3342_ = v_isSharedCheck_3415_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_fvarId_3339_);
lean_inc(v_mvarId_3338_);
lean_dec(v_fst_3333_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3415_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
uint8_t v___x_3343_; lean_object* v___x_3344_; 
v___x_3343_ = 0;
lean_inc(v_mvarId_3338_);
v___x_3344_ = l_Lean_Meta_simpIfTarget(v_mvarId_3338_, v___x_3343_, v_useNewSemantics_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v_a_3345_; lean_object* v_mvarId_3346_; lean_object* v_fvarId_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3406_; 
v_a_3345_ = lean_ctor_get(v___x_3344_, 0);
lean_inc(v_a_3345_);
lean_dec_ref_known(v___x_3344_, 1);
v_mvarId_3346_ = lean_ctor_get(v_snd_3334_, 0);
v_fvarId_3347_ = lean_ctor_get(v_snd_3334_, 1);
v_isSharedCheck_3406_ = !lean_is_exclusive(v_snd_3334_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3349_ = v_snd_3334_;
v_isShared_3350_ = v_isSharedCheck_3406_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_fvarId_3347_);
lean_inc(v_mvarId_3346_);
lean_dec(v_snd_3334_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3406_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3351_; 
lean_inc(v_mvarId_3346_);
v___x_3351_ = l_Lean_Meta_simpIfTarget(v_mvarId_3346_, v___x_3343_, v_useNewSemantics_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3397_; 
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3354_ = v___x_3351_;
v_isShared_3355_ = v_isSharedCheck_3397_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3351_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3397_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
uint8_t v___x_3372_; 
v___x_3372_ = l_Lean_instBEqMVarId_beq(v_mvarId_3338_, v_a_3345_);
lean_dec(v_mvarId_3338_);
if (v___x_3372_ == 0)
{
lean_dec(v_mvarId_3346_);
goto v___jp_3356_;
}
else
{
uint8_t v___x_3373_; 
v___x_3373_ = l_Lean_instBEqMVarId_beq(v_mvarId_3346_, v_a_3352_);
lean_dec(v_mvarId_3346_);
if (v___x_3373_ == 0)
{
goto v___jp_3356_;
}
else
{
lean_object* v_options_3374_; uint8_t v_hasTrace_3375_; 
lean_del_object(v___x_3354_);
lean_del_object(v___x_3349_);
lean_dec(v_fvarId_3347_);
lean_del_object(v___x_3341_);
lean_dec(v_fvarId_3339_);
lean_del_object(v___x_3336_);
lean_del_object(v___x_3331_);
v_options_3374_ = lean_ctor_get(v___y_3316_, 1);
v_hasTrace_3375_ = lean_ctor_get_uint8(v_options_3374_, sizeof(void*)*1);
if (v_hasTrace_3375_ == 0)
{
lean_dec(v_a_3352_);
lean_dec(v_a_3345_);
goto v___jp_3319_;
}
else
{
lean_object* v_toCold_3376_; lean_object* v_inheritedTraceOptions_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; uint8_t v___x_3380_; 
v_toCold_3376_ = lean_ctor_get(v___y_3316_, 0);
v_inheritedTraceOptions_3377_ = lean_ctor_get(v_toCold_3376_, 4);
v___x_3378_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1));
v___x_3379_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2);
v___x_3380_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3377_, v_options_3374_, v___x_3379_);
if (v___x_3380_ == 0)
{
lean_dec(v_a_3352_);
lean_dec(v_a_3345_);
goto v___jp_3319_;
}
else
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3381_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4);
v___x_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3382_, 0, v_a_3345_);
v___x_3383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3381_);
lean_ctor_set(v___x_3383_, 1, v___x_3382_);
v___x_3384_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6);
v___x_3385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3383_);
lean_ctor_set(v___x_3385_, 1, v___x_3384_);
v___x_3386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3386_, 0, v_a_3352_);
v___x_3387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3385_);
lean_ctor_set(v___x_3387_, 1, v___x_3386_);
v___x_3388_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_3378_, v___x_3387_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_dec_ref_known(v___x_3388_, 1);
goto v___jp_3319_;
}
else
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___x_3388_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3388_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3394_; 
if (v_isShared_3392_ == 0)
{
v___x_3394_ = v___x_3391_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3389_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
}
}
}
v___jp_3356_:
{
lean_object* v___x_3358_; 
if (v_isShared_3350_ == 0)
{
lean_ctor_set(v___x_3349_, 1, v_fvarId_3339_);
lean_ctor_set(v___x_3349_, 0, v_a_3345_);
v___x_3358_ = v___x_3349_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3345_);
lean_ctor_set(v_reuseFailAlloc_3371_, 1, v_fvarId_3339_);
v___x_3358_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
lean_object* v___x_3360_; 
if (v_isShared_3342_ == 0)
{
lean_ctor_set(v___x_3341_, 1, v_fvarId_3347_);
lean_ctor_set(v___x_3341_, 0, v_a_3352_);
v___x_3360_ = v___x_3341_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_a_3352_);
lean_ctor_set(v_reuseFailAlloc_3370_, 1, v_fvarId_3347_);
v___x_3360_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
lean_object* v___x_3362_; 
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 1, v___x_3360_);
lean_ctor_set(v___x_3336_, 0, v___x_3358_);
v___x_3362_ = v___x_3336_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3358_);
lean_ctor_set(v_reuseFailAlloc_3369_, 1, v___x_3360_);
v___x_3362_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
lean_object* v___x_3364_; 
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 0, v___x_3362_);
v___x_3364_ = v___x_3331_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3362_);
v___x_3364_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
lean_object* v___x_3366_; 
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 0, v___x_3364_);
v___x_3366_ = v___x_3354_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v___x_3364_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
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
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3405_; 
lean_del_object(v___x_3349_);
lean_dec(v_fvarId_3347_);
lean_dec(v_mvarId_3346_);
lean_dec(v_a_3345_);
lean_del_object(v___x_3341_);
lean_dec(v_fvarId_3339_);
lean_dec(v_mvarId_3338_);
lean_del_object(v___x_3336_);
lean_del_object(v___x_3331_);
v_a_3398_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3400_ = v___x_3351_;
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3351_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3403_; 
if (v_isShared_3401_ == 0)
{
v___x_3403_ = v___x_3400_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_a_3398_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
}
}
else
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3414_; 
lean_del_object(v___x_3341_);
lean_dec(v_fvarId_3339_);
lean_dec(v_mvarId_3338_);
lean_del_object(v___x_3336_);
lean_dec(v_snd_3334_);
lean_del_object(v___x_3331_);
v_a_3407_ = lean_ctor_get(v___x_3344_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3344_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3409_ = v___x_3344_;
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3344_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3412_; 
if (v_isShared_3410_ == 0)
{
v___x_3412_ = v___x_3409_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_a_3407_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3418_; lean_object* v___x_3420_; 
lean_dec(v_a_3325_);
v___x_3418_ = lean_box(0);
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 0, v___x_3418_);
v___x_3420_ = v___x_3327_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3418_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
else
{
return v___x_3324_;
}
}
else
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3430_; 
lean_dec(v_hName_x3f_3312_);
lean_dec(v_mvarId_3311_);
v_a_3423_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3425_ = v___x_3322_;
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3322_);
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
v___jp_3319_:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; 
v___x_3320_ = lean_box(0);
v___x_3321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3320_);
return v___x_3321_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0___boxed(lean_object* v_mvarId_3431_, lean_object* v_hName_x3f_3432_, lean_object* v_useNewSemantics_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_){
_start:
{
uint8_t v_useNewSemantics_boxed_3439_; lean_object* v_res_3440_; 
v_useNewSemantics_boxed_3439_ = lean_unbox(v_useNewSemantics_3433_);
v_res_3440_ = l_Lean_Meta_splitIfTarget_x3f___lam__0(v_mvarId_3431_, v_hName_x3f_3432_, v_useNewSemantics_boxed_3439_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_);
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3436_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f(lean_object* v_mvarId_3441_, lean_object* v_hName_x3f_3442_, uint8_t v_useNewSemantics_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_){
_start:
{
lean_object* v___x_3449_; lean_object* v___f_3450_; lean_object* v___x_3451_; 
v___x_3449_ = lean_box(v_useNewSemantics_3443_);
v___f_3450_ = lean_alloc_closure((void*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3450_, 0, v_mvarId_3441_);
lean_closure_set(v___f_3450_, 1, v_hName_x3f_3442_);
lean_closure_set(v___f_3450_, 2, v___x_3449_);
v___x_3451_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v___f_3450_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
return v___x_3451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___boxed(lean_object* v_mvarId_3452_, lean_object* v_hName_x3f_3453_, lean_object* v_useNewSemantics_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_){
_start:
{
uint8_t v_useNewSemantics_boxed_3460_; lean_object* v_res_3461_; 
v_useNewSemantics_boxed_3460_ = lean_unbox(v_useNewSemantics_3454_);
v_res_3461_ = l_Lean_Meta_splitIfTarget_x3f(v_mvarId_3452_, v_hName_x3f_3453_, v_useNewSemantics_boxed_3460_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_);
lean_dec(v_a_3458_);
lean_dec_ref(v_a_3457_);
lean_dec(v_a_3456_);
lean_dec_ref(v_a_3455_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___lam__0(lean_object* v___x_3462_, lean_object* v_mvarId_3463_, lean_object* v_hName_x3f_3464_, lean_object* v_fvarId_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
lean_object* v___x_3474_; 
lean_inc(v___y_3469_);
lean_inc_ref(v___y_3468_);
lean_inc(v___y_3467_);
lean_inc_ref(v___y_3466_);
v___x_3474_ = lean_infer_type(v___x_3462_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_a_3475_; lean_object* v___x_3476_; 
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_a_3475_);
lean_dec_ref_known(v___x_3474_, 1);
v___x_3476_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(v_mvarId_3463_, v_a_3475_, v_hName_x3f_3464_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
if (lean_obj_tag(v___x_3476_) == 0)
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3572_; 
v_a_3477_ = lean_ctor_get(v___x_3476_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3479_ = v___x_3476_;
v_isShared_3480_ = v_isSharedCheck_3572_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3476_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3572_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
if (lean_obj_tag(v_a_3477_) == 1)
{
lean_object* v_val_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3567_; 
lean_del_object(v___x_3479_);
v_val_3481_ = lean_ctor_get(v_a_3477_, 0);
v_isSharedCheck_3567_ = !lean_is_exclusive(v_a_3477_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3483_ = v_a_3477_;
v_isShared_3484_ = v_isSharedCheck_3567_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_val_3481_);
lean_dec(v_a_3477_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3567_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v_fst_3485_; lean_object* v_snd_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3566_; 
v_fst_3485_ = lean_ctor_get(v_val_3481_, 0);
v_snd_3486_ = lean_ctor_get(v_val_3481_, 1);
v_isSharedCheck_3566_ = !lean_is_exclusive(v_val_3481_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3488_ = v_val_3481_;
v_isShared_3489_ = v_isSharedCheck_3566_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_snd_3486_);
lean_inc(v_fst_3485_);
lean_dec(v_val_3481_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3566_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v_mvarId_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3564_; 
v_mvarId_3490_ = lean_ctor_get(v_fst_3485_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v_fst_3485_);
if (v_isSharedCheck_3564_ == 0)
{
lean_object* v_unused_3565_; 
v_unused_3565_ = lean_ctor_get(v_fst_3485_, 1);
lean_dec(v_unused_3565_);
v___x_3492_ = v_fst_3485_;
v_isShared_3493_ = v_isSharedCheck_3564_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_mvarId_3490_);
lean_dec(v_fst_3485_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3564_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
uint8_t v___x_3494_; lean_object* v___x_3495_; 
v___x_3494_ = 0;
lean_inc(v_fvarId_3465_);
lean_inc(v_mvarId_3490_);
v___x_3495_ = l_Lean_Meta_simpIfLocalDecl(v_mvarId_3490_, v_fvarId_3465_, v___x_3494_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v_mvarId_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3554_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v___x_3495_, 1);
v_mvarId_3497_ = lean_ctor_get(v_snd_3486_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v_snd_3486_);
if (v_isSharedCheck_3554_ == 0)
{
lean_object* v_unused_3555_; 
v_unused_3555_ = lean_ctor_get(v_snd_3486_, 1);
lean_dec(v_unused_3555_);
v___x_3499_ = v_snd_3486_;
v_isShared_3500_ = v_isSharedCheck_3554_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_mvarId_3497_);
lean_dec(v_snd_3486_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3554_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3501_; 
lean_inc(v_mvarId_3497_);
v___x_3501_ = l_Lean_Meta_simpIfLocalDecl(v_mvarId_3497_, v_fvarId_3465_, v___x_3494_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3545_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3504_ = v___x_3501_;
v_isShared_3505_ = v_isSharedCheck_3545_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3501_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3545_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
uint8_t v___x_3516_; 
v___x_3516_ = l_Lean_instBEqMVarId_beq(v_mvarId_3490_, v_a_3496_);
lean_dec(v_mvarId_3490_);
if (v___x_3516_ == 0)
{
lean_del_object(v___x_3499_);
lean_dec(v_mvarId_3497_);
lean_del_object(v___x_3492_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
goto v___jp_3506_;
}
else
{
uint8_t v___x_3517_; 
v___x_3517_ = l_Lean_instBEqMVarId_beq(v_mvarId_3497_, v_a_3502_);
lean_dec(v_mvarId_3497_);
if (v___x_3517_ == 0)
{
lean_del_object(v___x_3499_);
lean_del_object(v___x_3492_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
goto v___jp_3506_;
}
else
{
lean_object* v_options_3518_; uint8_t v_hasTrace_3519_; 
lean_del_object(v___x_3504_);
lean_del_object(v___x_3488_);
lean_del_object(v___x_3483_);
v_options_3518_ = lean_ctor_get(v___y_3468_, 1);
v_hasTrace_3519_ = lean_ctor_get_uint8(v_options_3518_, sizeof(void*)*1);
if (v_hasTrace_3519_ == 0)
{
lean_dec(v_a_3502_);
lean_del_object(v___x_3499_);
lean_dec(v_a_3496_);
lean_del_object(v___x_3492_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
goto v___jp_3471_;
}
else
{
lean_object* v_toCold_3520_; lean_object* v_inheritedTraceOptions_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; uint8_t v___x_3524_; 
v_toCold_3520_ = lean_ctor_get(v___y_3468_, 0);
v_inheritedTraceOptions_3521_ = lean_ctor_get(v_toCold_3520_, 4);
v___x_3522_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1));
v___x_3523_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2);
v___x_3524_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3521_, v_options_3518_, v___x_3523_);
if (v___x_3524_ == 0)
{
lean_dec(v_a_3502_);
lean_del_object(v___x_3499_);
lean_dec(v_a_3496_);
lean_del_object(v___x_3492_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
goto v___jp_3471_;
}
else
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3528_; 
v___x_3525_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4);
v___x_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3526_, 0, v_a_3496_);
if (v_isShared_3500_ == 0)
{
lean_ctor_set_tag(v___x_3499_, 7);
lean_ctor_set(v___x_3499_, 1, v___x_3526_);
lean_ctor_set(v___x_3499_, 0, v___x_3525_);
v___x_3528_ = v___x_3499_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v___x_3525_);
lean_ctor_set(v_reuseFailAlloc_3544_, 1, v___x_3526_);
v___x_3528_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
lean_object* v___x_3529_; lean_object* v___x_3531_; 
v___x_3529_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6);
if (v_isShared_3493_ == 0)
{
lean_ctor_set_tag(v___x_3492_, 7);
lean_ctor_set(v___x_3492_, 1, v___x_3529_);
lean_ctor_set(v___x_3492_, 0, v___x_3528_);
v___x_3531_ = v___x_3492_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v___x_3528_);
lean_ctor_set(v_reuseFailAlloc_3543_, 1, v___x_3529_);
v___x_3531_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3532_, 0, v_a_3502_);
v___x_3533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3531_);
lean_ctor_set(v___x_3533_, 1, v___x_3532_);
v___x_3534_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_3522_, v___x_3533_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_dec_ref_known(v___x_3534_, 1);
goto v___jp_3471_;
}
else
{
lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3542_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3537_ = v___x_3534_;
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___x_3534_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3540_; 
if (v_isShared_3538_ == 0)
{
v___x_3540_ = v___x_3537_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3535_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
}
}
}
}
}
}
v___jp_3506_:
{
lean_object* v___x_3508_; 
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 1, v_a_3502_);
lean_ctor_set(v___x_3488_, 0, v_a_3496_);
v___x_3508_ = v___x_3488_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_a_3496_);
lean_ctor_set(v_reuseFailAlloc_3515_, 1, v_a_3502_);
v___x_3508_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
lean_object* v___x_3510_; 
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 0, v___x_3508_);
v___x_3510_ = v___x_3483_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v___x_3508_);
v___x_3510_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
lean_object* v___x_3512_; 
if (v_isShared_3505_ == 0)
{
lean_ctor_set(v___x_3504_, 0, v___x_3510_);
v___x_3512_ = v___x_3504_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v___x_3510_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
}
}
}
}
else
{
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
lean_del_object(v___x_3499_);
lean_dec(v_mvarId_3497_);
lean_dec(v_a_3496_);
lean_del_object(v___x_3492_);
lean_dec(v_mvarId_3490_);
lean_del_object(v___x_3488_);
lean_del_object(v___x_3483_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
v_a_3546_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3548_ = v___x_3501_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3501_);
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
else
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3563_; 
lean_del_object(v___x_3492_);
lean_dec(v_mvarId_3490_);
lean_del_object(v___x_3488_);
lean_dec(v_snd_3486_);
lean_del_object(v___x_3483_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec(v_fvarId_3465_);
v_a_3556_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3558_ = v___x_3495_;
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3495_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3561_; 
if (v_isShared_3559_ == 0)
{
v___x_3561_ = v___x_3558_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3556_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3568_; lean_object* v___x_3570_; 
lean_dec(v_a_3477_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec(v_fvarId_3465_);
v___x_3568_ = lean_box(0);
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 0, v___x_3568_);
v___x_3570_ = v___x_3479_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v___x_3568_);
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
else
{
lean_object* v_a_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3580_; 
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec(v_fvarId_3465_);
v_a_3573_ = lean_ctor_get(v___x_3476_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3575_ = v___x_3476_;
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_a_3573_);
lean_dec(v___x_3476_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3578_; 
if (v_isShared_3576_ == 0)
{
v___x_3578_ = v___x_3575_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_a_3573_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
}
else
{
lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3588_; 
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec(v_fvarId_3465_);
lean_dec(v_hName_x3f_3464_);
lean_dec(v_mvarId_3463_);
v_a_3581_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3583_ = v___x_3474_;
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v___x_3474_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3586_; 
if (v_isShared_3584_ == 0)
{
v___x_3586_ = v___x_3583_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_a_3581_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
v___jp_3471_:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3472_ = lean_box(0);
v___x_3473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3472_);
return v___x_3473_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___lam__0___boxed(lean_object* v___x_3589_, lean_object* v_mvarId_3590_, lean_object* v_hName_x3f_3591_, lean_object* v_fvarId_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_){
_start:
{
lean_object* v_res_3598_; 
v_res_3598_ = l_Lean_Meta_splitIfLocalDecl_x3f___lam__0(v___x_3589_, v_mvarId_3590_, v_hName_x3f_3591_, v_fvarId_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f(lean_object* v_mvarId_3599_, lean_object* v_fvarId_3600_, lean_object* v_hName_x3f_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_){
_start:
{
lean_object* v___x_3607_; lean_object* v___f_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
lean_inc(v_fvarId_3600_);
v___x_3607_ = l_Lean_mkFVar(v_fvarId_3600_);
lean_inc(v_mvarId_3599_);
v___f_3608_ = lean_alloc_closure((void*)(l_Lean_Meta_splitIfLocalDecl_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3608_, 0, v___x_3607_);
lean_closure_set(v___f_3608_, 1, v_mvarId_3599_);
lean_closure_set(v___f_3608_, 2, v_hName_x3f_3601_);
lean_closure_set(v___f_3608_, 3, v_fvarId_3600_);
v___x_3609_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3609_, 0, lean_box(0));
lean_closure_set(v___x_3609_, 1, v_mvarId_3599_);
lean_closure_set(v___x_3609_, 2, v___f_3608_);
v___x_3610_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v___x_3609_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___boxed(lean_object* v_mvarId_3611_, lean_object* v_fvarId_3612_, lean_object* v_hName_x3f_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l_Lean_Meta_splitIfLocalDecl_x3f(v_mvarId_3611_, v_fvarId_3612_, v_hName_x3f_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_);
lean_dec(v_a_3617_);
lean_dec_ref(v_a_3616_);
lean_dec(v_a_3615_);
lean_dec_ref(v_a_3614_);
return v_res_3619_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3640_ = lean_unsigned_to_nat(3526097586u);
v___x_3641_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_));
v___x_3642_ = l_Lean_Name_num___override(v___x_3641_, v___x_3640_);
return v___x_3642_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3644_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_));
v___x_3645_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3646_ = l_Lean_Name_str___override(v___x_3645_, v___x_3644_);
return v___x_3646_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3648_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_));
v___x_3649_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3650_ = l_Lean_Name_str___override(v___x_3649_, v___x_3648_);
return v___x_3650_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3651_ = lean_unsigned_to_nat(2u);
v___x_3652_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3653_ = l_Lean_Name_num___override(v___x_3652_, v___x_3651_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3655_; uint8_t v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3655_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9));
v___x_3656_ = 0;
v___x_3657_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3658_ = l_Lean_registerTraceClass(v___x_3655_, v___x_3656_, v___x_3657_);
return v___x_3658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2____boxed(lean_object* v_a_3659_){
_start:
{
lean_object* v_res_3660_; 
v_res_3660_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_();
return v_res_3660_;
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
