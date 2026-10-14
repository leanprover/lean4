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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Meta_DiscrTree_empty___redArg();
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
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
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
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
lean_object* l_Lean_instBEqPtr___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_instHashablePtr___redArg___lam__0___boxed(lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ctorIdx___impl___boxed(lean_object*);
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
static const lean_closure_object l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqPtr___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashablePtr___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1(lean_object*);
static lean_once_cell_t l_Lean_Meta_SplitIf_getSimpContext___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__0;
static lean_once_cell_t l_Lean_Meta_SplitIf_getSimpContext___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__1;
static lean_once_cell_t l_Lean_Meta_SplitIf_getSimpContext___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__2;
static const lean_string_object l_Lean_Meta_SplitIf_getSimpContext___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ite_eq_left"};
static const lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__3 = (const lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__3_value;
static const lean_ctor_object l_Lean_Meta_SplitIf_getSimpContext___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__3_value),LEAN_SCALAR_PTR_LITERAL(224, 237, 116, 5, 155, 59, 56, 160)}};
static const lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__4 = (const lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__4_value;
static const lean_string_object l_Lean_Meta_SplitIf_getSimpContext___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ite_eq_right"};
static const lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__5 = (const lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__5_value;
static const lean_ctor_object l_Lean_Meta_SplitIf_getSimpContext___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__5_value),LEAN_SCALAR_PTR_LITERAL(61, 39, 8, 237, 213, 91, 107, 69)}};
static const lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__6 = (const lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__6_value;
static const lean_string_object l_Lean_Meta_SplitIf_getSimpContext___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "dite_eq_left"};
static const lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__7 = (const lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__7_value;
static const lean_ctor_object l_Lean_Meta_SplitIf_getSimpContext___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__7_value),LEAN_SCALAR_PTR_LITERAL(239, 169, 41, 13, 119, 67, 249, 86)}};
static const lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__8 = (const lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__8_value;
static const lean_string_object l_Lean_Meta_SplitIf_getSimpContext___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "dite_eq_right"};
static const lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__9 = (const lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__9_value;
static const lean_ctor_object l_Lean_Meta_SplitIf_getSimpContext___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__9_value),LEAN_SCALAR_PTR_LITERAL(138, 158, 15, 234, 166, 144, 231, 97)}};
static const lean_object* l_Lean_Meta_SplitIf_getSimpContext___closed__10 = (const lean_object*)&l_Lean_Meta_SplitIf_getSimpContext___closed__10_value;
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__2_value),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1_value;
static const lean_array_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__4_value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__5_value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__6_value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "SplitIf"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__7_value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(76, 221, 255, 40, 254, 93, 36, 145)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(77, 67, 39, 96, 166, 188, 81, 166)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__10_value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(56, 202, 4, 90, 23, 96, 207, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__11_value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(148, 235, 194, 225, 124, 161, 64, 247)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__12_value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(167, 120, 249, 182, 103, 12, 98, 131)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reduceIte'"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__13_value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__14_value),LEAN_SCALAR_PTR_LITERAL(244, 195, 180, 159, 75, 12, 135, 86)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__4_value),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__16_value;
static const lean_array_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "reduceDIte'"};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__18_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__13_value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__18_value),LEAN_SCALAR_PTR_LITERAL(167, 195, 231, 206, 69, 191, 167, 198)}};
static const lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__19_value;
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
static const lean_closure_object l_panic___at___00Lean_Meta_simpIfTarget_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_string_object l_Lean_Meta_simpIfTarget___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Meta.Tactic.SplitIf"};
static const lean_object* l_Lean_Meta_simpIfTarget___closed__6 = (const lean_object*)&l_Lean_Meta_simpIfTarget___closed__6_value;
static const lean_string_object l_Lean_Meta_simpIfTarget___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.simpIfTarget"};
static const lean_object* l_Lean_Meta_simpIfTarget___closed__7 = (const lean_object*)&l_Lean_Meta_simpIfTarget___closed__7_value;
static const lean_string_object l_Lean_Meta_simpIfTarget___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Meta_simpIfTarget___closed__8 = (const lean_object*)&l_Lean_Meta_simpIfTarget___closed__8_value;
static lean_once_cell_t l_Lean_Meta_simpIfTarget___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_simpIfTarget___closed__9;
static const lean_array_object l_Lean_Meta_simpIfTarget___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_simpIfTarget___closed__10 = (const lean_object*)&l_Lean_Meta_simpIfTarget___closed__10_value;
static lean_once_cell_t l_Lean_Meta_simpIfTarget___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_simpIfTarget___closed__11;
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__12_value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(81, 137, 76, 163, 76, 115, 6, 53)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(79, 37, 36, 7, 71, 199, 210, 30)}};
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
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_Meta_SplitKind_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Meta_SplitKind_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lean_Meta_SplitKind_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ite_elim___redArg(lean_object* v_ite_22_){
_start:
{
lean_inc(v_ite_22_);
return v_ite_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ite_elim___redArg___boxed(lean_object* v_ite_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Meta_SplitKind_ite_elim___redArg(v_ite_23_);
lean_dec(v_ite_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ite_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_ite_28_){
_start:
{
lean_inc(v_ite_28_);
return v_ite_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ite_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_ite_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_Meta_SplitKind_ite_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_ite_32_);
lean_dec(v_ite_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_match_elim___redArg(lean_object* v_match_35_){
_start:
{
lean_inc(v_match_35_);
return v_match_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_match_elim___redArg___boxed(lean_object* v_match_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Meta_SplitKind_match_elim___redArg(v_match_36_);
lean_dec(v_match_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_match_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_match_41_){
_start:
{
lean_inc(v_match_41_);
return v_match_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_match_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_match_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_Meta_SplitKind_match_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_match_45_);
lean_dec(v_match_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_both_elim___redArg(lean_object* v_both_48_){
_start:
{
lean_inc(v_both_48_);
return v_both_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_both_elim___redArg___boxed(lean_object* v_both_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Meta_SplitKind_both_elim___redArg(v_both_49_);
lean_dec(v_both_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_both_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_both_54_){
_start:
{
lean_inc(v_both_54_);
return v_both_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_both_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_both_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lean_Meta_SplitKind_both_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_both_58_);
lean_dec(v_both_58_);
return v_res_60_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SplitKind_considerIte(uint8_t v_x_61_){
_start:
{
switch(v_x_61_)
{
case 0:
{
uint8_t v___x_62_; 
v___x_62_ = 1;
return v___x_62_;
}
case 2:
{
uint8_t v___x_63_; 
v___x_63_ = 1;
return v___x_63_;
}
default: 
{
uint8_t v___x_64_; 
v___x_64_ = 0;
return v___x_64_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_considerIte___boxed(lean_object* v_x_65_){
_start:
{
uint8_t v_x_22__boxed_66_; uint8_t v_res_67_; lean_object* v_r_68_; 
v_x_22__boxed_66_ = lean_unbox(v_x_65_);
v_res_67_ = l_Lean_Meta_SplitKind_considerIte(v_x_22__boxed_66_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SplitKind_considerMatch(uint8_t v_x_69_){
_start:
{
switch(v_x_69_)
{
case 1:
{
uint8_t v___x_70_; 
v___x_70_ = 1;
return v___x_70_;
}
case 2:
{
uint8_t v___x_71_; 
v___x_71_ = 1;
return v___x_71_;
}
default: 
{
uint8_t v___x_72_; 
v___x_72_ = 0;
return v___x_72_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_considerMatch___boxed(lean_object* v_x_73_){
_start:
{
uint8_t v_x_22__boxed_74_; uint8_t v_res_75_; lean_object* v_r_76_; 
v_x_22__boxed_74_ = lean_unbox(v_x_73_);
v_res_75_ = l_Lean_Meta_SplitKind_considerMatch(v_x_22__boxed_74_);
v_r_76_ = lean_box(v_res_75_);
return v_r_76_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg(lean_object* v_a_77_, lean_object* v_x_78_){
_start:
{
if (lean_obj_tag(v_x_78_) == 0)
{
uint8_t v___x_79_; 
v___x_79_ = 0;
return v___x_79_;
}
else
{
lean_object* v_key_80_; lean_object* v_tail_81_; uint8_t v___x_82_; 
v_key_80_ = lean_ctor_get(v_x_78_, 0);
v_tail_81_ = lean_ctor_get(v_x_78_, 2);
v___x_82_ = lean_expr_eqv(v_key_80_, v_a_77_);
if (v___x_82_ == 0)
{
v_x_78_ = v_tail_81_;
goto _start;
}
else
{
return v___x_82_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_84_, lean_object* v_x_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg(v_a_84_, v_x_85_);
lean_dec(v_x_85_);
lean_dec_ref(v_a_84_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(lean_object* v_m_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_buckets_90_; lean_object* v___x_91_; uint64_t v___x_92_; uint64_t v___x_93_; uint64_t v___x_94_; uint64_t v_fold_95_; uint64_t v___x_96_; uint64_t v___x_97_; uint64_t v___x_98_; size_t v___x_99_; size_t v___x_100_; size_t v___x_101_; size_t v___x_102_; size_t v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v_buckets_90_ = lean_ctor_get(v_m_88_, 1);
v___x_91_ = lean_array_get_size(v_buckets_90_);
v___x_92_ = l_Lean_Expr_hash(v_a_89_);
v___x_93_ = 32ULL;
v___x_94_ = lean_uint64_shift_right(v___x_92_, v___x_93_);
v_fold_95_ = lean_uint64_xor(v___x_92_, v___x_94_);
v___x_96_ = 16ULL;
v___x_97_ = lean_uint64_shift_right(v_fold_95_, v___x_96_);
v___x_98_ = lean_uint64_xor(v_fold_95_, v___x_97_);
v___x_99_ = lean_uint64_to_usize(v___x_98_);
v___x_100_ = lean_usize_of_nat(v___x_91_);
v___x_101_ = ((size_t)1ULL);
v___x_102_ = lean_usize_sub(v___x_100_, v___x_101_);
v___x_103_ = lean_usize_land(v___x_99_, v___x_102_);
v___x_104_ = lean_array_uget_borrowed(v_buckets_90_, v___x_103_);
v___x_105_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg(v_a_89_, v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg___boxed(lean_object* v_m_106_, lean_object* v_a_107_){
_start:
{
uint8_t v_res_108_; lean_object* v_r_109_; 
v_res_108_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(v_m_106_, v_a_107_);
lean_dec_ref(v_a_107_);
lean_dec_ref(v_m_106_);
v_r_109_ = lean_box(v_res_108_);
return v_r_109_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg(lean_object* v_upperBound_118_, lean_object* v_args_119_, lean_object* v_a_120_, lean_object* v_b_121_){
_start:
{
uint8_t v___x_122_; 
v___x_122_ = lean_nat_dec_lt(v_a_120_, v_upperBound_118_);
if (v___x_122_ == 0)
{
lean_dec(v_a_120_);
lean_inc_ref(v_b_121_);
return v_b_121_;
}
else
{
lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_123_ = l_Lean_instInhabitedExpr;
v___x_124_ = lean_array_get_borrowed(v___x_123_, v_args_119_, v_a_120_);
v___x_125_ = l_Lean_Expr_hasLooseBVars(v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_126_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0));
v___x_127_ = lean_unsigned_to_nat(1u);
v___x_128_ = lean_nat_add(v_a_120_, v___x_127_);
lean_dec(v_a_120_);
v_a_120_ = v___x_128_;
v_b_121_ = v___x_126_;
goto _start;
}
else
{
lean_object* v___x_130_; 
lean_dec(v_a_120_);
v___x_130_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__2));
return v___x_130_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___boxed(lean_object* v_upperBound_131_, lean_object* v_args_132_, lean_object* v_a_133_, lean_object* v_b_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg(v_upperBound_131_, v_args_132_, v_a_133_, v_b_134_);
lean_dec_ref(v_b_134_);
lean_dec_ref(v_args_132_);
lean_dec(v_upperBound_131_);
return v_res_135_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0(void){
_start:
{
lean_object* v___x_136_; lean_object* v_dummy_137_; 
v___x_136_ = lean_box(0);
v_dummy_137_ = l_Lean_Expr_sort___override(v___x_136_);
return v_dummy_137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f(lean_object* v_env_144_, lean_object* v_ctx_145_, lean_object* v_e_146_){
_start:
{
lean_object* v_exceptionSet_147_; uint8_t v_kind_148_; lean_object* v_e_150_; uint8_t v___y_178_; uint8_t v___x_187_; 
v_exceptionSet_147_ = lean_ctor_get(v_ctx_145_, 0);
v_kind_148_ = lean_ctor_get_uint8(v_ctx_145_, sizeof(void*)*1);
v___x_187_ = l_Lean_Meta_SplitKind_considerIte(v_kind_148_);
if (v___x_187_ == 0)
{
goto v___jp_154_;
}
else
{
lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__2));
v___x_189_ = l_Lean_Expr_isAppOf(v_e_146_, v___x_188_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; uint8_t v___x_191_; 
v___x_190_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__4));
v___x_191_ = l_Lean_Expr_isAppOf(v_e_146_, v___x_190_);
if (v___x_191_ == 0)
{
goto v___jp_154_;
}
else
{
v___y_178_ = v___x_191_;
goto v___jp_177_;
}
}
else
{
v___y_178_ = v___x_189_;
goto v___jp_177_;
}
}
v___jp_149_:
{
uint8_t v___x_151_; 
v___x_151_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(v_exceptionSet_147_, v_e_150_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; 
v___x_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_152_, 0, v_e_150_);
return v___x_152_;
}
else
{
lean_object* v___x_153_; 
lean_dec_ref(v_e_150_);
v___x_153_ = lean_box(0);
return v___x_153_;
}
}
v___jp_154_:
{
uint8_t v___x_155_; 
v___x_155_ = l_Lean_Meta_SplitKind_considerMatch(v_kind_148_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; 
lean_dec_ref(v_e_146_);
lean_dec_ref(v_env_144_);
v___x_156_ = lean_box(0);
return v___x_156_;
}
else
{
lean_object* v___x_157_; 
v___x_157_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_144_, v_e_146_);
if (lean_obj_tag(v___x_157_) == 1)
{
lean_object* v_val_158_; lean_object* v_numDiscrs_159_; lean_object* v_nargs_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v_dummy_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v_args_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v_fst_170_; 
v_val_158_ = lean_ctor_get(v___x_157_, 0);
lean_inc(v_val_158_);
lean_dec_ref_known(v___x_157_, 1);
v_numDiscrs_159_ = lean_ctor_get(v_val_158_, 1);
v_nargs_160_ = l_Lean_Expr_getAppNumArgs(v_e_146_);
v___x_161_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_158_);
v___x_162_ = lean_nat_add(v___x_161_, v_numDiscrs_159_);
v_dummy_163_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0);
lean_inc(v_nargs_160_);
v___x_164_ = lean_mk_array(v_nargs_160_, v_dummy_163_);
v___x_165_ = lean_unsigned_to_nat(1u);
v___x_166_ = lean_nat_sub(v_nargs_160_, v___x_165_);
lean_dec(v_nargs_160_);
lean_inc_ref(v_e_146_);
v_args_167_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_146_, v___x_164_, v___x_166_);
v___x_168_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0));
v___x_169_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg(v___x_162_, v_args_167_, v___x_161_, v___x_168_);
lean_dec(v___x_162_);
v_fst_170_ = lean_ctor_get(v___x_169_, 0);
lean_inc(v_fst_170_);
lean_dec_ref(v___x_169_);
if (lean_obj_tag(v_fst_170_) == 0)
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_171_ = lean_array_get_size(v_args_167_);
lean_dec_ref(v_args_167_);
v___x_172_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_158_);
lean_dec(v_val_158_);
v___x_173_ = lean_nat_sub(v___x_171_, v___x_172_);
lean_dec(v___x_172_);
v___x_174_ = l_Lean_Expr_getBoundedAppFn(v___x_173_, v_e_146_);
lean_dec_ref(v_e_146_);
v_e_150_ = v___x_174_;
goto v___jp_149_;
}
else
{
lean_object* v_val_175_; 
lean_dec_ref(v_args_167_);
lean_dec(v_val_158_);
lean_dec_ref(v_e_146_);
v_val_175_ = lean_ctor_get(v_fst_170_, 0);
lean_inc(v_val_175_);
lean_dec_ref_known(v_fst_170_, 1);
return v_val_175_;
}
}
else
{
lean_object* v___x_176_; 
lean_dec(v___x_157_);
lean_dec_ref(v_e_146_);
v___x_176_ = lean_box(0);
return v___x_176_;
}
}
}
v___jp_177_:
{
lean_object* v_numArgs_179_; lean_object* v___x_180_; uint8_t v___x_181_; 
v_numArgs_179_ = l_Lean_Expr_getAppNumArgs(v_e_146_);
v___x_180_ = lean_unsigned_to_nat(5u);
v___x_181_ = lean_nat_dec_le(v___x_180_, v_numArgs_179_);
if (v___x_181_ == 0)
{
lean_dec(v_numArgs_179_);
goto v___jp_154_;
}
else
{
lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_182_ = lean_unsigned_to_nat(3u);
v___x_183_ = l_Lean_Expr_getRevArg_x21(v_e_146_, v___x_182_);
v___x_184_ = l_Lean_Expr_hasLooseBVars(v___x_183_);
lean_dec_ref(v___x_183_);
if (v___x_184_ == 0)
{
if (v___y_178_ == 0)
{
lean_dec(v_numArgs_179_);
goto v___jp_154_;
}
else
{
lean_object* v___x_185_; lean_object* v___x_186_; 
lean_dec_ref(v_env_144_);
v___x_185_ = lean_nat_sub(v_numArgs_179_, v___x_180_);
lean_dec(v_numArgs_179_);
v___x_186_ = l_Lean_Expr_getBoundedAppFn(v___x_185_, v_e_146_);
lean_dec_ref(v_e_146_);
v_e_150_ = v___x_186_;
goto v___jp_149_;
}
}
else
{
lean_dec(v_numArgs_179_);
goto v___jp_154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___boxed(lean_object* v_env_192_, lean_object* v_ctx_193_, lean_object* v_e_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f(v_env_192_, v_ctx_193_, v_e_194_);
lean_dec_ref(v_ctx_193_);
return v_res_195_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0(lean_object* v_00_u03b2_196_, lean_object* v_m_197_, lean_object* v_a_198_){
_start:
{
uint8_t v___x_199_; 
v___x_199_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(v_m_197_, v_a_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___boxed(lean_object* v_00_u03b2_200_, lean_object* v_m_201_, lean_object* v_a_202_){
_start:
{
uint8_t v_res_203_; lean_object* v_r_204_; 
v_res_203_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0(v_00_u03b2_200_, v_m_201_, v_a_202_);
lean_dec_ref(v_a_202_);
lean_dec_ref(v_m_201_);
v_r_204_ = lean_box(v_res_203_);
return v_r_204_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1(lean_object* v_upperBound_205_, lean_object* v_args_206_, lean_object* v_inst_207_, lean_object* v_R_208_, lean_object* v_a_209_, lean_object* v_b_210_, lean_object* v_c_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg(v_upperBound_205_, v_args_206_, v_a_209_, v_b_210_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___boxed(lean_object* v_upperBound_213_, lean_object* v_args_214_, lean_object* v_inst_215_, lean_object* v_R_216_, lean_object* v_a_217_, lean_object* v_b_218_, lean_object* v_c_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1(v_upperBound_213_, v_args_214_, v_inst_215_, v_R_216_, v_a_217_, v_b_218_, v_c_219_);
lean_dec_ref(v_b_218_);
lean_dec_ref(v_args_214_);
lean_dec(v_upperBound_213_);
return v_res_220_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0(lean_object* v_00_u03b2_221_, lean_object* v_a_222_, lean_object* v_x_223_){
_start:
{
uint8_t v___x_224_; 
v___x_224_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg(v_a_222_, v_x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_225_, lean_object* v_a_226_, lean_object* v_x_227_){
_start:
{
uint8_t v_res_228_; lean_object* v_r_229_; 
v_res_228_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0(v_00_u03b2_225_, v_a_226_, v_x_227_);
lean_dec(v_x_227_);
lean_dec_ref(v_a_226_);
v_r_229_ = lean_box(v_res_228_);
return v_r_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___redArg(lean_object* v_e_234_, lean_object* v_a_235_){
_start:
{
lean_object* v___f_237_; lean_object* v___f_238_; uint8_t v___x_239_; 
v___f_237_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__0));
v___f_238_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__1));
lean_inc_ref(v_e_234_);
v___x_239_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_237_, v___f_238_, v_a_235_, v_e_234_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_240_ = lean_box(0);
v___x_241_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_237_, v___f_238_, v_a_235_, v_e_234_, v___x_240_);
v___x_242_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__2));
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v___x_241_);
v___x_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
return v___x_244_;
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
lean_dec_ref(v_e_234_);
v___x_245_ = lean_box(0);
v___x_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v_a_235_);
v___x_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
return v___x_247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___redArg___boxed(lean_object* v_e_248_, lean_object* v_a_249_, lean_object* v_a_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_Meta_FindSplitImpl_checkVisited___redArg(v_e_248_, v_a_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited(lean_object* v_e_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v___f_260_; lean_object* v___f_261_; uint8_t v___x_262_; 
v___f_260_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__0));
v___f_261_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__1));
lean_inc_ref(v_e_252_);
v___x_262_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_260_, v___f_261_, v_a_254_, v_e_252_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_263_ = lean_box(0);
v___x_264_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_260_, v___f_261_, v_a_254_, v_e_252_, v___x_263_);
v___x_265_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__2));
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v___x_264_);
v___x_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
return v___x_267_;
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
lean_dec_ref(v_e_252_);
v___x_268_ = lean_box(0);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v_a_254_);
v___x_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
return v___x_270_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___boxed(lean_object* v_e_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Meta_FindSplitImpl_checkVisited(v_e_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_);
lean_dec(v_a_277_);
lean_dec_ref(v_a_276_);
lean_dec(v_a_275_);
lean_dec_ref(v_a_274_);
lean_dec_ref(v_a_272_);
return v_res_279_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(lean_object* v_a_280_, lean_object* v_x_281_){
_start:
{
if (lean_obj_tag(v_x_281_) == 0)
{
uint8_t v___x_282_; 
v___x_282_ = 0;
return v___x_282_;
}
else
{
lean_object* v_key_283_; lean_object* v_tail_284_; size_t v___x_285_; size_t v___x_286_; uint8_t v___x_287_; 
v_key_283_ = lean_ctor_get(v_x_281_, 0);
v_tail_284_ = lean_ctor_get(v_x_281_, 2);
v___x_285_ = lean_ptr_addr(v_key_283_);
v___x_286_ = lean_ptr_addr(v_a_280_);
v___x_287_ = lean_usize_dec_eq(v___x_285_, v___x_286_);
if (v___x_287_ == 0)
{
v_x_281_ = v_tail_284_;
goto _start;
}
else
{
return v___x_287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg___boxed(lean_object* v_a_289_, lean_object* v_x_290_){
_start:
{
uint8_t v_res_291_; lean_object* v_r_292_; 
v_res_291_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(v_a_289_, v_x_290_);
lean_dec(v_x_290_);
lean_dec_ref(v_a_289_);
v_r_292_ = lean_box(v_res_291_);
return v_r_292_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6_spec__7___redArg(lean_object* v_x_293_, lean_object* v_x_294_){
_start:
{
if (lean_obj_tag(v_x_294_) == 0)
{
return v_x_293_;
}
else
{
lean_object* v_key_295_; lean_object* v_value_296_; lean_object* v_tail_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_323_; 
v_key_295_ = lean_ctor_get(v_x_294_, 0);
v_value_296_ = lean_ctor_get(v_x_294_, 1);
v_tail_297_ = lean_ctor_get(v_x_294_, 2);
v_isSharedCheck_323_ = !lean_is_exclusive(v_x_294_);
if (v_isSharedCheck_323_ == 0)
{
v___x_299_ = v_x_294_;
v_isShared_300_ = v_isSharedCheck_323_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_tail_297_);
lean_inc(v_value_296_);
lean_inc(v_key_295_);
lean_dec(v_x_294_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_323_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; size_t v___x_302_; uint64_t v___x_303_; uint64_t v___x_304_; uint64_t v___x_305_; uint64_t v___x_306_; uint64_t v___x_307_; uint64_t v_fold_308_; uint64_t v___x_309_; uint64_t v___x_310_; uint64_t v___x_311_; size_t v___x_312_; size_t v___x_313_; size_t v___x_314_; size_t v___x_315_; size_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_301_ = lean_array_get_size(v_x_293_);
v___x_302_ = lean_ptr_addr(v_key_295_);
v___x_303_ = lean_usize_to_uint64(v___x_302_);
v___x_304_ = 11ULL;
v___x_305_ = lean_uint64_mix_hash(v___x_303_, v___x_304_);
v___x_306_ = 32ULL;
v___x_307_ = lean_uint64_shift_right(v___x_305_, v___x_306_);
v_fold_308_ = lean_uint64_xor(v___x_305_, v___x_307_);
v___x_309_ = 16ULL;
v___x_310_ = lean_uint64_shift_right(v_fold_308_, v___x_309_);
v___x_311_ = lean_uint64_xor(v_fold_308_, v___x_310_);
v___x_312_ = lean_uint64_to_usize(v___x_311_);
v___x_313_ = lean_usize_of_nat(v___x_301_);
v___x_314_ = ((size_t)1ULL);
v___x_315_ = lean_usize_sub(v___x_313_, v___x_314_);
v___x_316_ = lean_usize_land(v___x_312_, v___x_315_);
v___x_317_ = lean_array_uget_borrowed(v_x_293_, v___x_316_);
lean_inc(v___x_317_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 2, v___x_317_);
v___x_319_ = v___x_299_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_key_295_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_value_296_);
lean_ctor_set(v_reuseFailAlloc_322_, 2, v___x_317_);
v___x_319_ = v_reuseFailAlloc_322_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_320_; 
v___x_320_ = lean_array_uset(v_x_293_, v___x_316_, v___x_319_);
v_x_293_ = v___x_320_;
v_x_294_ = v_tail_297_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6___redArg(lean_object* v_i_324_, lean_object* v_source_325_, lean_object* v_target_326_){
_start:
{
lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = lean_array_get_size(v_source_325_);
v___x_328_ = lean_nat_dec_lt(v_i_324_, v___x_327_);
if (v___x_328_ == 0)
{
lean_dec_ref(v_source_325_);
lean_dec(v_i_324_);
return v_target_326_;
}
else
{
lean_object* v_es_329_; lean_object* v___x_330_; lean_object* v_source_331_; lean_object* v_target_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_es_329_ = lean_array_fget(v_source_325_, v_i_324_);
v___x_330_ = lean_box(0);
v_source_331_ = lean_array_fset(v_source_325_, v_i_324_, v___x_330_);
v_target_332_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6_spec__7___redArg(v_target_326_, v_es_329_);
v___x_333_ = lean_unsigned_to_nat(1u);
v___x_334_ = lean_nat_add(v_i_324_, v___x_333_);
lean_dec(v_i_324_);
v_i_324_ = v___x_334_;
v_source_325_ = v_source_331_;
v_target_326_ = v_target_332_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5___redArg(lean_object* v_data_336_){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v_nbuckets_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_337_ = lean_array_get_size(v_data_336_);
v___x_338_ = lean_unsigned_to_nat(2u);
v_nbuckets_339_ = lean_nat_mul(v___x_337_, v___x_338_);
v___x_340_ = lean_unsigned_to_nat(0u);
v___x_341_ = lean_box(0);
v___x_342_ = lean_mk_array(v_nbuckets_339_, v___x_341_);
v___x_343_ = lean_array_propagate_mark(v_data_336_, v___x_342_);
v___x_344_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6___redArg(v___x_340_, v_data_336_, v___x_343_);
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
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v_env_459_; lean_object* v___x_460_; 
v___x_456_ = lean_box(0);
lean_inc_ref_n(v_e_416_, 2);
v___x_457_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4___redArg(v_a_418_, v_e_416_, v___x_456_);
v___x_458_ = lean_st_ref_get(v_a_422_);
v_env_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc_ref(v_env_459_);
lean_dec(v___x_458_);
v___x_460_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f(v_env_459_, v_a_417_, v_e_416_);
if (lean_obj_tag(v___x_460_) == 1)
{
lean_object* v___x_461_; lean_object* v___x_462_; 
lean_dec_ref(v_e_416_);
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
lean_ctor_set(v___x_461_, 1, v___x_457_);
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
v___y_426_ = v___x_457_;
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
lean_ctor_set(v___x_471_, 1, v___x_457_);
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
lean_dec_ref(v___x_457_);
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
v___y_426_ = v___x_457_;
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
v_fst_441_ = lean_ctor_get(v_a_440_, 0);
if (lean_obj_tag(v_fst_441_) == 0)
{
lean_object* v_snd_442_; 
lean_inc(v_a_440_);
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
v_fst_448_ = lean_ctor_get(v_a_447_, 0);
if (lean_obj_tag(v_fst_448_) == 0)
{
lean_object* v_snd_449_; 
lean_inc(v_a_447_);
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
lean_object* v___x_810_; lean_object* v_env_811_; uint8_t v___x_812_; lean_object* v_env_813_; lean_object* v___x_814_; lean_object* v_toCold_815_; lean_object* v_mctx_816_; lean_object* v_lctx_817_; lean_object* v_options_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_810_ = lean_st_ref_get(v___y_808_);
v_env_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc_ref(v_env_811_);
lean_dec(v___x_810_);
v___x_812_ = 0;
v_env_813_ = l_Lean_Environment_setRecordingDeps(v_env_811_, v___x_812_);
v___x_814_ = lean_st_ref_get(v___y_806_);
v_toCold_815_ = lean_ctor_get(v___y_807_, 0);
v_mctx_816_ = lean_ctor_get(v___x_814_, 0);
lean_inc_ref(v_mctx_816_);
lean_dec(v___x_814_);
v_lctx_817_ = lean_ctor_get(v___y_805_, 2);
v_options_818_ = lean_ctor_get(v_toCold_815_, 2);
lean_inc_ref(v_options_818_);
lean_inc_ref(v_lctx_817_);
v___x_819_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_819_, 0, v_env_813_);
lean_ctor_set(v___x_819_, 1, v_mctx_816_);
lean_ctor_set(v___x_819_, 2, v_lctx_817_);
lean_ctor_set(v___x_819_, 3, v_options_818_);
v___x_820_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
lean_ctor_set(v___x_820_, 1, v_msgData_804_);
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0___boxed(lean_object* v_msgData_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(v_msgData_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
return v_res_828_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_829_; double v___x_830_; 
v___x_829_ = lean_unsigned_to_nat(0u);
v___x_830_ = lean_float_of_nat(v___x_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(lean_object* v_cls_834_, lean_object* v_msg_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_ref_841_; lean_object* v___x_842_; lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_888_; 
v_ref_841_ = lean_ctor_get(v___y_838_, 2);
v___x_842_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(v_msg_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_888_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_888_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_888_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; lean_object* v_traceState_848_; lean_object* v_env_849_; lean_object* v_nextMacroScope_850_; lean_object* v_ngen_851_; lean_object* v_auxDeclNGen_852_; lean_object* v_cache_853_; lean_object* v_recordedDeps_854_; lean_object* v_messages_855_; lean_object* v_infoState_856_; lean_object* v_snapshotTasks_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_887_; 
v___x_847_ = lean_st_ref_take(v___y_839_);
v_traceState_848_ = lean_ctor_get(v___x_847_, 4);
v_env_849_ = lean_ctor_get(v___x_847_, 0);
v_nextMacroScope_850_ = lean_ctor_get(v___x_847_, 1);
v_ngen_851_ = lean_ctor_get(v___x_847_, 2);
v_auxDeclNGen_852_ = lean_ctor_get(v___x_847_, 3);
v_cache_853_ = lean_ctor_get(v___x_847_, 5);
v_recordedDeps_854_ = lean_ctor_get(v___x_847_, 6);
v_messages_855_ = lean_ctor_get(v___x_847_, 7);
v_infoState_856_ = lean_ctor_get(v___x_847_, 8);
v_snapshotTasks_857_ = lean_ctor_get(v___x_847_, 9);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_887_ == 0)
{
v___x_859_ = v___x_847_;
v_isShared_860_ = v_isSharedCheck_887_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_snapshotTasks_857_);
lean_inc(v_infoState_856_);
lean_inc(v_messages_855_);
lean_inc(v_recordedDeps_854_);
lean_inc(v_cache_853_);
lean_inc(v_traceState_848_);
lean_inc(v_auxDeclNGen_852_);
lean_inc(v_ngen_851_);
lean_inc(v_nextMacroScope_850_);
lean_inc(v_env_849_);
lean_dec(v___x_847_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_887_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
uint64_t v_tid_861_; lean_object* v_traces_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_886_; 
v_tid_861_ = lean_ctor_get_uint64(v_traceState_848_, sizeof(void*)*1);
v_traces_862_ = lean_ctor_get(v_traceState_848_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v_traceState_848_);
if (v_isSharedCheck_886_ == 0)
{
v___x_864_ = v_traceState_848_;
v_isShared_865_ = v_isSharedCheck_886_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_traces_862_);
lean_dec(v_traceState_848_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_886_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_866_; lean_object* v___x_867_; double v___x_868_; uint8_t v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_866_ = lean_box(0);
v___x_867_ = lean_box(0);
v___x_868_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0);
v___x_869_ = 0;
v___x_870_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__1));
v___x_871_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_871_, 0, v_cls_834_);
lean_ctor_set(v___x_871_, 1, v___x_867_);
lean_ctor_set(v___x_871_, 2, v___x_870_);
lean_ctor_set_float(v___x_871_, sizeof(void*)*3, v___x_868_);
lean_ctor_set_float(v___x_871_, sizeof(void*)*3 + 8, v___x_868_);
lean_ctor_set_uint8(v___x_871_, sizeof(void*)*3 + 16, v___x_869_);
v___x_872_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__2));
v___x_873_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_873_, 0, v___x_871_);
lean_ctor_set(v___x_873_, 1, v_a_843_);
lean_ctor_set(v___x_873_, 2, v___x_872_);
lean_inc(v_ref_841_);
v___x_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_874_, 0, v_ref_841_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = l_Lean_PersistentArray_push___redArg(v_traces_862_, v___x_874_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_875_);
v___x_877_ = v___x_864_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_875_);
lean_ctor_set_uint64(v_reuseFailAlloc_885_, sizeof(void*)*1, v_tid_861_);
v___x_877_ = v_reuseFailAlloc_885_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
lean_object* v___x_879_; 
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 4, v___x_877_);
v___x_879_ = v___x_859_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_env_849_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v_nextMacroScope_850_);
lean_ctor_set(v_reuseFailAlloc_884_, 2, v_ngen_851_);
lean_ctor_set(v_reuseFailAlloc_884_, 3, v_auxDeclNGen_852_);
lean_ctor_set(v_reuseFailAlloc_884_, 4, v___x_877_);
lean_ctor_set(v_reuseFailAlloc_884_, 5, v_cache_853_);
lean_ctor_set(v_reuseFailAlloc_884_, 6, v_recordedDeps_854_);
lean_ctor_set(v_reuseFailAlloc_884_, 7, v_messages_855_);
lean_ctor_set(v_reuseFailAlloc_884_, 8, v_infoState_856_);
lean_ctor_set(v_reuseFailAlloc_884_, 9, v_snapshotTasks_857_);
v___x_879_ = v_reuseFailAlloc_884_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_880_ = lean_st_ref_put(v___y_839_, v___x_879_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v___x_866_);
v___x_882_ = v___x_845_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_866_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___boxed(lean_object* v_cls_889_, lean_object* v_msg_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v_cls_889_, v_msg_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
return v_res_896_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_905_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__2));
v___x_906_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4));
v___x_907_ = l_Lean_Name_append(v___x_906_, v___x_905_);
return v___x_907_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__6));
v___x_910_ = l_Lean_stringToMessageData(v___x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f(uint8_t v_kind_911_, lean_object* v_exceptionSet_912_, lean_object* v_e_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_919_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_919_, 0, v_exceptionSet_912_);
lean_ctor_set_uint8(v___x_919_, sizeof(void*)*1, v_kind_911_);
v___x_920_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0);
v___x_921_ = l_Lean_Meta_FindSplitImpl_visit(v_e_913_, v___x_919_, v___x_920_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
lean_dec_ref_known(v___x_919_, 1);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_969_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_969_ == 0)
{
v___x_924_ = v___x_921_;
v_isShared_925_ = v_isSharedCheck_969_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_921_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_969_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v_fst_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_967_; 
v_fst_926_ = lean_ctor_get(v_a_922_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v_a_922_);
if (v_isSharedCheck_967_ == 0)
{
lean_object* v_unused_968_; 
v_unused_968_ = lean_ctor_get(v_a_922_, 1);
lean_dec(v_unused_968_);
v___x_928_ = v_a_922_;
v_isShared_929_ = v_isSharedCheck_967_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_fst_926_);
lean_dec(v_a_922_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_967_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
if (lean_obj_tag(v_fst_926_) == 1)
{
lean_object* v_toCold_930_; lean_object* v_options_931_; lean_object* v_val_932_; lean_object* v_inheritedTraceOptions_933_; uint8_t v_hasTrace_934_; lean_object* v___x_936_; 
v_toCold_930_ = lean_ctor_get(v_a_916_, 0);
v_options_931_ = lean_ctor_get(v_toCold_930_, 2);
v_val_932_ = lean_ctor_get(v_fst_926_, 0);
v_inheritedTraceOptions_933_ = lean_ctor_get(v_toCold_930_, 11);
v_hasTrace_934_ = lean_ctor_get_uint8(v_options_931_, sizeof(void*)*1);
lean_inc_ref(v_fst_926_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v_fst_926_);
v___x_936_ = v___x_924_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_fst_926_);
v___x_936_ = v_reuseFailAlloc_962_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
if (v_hasTrace_934_ == 0)
{
lean_dec_ref_known(v_fst_926_, 1);
lean_del_object(v___x_928_);
return v___x_936_;
}
else
{
lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
v___x_937_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__2));
v___x_938_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5);
v___x_939_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_933_, v_options_931_, v___x_938_);
if (v___x_939_ == 0)
{
lean_dec_ref_known(v_fst_926_, 1);
lean_del_object(v___x_928_);
return v___x_936_;
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
lean_dec_ref(v___x_936_);
v___x_940_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7);
lean_inc(v_val_932_);
v___x_941_ = l_Lean_indentExpr(v_val_932_);
if (v_isShared_929_ == 0)
{
lean_ctor_set_tag(v___x_928_, 7);
lean_ctor_set(v___x_928_, 1, v___x_941_);
lean_ctor_set(v___x_928_, 0, v___x_940_);
v___x_943_ = v___x_928_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v___x_941_);
v___x_943_ = v_reuseFailAlloc_961_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_944_; 
v___x_944_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_937_, v___x_943_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_951_ == 0)
{
lean_object* v_unused_952_; 
v_unused_952_ = lean_ctor_get(v___x_944_, 0);
lean_dec(v_unused_952_);
v___x_946_ = v___x_944_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_dec(v___x_944_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v_fst_926_);
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_fst_926_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
lean_dec_ref_known(v_fst_926_, 1);
v_a_953_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_944_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_944_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
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
}
}
}
}
else
{
lean_object* v___x_963_; lean_object* v___x_965_; 
lean_del_object(v___x_928_);
lean_dec(v_fst_926_);
v___x_963_ = lean_box(0);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___x_963_);
v___x_965_ = v___x_924_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
v_a_970_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_921_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_921_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___boxed(lean_object* v_kind_978_, lean_object* v_exceptionSet_979_, lean_object* v_e_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
uint8_t v_kind_boxed_986_; lean_object* v_res_987_; 
v_kind_boxed_986_ = lean_unbox(v_kind_978_);
v_res_987_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f(v_kind_boxed_986_, v_exceptionSet_979_, v_e_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(uint8_t v_kind_988_, lean_object* v_exceptionSet_989_, lean_object* v_e_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_){
_start:
{
lean_object* v___y_997_; lean_object* v___x_1000_; 
lean_inc_ref(v_exceptionSet_989_);
v___x_1000_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f(v_kind_988_, v_exceptionSet_989_, v_e_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
if (lean_obj_tag(v_a_1001_) == 1)
{
lean_object* v_val_1002_; uint8_t v___y_1004_; uint8_t v___x_1010_; 
v_val_1002_ = lean_ctor_get(v_a_1001_, 0);
v___x_1010_ = l_Lean_Expr_isIte(v_val_1002_);
if (v___x_1010_ == 0)
{
uint8_t v___x_1011_; 
v___x_1011_ = l_Lean_Expr_isDIte(v_val_1002_);
v___y_1004_ = v___x_1011_;
goto v___jp_1003_;
}
else
{
v___y_1004_ = v___x_1010_;
goto v___jp_1003_;
}
v___jp_1003_:
{
if (v___y_1004_ == 0)
{
lean_dec_ref(v_exceptionSet_989_);
return v___x_1000_;
}
else
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
lean_inc(v_val_1002_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1005_ = lean_unsigned_to_nat(3u);
v___x_1006_ = l_Lean_Expr_getRevArg_x21(v_val_1002_, v___x_1005_);
v___x_1007_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(v_kind_988_, v_exceptionSet_989_, v___x_1006_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref_known(v___x_1007_, 1);
if (lean_obj_tag(v_a_1008_) == 0)
{
v___y_997_ = v_val_1002_;
goto v___jp_996_;
}
else
{
lean_object* v_val_1009_; 
lean_dec(v_val_1002_);
v_val_1009_ = lean_ctor_get(v_a_1008_, 0);
lean_inc(v_val_1009_);
lean_dec_ref_known(v_a_1008_, 1);
v___y_997_ = v_val_1009_;
goto v___jp_996_;
}
}
else
{
lean_dec(v_val_1002_);
return v___x_1007_;
}
}
}
}
else
{
lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1019_; 
lean_dec_ref(v_exceptionSet_989_);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1019_ == 0)
{
lean_object* v_unused_1020_; 
v_unused_1020_ = lean_ctor_get(v___x_1000_, 0);
lean_dec(v_unused_1020_);
v___x_1013_ = v___x_1000_;
v_isShared_1014_ = v_isSharedCheck_1019_;
goto v_resetjp_1012_;
}
else
{
lean_dec(v___x_1000_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1019_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1015_ = lean_box(0);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v___x_1015_);
v___x_1017_ = v___x_1013_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
else
{
lean_dec_ref(v_exceptionSet_989_);
return v___x_1000_;
}
v___jp_996_:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_998_, 0, v___y_997_);
v___x_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
return v___x_999_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go___boxed(lean_object* v_kind_1021_, lean_object* v_exceptionSet_1022_, lean_object* v_e_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_){
_start:
{
uint8_t v_kind_boxed_1029_; lean_object* v_res_1030_; 
v_kind_boxed_1029_ = lean_unbox(v_kind_1021_);
v_res_1030_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(v_kind_boxed_1029_, v_exceptionSet_1022_, v_e_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(lean_object* v_e_1031_, lean_object* v___y_1032_){
_start:
{
uint8_t v___x_1034_; 
v___x_1034_ = l_Lean_Expr_hasMVar(v_e_1031_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; 
v___x_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1035_, 0, v_e_1031_);
return v___x_1035_;
}
else
{
lean_object* v___x_1036_; lean_object* v_mctx_1037_; lean_object* v___x_1038_; lean_object* v_fst_1039_; lean_object* v_snd_1040_; lean_object* v___x_1041_; lean_object* v_cache_1042_; lean_object* v_zetaDeltaFVarIds_1043_; lean_object* v_postponed_1044_; lean_object* v_diag_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1054_; 
v___x_1036_ = lean_st_ref_get(v___y_1032_);
v_mctx_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc_ref(v_mctx_1037_);
lean_dec(v___x_1036_);
v___x_1038_ = l_Lean_instantiateMVarsCore(v_mctx_1037_, v_e_1031_);
v_fst_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_fst_1039_);
v_snd_1040_ = lean_ctor_get(v___x_1038_, 1);
lean_inc(v_snd_1040_);
lean_dec_ref(v___x_1038_);
v___x_1041_ = lean_st_ref_take(v___y_1032_);
v_cache_1042_ = lean_ctor_get(v___x_1041_, 1);
v_zetaDeltaFVarIds_1043_ = lean_ctor_get(v___x_1041_, 2);
v_postponed_1044_ = lean_ctor_get(v___x_1041_, 3);
v_diag_1045_ = lean_ctor_get(v___x_1041_, 4);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1054_ == 0)
{
lean_object* v_unused_1055_; 
v_unused_1055_ = lean_ctor_get(v___x_1041_, 0);
lean_dec(v_unused_1055_);
v___x_1047_ = v___x_1041_;
v_isShared_1048_ = v_isSharedCheck_1054_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_diag_1045_);
lean_inc(v_postponed_1044_);
lean_inc(v_zetaDeltaFVarIds_1043_);
lean_inc(v_cache_1042_);
lean_dec(v___x_1041_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1054_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 0, v_snd_1040_);
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_snd_1040_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_cache_1042_);
lean_ctor_set(v_reuseFailAlloc_1053_, 2, v_zetaDeltaFVarIds_1043_);
lean_ctor_set(v_reuseFailAlloc_1053_, 3, v_postponed_1044_);
lean_ctor_set(v_reuseFailAlloc_1053_, 4, v_diag_1045_);
v___x_1050_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = lean_st_ref_put(v___y_1032_, v___x_1050_);
v___x_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1052_, 0, v_fst_1039_);
return v___x_1052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg___boxed(lean_object* v_e_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_1056_, v___y_1057_);
lean_dec(v___y_1057_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0(lean_object* v_e_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_1060_, v___y_1062_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___boxed(lean_object* v_e_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0(v_e_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f(lean_object* v_e_1074_, uint8_t v_kind_1075_, lean_object* v_exceptionSet_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v___x_1082_; lean_object* v_a_1083_; lean_object* v___x_1084_; 
v___x_1082_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_1074_, v_a_1078_);
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_a_1083_);
lean_dec_ref(v___x_1082_);
v___x_1084_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(v_kind_1075_, v_exceptionSet_1076_, v_a_1083_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f___boxed(lean_object* v_e_1085_, lean_object* v_kind_1086_, lean_object* v_exceptionSet_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_){
_start:
{
uint8_t v_kind_boxed_1093_; lean_object* v_res_1094_; 
v_kind_boxed_1093_ = lean_unbox(v_kind_1086_);
v_res_1094_ = l_Lean_Meta_findSplit_x3f(v_e_1085_, v_kind_boxed_1093_, v_exceptionSet_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
lean_dec(v_a_1089_);
lean_dec_ref(v_a_1088_);
return v_res_1094_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0(void){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1095_ = lean_box(0);
v___x_1096_ = lean_unsigned_to_nat(16u);
v___x_1097_ = lean_mk_array(v___x_1096_, v___x_1095_);
return v___x_1097_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1098_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0);
v___x_1099_ = lean_unsigned_to_nat(0u);
v___x_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
lean_ctor_set(v___x_1100_, 1, v___x_1098_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(lean_object* v_e_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
uint8_t v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1107_ = 0;
v___x_1108_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1);
v___x_1109_ = l_Lean_Meta_findSplit_x3f(v_e_1101_, v___x_1107_, v___x_1108_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1134_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1112_ = v___x_1109_;
v_isShared_1113_ = v_isSharedCheck_1134_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1109_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1134_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
if (lean_obj_tag(v_a_1110_) == 1)
{
lean_object* v_val_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1129_; 
v_val_1114_ = lean_ctor_get(v_a_1110_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_a_1110_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1116_ = v_a_1110_;
v_isShared_1117_ = v_isSharedCheck_1129_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_val_1114_);
lean_dec(v_a_1110_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1129_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1124_; 
v___x_1118_ = lean_unsigned_to_nat(3u);
v___x_1119_ = l_Lean_Expr_getRevArg_x21(v_val_1114_, v___x_1118_);
v___x_1120_ = lean_unsigned_to_nat(2u);
v___x_1121_ = l_Lean_Expr_getRevArg_x21(v_val_1114_, v___x_1120_);
lean_dec(v_val_1114_);
v___x_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1119_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 0, v___x_1122_);
v___x_1124_ = v___x_1116_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
lean_object* v___x_1126_; 
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v___x_1124_);
v___x_1126_ = v___x_1112_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
lean_dec(v_a_1110_);
v___x_1130_ = lean_box(0);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v___x_1130_);
v___x_1132_ = v___x_1112_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
v_a_1135_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1109_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1109_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___boxed(lean_object* v_e_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(v_e_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(lean_object* v_name_1150_, lean_object* v_decl_1151_, lean_object* v_ref_1152_){
_start:
{
lean_object* v_defValue_1154_; lean_object* v_descr_1155_; lean_object* v_deprecation_x3f_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v_defValue_1154_ = lean_ctor_get(v_decl_1151_, 0);
v_descr_1155_ = lean_ctor_get(v_decl_1151_, 1);
v_deprecation_x3f_1156_ = lean_ctor_get(v_decl_1151_, 2);
v___x_1157_ = lean_alloc_ctor(1, 0, 1);
v___x_1158_ = lean_unbox(v_defValue_1154_);
lean_ctor_set_uint8(v___x_1157_, 0, v___x_1158_);
lean_inc(v_deprecation_x3f_1156_);
lean_inc_ref(v_descr_1155_);
lean_inc_n(v_name_1150_, 2);
v___x_1159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1159_, 0, v_name_1150_);
lean_ctor_set(v___x_1159_, 1, v_ref_1152_);
lean_ctor_set(v___x_1159_, 2, v___x_1157_);
lean_ctor_set(v___x_1159_, 3, v_descr_1155_);
lean_ctor_set(v___x_1159_, 4, v_deprecation_x3f_1156_);
v___x_1160_ = lean_register_option(v_name_1150_, v___x_1159_);
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
lean_inc(v_defValue_1154_);
v___x_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1164_, 0, v_name_1150_);
lean_ctor_set(v___x_1164_, 1, v_defValue_1154_);
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
lean_dec(v_name_1150_);
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
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1178_, lean_object* v_decl_1179_, lean_object* v_ref_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(v_name_1178_, v_decl_1179_, v_ref_1180_);
lean_dec_ref(v_decl_1179_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1201_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_));
v___x_1202_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_));
v___x_1203_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_));
v___x_1204_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(v___x_1201_, v___x_1202_, v___x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4____boxed(lean_object* v_a_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_();
return v_res_1206_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1207_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__0);
v___x_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg(){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__1);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___boxed(lean_object* v___dummy_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg();
return v_res_1213_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg();
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0(lean_object* v_00_u03b2_1215_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0);
return v___x_1216_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__0);
v___x_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___redArg(){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___redArg___closed__0);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___redArg___boxed(lean_object* v___dummy_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___redArg();
return v_res_1222_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___redArg();
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1(lean_object* v_00_u03b2_1224_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0);
return v___x_1225_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__0(void){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Lean_Meta_DiscrTree_empty___redArg();
return v___x_1226_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__1(void){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__0);
v___x_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
return v___x_1228_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__2(void){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v_s_1233_; 
v___x_1229_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__1, &l_Lean_Meta_SplitIf_getSimpContext___closed__1_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__1);
v___x_1230_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0);
v___x_1231_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0);
v___x_1232_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__0, &l_Lean_Meta_SplitIf_getSimpContext___closed__0_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__0);
v_s_1233_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_s_1233_, 0, v___x_1232_);
lean_ctor_set(v_s_1233_, 1, v___x_1232_);
lean_ctor_set(v_s_1233_, 2, v___x_1231_);
lean_ctor_set(v_s_1233_, 3, v___x_1230_);
lean_ctor_set(v_s_1233_, 4, v___x_1231_);
lean_ctor_set(v_s_1233_, 5, v___x_1229_);
return v_s_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_getSimpContext(lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_){
_start:
{
lean_object* v_s_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; uint8_t v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v_s_1251_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__2, &l_Lean_Meta_SplitIf_getSimpContext___closed__2_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__2);
v___x_1252_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__4));
v___x_1253_ = 1;
v___x_1254_ = 0;
v___x_1255_ = lean_unsigned_to_nat(1000u);
v___x_1256_ = l_Lean_Meta_SimpTheorems_addConst(v_s_1251_, v___x_1252_, v___x_1253_, v___x_1254_, v___x_1255_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_a_1257_);
lean_dec_ref_known(v___x_1256_, 1);
v___x_1258_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__6));
v___x_1259_ = l_Lean_Meta_SimpTheorems_addConst(v_a_1257_, v___x_1258_, v___x_1253_, v___x_1254_, v___x_1255_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_a_1260_);
lean_dec_ref_known(v___x_1259_, 1);
v___x_1261_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__8));
v___x_1262_ = l_Lean_Meta_SimpTheorems_addConst(v_a_1260_, v___x_1261_, v___x_1253_, v___x_1254_, v___x_1255_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_a_1263_);
lean_dec_ref_known(v___x_1262_, 1);
v___x_1264_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__10));
v___x_1265_ = l_Lean_Meta_SimpTheorems_addConst(v_a_1263_, v___x_1264_, v___x_1253_, v___x_1254_, v___x_1255_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1267_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_a_1266_);
lean_dec_ref_known(v___x_1265_, 1);
v___x_1267_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_1249_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; lean_object* v___x_1269_; lean_object* v_maxSteps_1270_; lean_object* v_maxDischargeDepth_1271_; uint8_t v_contextual_1272_; uint8_t v_memoize_1273_; uint8_t v_singlePass_1274_; uint8_t v_zeta_1275_; uint8_t v_beta_1276_; uint8_t v_eta_1277_; uint8_t v_etaStruct_1278_; uint8_t v_iota_1279_; uint8_t v_proj_1280_; uint8_t v_decide_1281_; uint8_t v_arith_1282_; uint8_t v_autoUnfold_1283_; uint8_t v_failIfUnchanged_1284_; uint8_t v_ground_1285_; uint8_t v_unfoldPartialApp_1286_; uint8_t v_zetaDelta_1287_; uint8_t v_index_1288_; uint8_t v_implicitDefEqProofs_1289_; uint8_t v_zetaUnused_1290_; uint8_t v_catchRuntime_1291_; uint8_t v_zetaHave_1292_; uint8_t v_congrConsts_1293_; uint8_t v_bitVecOfNat_1294_; uint8_t v_warnExponents_1295_; uint8_t v_suggestions_1296_; lean_object* v_maxSuggestions_1297_; uint8_t v_locals_1298_; uint8_t v_instances_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
lean_dec_ref_known(v___x_1267_, 1);
v___x_1269_ = l_Lean_Meta_Simp_neutralConfig;
v_maxSteps_1270_ = lean_ctor_get(v___x_1269_, 0);
v_maxDischargeDepth_1271_ = lean_ctor_get(v___x_1269_, 1);
v_contextual_1272_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*3);
v_memoize_1273_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*3 + 1);
v_singlePass_1274_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*3 + 2);
v_zeta_1275_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*3 + 3);
v_beta_1276_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*3 + 4);
v_eta_1277_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*3 + 5);
v_etaStruct_1278_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*3 + 6);
v_iota_1279_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*3 + 7);
v_proj_1280_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*3 + 8);
v_decide_1281_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*3 + 9);
v_arith_1282_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*3 + 10);
v_autoUnfold_1283_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*3 + 11);
v_failIfUnchanged_1284_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*3 + 13);
v_ground_1285_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_1286_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*3 + 15);
v_zetaDelta_1287_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*3 + 16);
v_index_1288_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_1289_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*3 + 18);
v_zetaUnused_1290_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*3 + 19);
v_catchRuntime_1291_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*3 + 20);
v_zetaHave_1292_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*3 + 21);
v_congrConsts_1293_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*3 + 23);
v_bitVecOfNat_1294_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*3 + 24);
v_warnExponents_1295_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*3 + 25);
v_suggestions_1296_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*3 + 26);
v_maxSuggestions_1297_ = lean_ctor_get(v___x_1269_, 2);
v_locals_1298_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*3 + 27);
v_instances_1299_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*3 + 28);
lean_inc(v_maxSuggestions_1297_);
lean_inc(v_maxDischargeDepth_1271_);
lean_inc(v_maxSteps_1270_);
v___x_1300_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1300_, 0, v_maxSteps_1270_);
lean_ctor_set(v___x_1300_, 1, v_maxDischargeDepth_1271_);
lean_ctor_set(v___x_1300_, 2, v_maxSuggestions_1297_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3, v_contextual_1272_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 1, v_memoize_1273_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 2, v_singlePass_1274_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 3, v_zeta_1275_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 4, v_beta_1276_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 5, v_eta_1277_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 6, v_etaStruct_1278_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 7, v_iota_1279_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 8, v_proj_1280_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 9, v_decide_1281_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 10, v_arith_1282_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 11, v_autoUnfold_1283_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 12, v___x_1254_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 13, v_failIfUnchanged_1284_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 14, v_ground_1285_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 15, v_unfoldPartialApp_1286_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 16, v_zetaDelta_1287_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 17, v_index_1288_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_1289_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 19, v_zetaUnused_1290_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 20, v_catchRuntime_1291_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 21, v_zetaHave_1292_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 22, v___x_1253_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 23, v_congrConsts_1293_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 24, v_bitVecOfNat_1294_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 25, v_warnExponents_1295_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 26, v_suggestions_1296_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 27, v_locals_1298_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 28, v_instances_1299_);
v___x_1301_ = lean_unsigned_to_nat(1u);
v___x_1302_ = lean_mk_empty_array_with_capacity(v___x_1301_);
v___x_1303_ = lean_array_push(v___x_1302_, v_a_1266_);
v___x_1304_ = l_Lean_Options_empty;
v___x_1305_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1300_, v___x_1303_, v_a_1268_, v___x_1304_, v_a_1246_, v_a_1248_, v_a_1249_);
return v___x_1305_;
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec(v_a_1266_);
v_a_1306_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1267_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1267_);
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
v_a_1314_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1265_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1265_);
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
else
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
v_a_1322_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1262_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1262_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
v_a_1330_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1259_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1259_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
v_a_1338_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1256_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1256_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_getSimpContext___boxed(lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
lean_dec(v_a_1349_);
lean_dec_ref(v_a_1348_);
lean_dec(v_a_1347_);
lean_dec_ref(v_a_1346_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_1356_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_a_1359_; lean_object* v___x_1360_; lean_object* v_maxSteps_1361_; lean_object* v_maxDischargeDepth_1362_; uint8_t v_contextual_1363_; uint8_t v_memoize_1364_; uint8_t v_singlePass_1365_; uint8_t v_zeta_1366_; uint8_t v_beta_1367_; uint8_t v_eta_1368_; uint8_t v_etaStruct_1369_; uint8_t v_iota_1370_; uint8_t v_proj_1371_; uint8_t v_decide_1372_; uint8_t v_arith_1373_; uint8_t v_autoUnfold_1374_; uint8_t v_failIfUnchanged_1375_; uint8_t v_ground_1376_; uint8_t v_unfoldPartialApp_1377_; uint8_t v_zetaDelta_1378_; uint8_t v_index_1379_; uint8_t v_implicitDefEqProofs_1380_; uint8_t v_zetaUnused_1381_; uint8_t v_catchRuntime_1382_; uint8_t v_zetaHave_1383_; uint8_t v_congrConsts_1384_; uint8_t v_bitVecOfNat_1385_; uint8_t v_warnExponents_1386_; uint8_t v_suggestions_1387_; lean_object* v_maxSuggestions_1388_; uint8_t v_locals_1389_; uint8_t v_instances_1390_; uint8_t v___x_1391_; uint8_t v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_a_1359_);
lean_dec_ref_known(v___x_1358_, 1);
v___x_1360_ = l_Lean_Meta_Simp_neutralConfig;
v_maxSteps_1361_ = lean_ctor_get(v___x_1360_, 0);
v_maxDischargeDepth_1362_ = lean_ctor_get(v___x_1360_, 1);
v_contextual_1363_ = lean_ctor_get_uint8(v___x_1360_, sizeof(void*)*3);
v_memoize_1364_ = lean_ctor_get_uint8(v___x_1360_, sizeof(void*)*3 + 1);
v_singlePass_1365_ = lean_ctor_get_uint8(v___x_1360_, sizeof(void*)*3 + 2);
v_zeta_1366_ = lean_ctor_get_uint8(v___x_1360_, sizeof(void*)*3 + 3);
v_beta_1367_ = lean_ctor_get_uint8(v___x_1360_, sizeof(void*)*3 + 4);
v_eta_1368_ = lean_ctor_get_uint8(v___x_1360_, sizeof(void*)*3 + 5);
v_etaStruct_1369_ = lean_ctor_get_uint8(v___x_1360_, sizeof(void*)*3 + 6);
v_iota_1370_ = lean_ctor_get_uint8(v___x_1360_, sizeof(void*)*3 + 7);
v_proj_1371_ = lean_ctor_get_uint8(v___x_1360_, sizeof(void*)*3 + 8);
v_decide_1372_ = lean_ctor_get_uint8(v___x_1360_, sizeof(void*)*3 + 9);
v_arith_1373_ = lean_ctor_get_uint8(v___x_1360_, sizeof(void*)*3 + 10);
v_autoUnfold_1374_ = lean_ctor_get_uint8(v___x_1360_, sizeof(void*)*3 + 11);
v_failIfUnchanged_1375_ = lean_ctor_get_uint8(v___x_1360_, sizeof(void*)*3 + 13);
v_ground_1376_ = lean_ctor_get_uint8(v___x_1360_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_1377_ = lean_ctor_get_uint8(v___x_1360_, sizeof(void*)*3 + 15);
v_zetaDelta_1378_ = lean_ctor_get_uint8(v___x_1360_, sizeof(void*)*3 + 16);
v_index_1379_ = lean_ctor_get_uint8(v___x_1360_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_1380_ = lean_ctor_get_uint8(v___x_1360_, sizeof(void*)*3 + 18);
v_zetaUnused_1381_ = lean_ctor_get_uint8(v___x_1360_, sizeof(void*)*3 + 19);
v_catchRuntime_1382_ = lean_ctor_get_uint8(v___x_1360_, sizeof(void*)*3 + 20);
v_zetaHave_1383_ = lean_ctor_get_uint8(v___x_1360_, sizeof(void*)*3 + 21);
v_congrConsts_1384_ = lean_ctor_get_uint8(v___x_1360_, sizeof(void*)*3 + 23);
v_bitVecOfNat_1385_ = lean_ctor_get_uint8(v___x_1360_, sizeof(void*)*3 + 24);
v_warnExponents_1386_ = lean_ctor_get_uint8(v___x_1360_, sizeof(void*)*3 + 25);
v_suggestions_1387_ = lean_ctor_get_uint8(v___x_1360_, sizeof(void*)*3 + 26);
v_maxSuggestions_1388_ = lean_ctor_get(v___x_1360_, 2);
v_locals_1389_ = lean_ctor_get_uint8(v___x_1360_, sizeof(void*)*3 + 27);
v_instances_1390_ = lean_ctor_get_uint8(v___x_1360_, sizeof(void*)*3 + 28);
v___x_1391_ = 0;
v___x_1392_ = 1;
lean_inc(v_maxSuggestions_1388_);
lean_inc(v_maxDischargeDepth_1362_);
lean_inc(v_maxSteps_1361_);
v___x_1393_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1393_, 0, v_maxSteps_1361_);
lean_ctor_set(v___x_1393_, 1, v_maxDischargeDepth_1362_);
lean_ctor_set(v___x_1393_, 2, v_maxSuggestions_1388_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3, v_contextual_1363_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3 + 1, v_memoize_1364_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3 + 2, v_singlePass_1365_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3 + 3, v_zeta_1366_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3 + 4, v_beta_1367_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3 + 5, v_eta_1368_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3 + 6, v_etaStruct_1369_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3 + 7, v_iota_1370_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3 + 8, v_proj_1371_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3 + 9, v_decide_1372_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3 + 10, v_arith_1373_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3 + 11, v_autoUnfold_1374_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3 + 12, v___x_1391_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3 + 13, v_failIfUnchanged_1375_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3 + 14, v_ground_1376_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3 + 15, v_unfoldPartialApp_1377_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3 + 16, v_zetaDelta_1378_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3 + 17, v_index_1379_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_1380_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3 + 19, v_zetaUnused_1381_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3 + 20, v_catchRuntime_1382_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3 + 21, v_zetaHave_1383_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3 + 22, v___x_1392_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3 + 23, v_congrConsts_1384_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3 + 24, v_bitVecOfNat_1385_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3 + 25, v_warnExponents_1386_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3 + 26, v_suggestions_1387_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3 + 27, v_locals_1389_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*3 + 28, v_instances_1390_);
v___x_1394_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg___closed__0));
v___x_1395_ = l_Lean_Options_empty;
v___x_1396_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1393_, v___x_1394_, v_a_1359_, v___x_1395_, v_a_1354_, v_a_1355_, v_a_1356_);
return v___x_1396_;
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
v_a_1397_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1358_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1358_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg___boxed(lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_1405_, v_a_1406_, v_a_1407_);
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
lean_dec_ref(v_a_1405_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27(lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_1410_, v_a_1412_, v_a_1413_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___boxed(lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27(v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
lean_dec(v_a_1419_);
lean_dec_ref(v_a_1418_);
lean_dec(v_a_1417_);
lean_dec_ref(v_a_1416_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(lean_object* v_e_1422_, lean_object* v___y_1423_){
_start:
{
uint8_t v___x_1425_; 
v___x_1425_ = l_Lean_Expr_hasMVar(v_e_1422_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1426_; 
v___x_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1426_, 0, v_e_1422_);
return v___x_1426_;
}
else
{
lean_object* v___x_1427_; lean_object* v_mctx_1428_; lean_object* v___x_1429_; lean_object* v_fst_1430_; lean_object* v_snd_1431_; lean_object* v___x_1432_; lean_object* v_cache_1433_; lean_object* v_zetaDeltaFVarIds_1434_; lean_object* v_postponed_1435_; lean_object* v_diag_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1445_; 
v___x_1427_ = lean_st_ref_get(v___y_1423_);
v_mctx_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc_ref(v_mctx_1428_);
lean_dec(v___x_1427_);
v___x_1429_ = l_Lean_instantiateMVarsCore(v_mctx_1428_, v_e_1422_);
v_fst_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_fst_1430_);
v_snd_1431_ = lean_ctor_get(v___x_1429_, 1);
lean_inc(v_snd_1431_);
lean_dec_ref(v___x_1429_);
v___x_1432_ = lean_st_ref_take(v___y_1423_);
v_cache_1433_ = lean_ctor_get(v___x_1432_, 1);
v_zetaDeltaFVarIds_1434_ = lean_ctor_get(v___x_1432_, 2);
v_postponed_1435_ = lean_ctor_get(v___x_1432_, 3);
v_diag_1436_ = lean_ctor_get(v___x_1432_, 4);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1445_ == 0)
{
lean_object* v_unused_1446_; 
v_unused_1446_ = lean_ctor_get(v___x_1432_, 0);
lean_dec(v_unused_1446_);
v___x_1438_ = v___x_1432_;
v_isShared_1439_ = v_isSharedCheck_1445_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_diag_1436_);
lean_inc(v_postponed_1435_);
lean_inc(v_zetaDeltaFVarIds_1434_);
lean_inc(v_cache_1433_);
lean_dec(v___x_1432_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1445_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v_snd_1431_);
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_snd_1431_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_cache_1433_);
lean_ctor_set(v_reuseFailAlloc_1444_, 2, v_zetaDeltaFVarIds_1434_);
lean_ctor_set(v_reuseFailAlloc_1444_, 3, v_postponed_1435_);
lean_ctor_set(v_reuseFailAlloc_1444_, 4, v_diag_1436_);
v___x_1441_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1442_ = lean_st_ref_put(v___y_1423_, v___x_1441_);
v___x_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1443_, 0, v_fst_1430_);
return v___x_1443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg___boxed(lean_object* v_e_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_e_1447_, v___y_1448_);
lean_dec(v___y_1448_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0(lean_object* v_e_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_e_1451_, v___y_1456_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___boxed(lean_object* v_e_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0(v_e_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(lean_object* v_cls_1471_, lean_object* v_msg_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v_ref_1478_; lean_object* v___x_1479_; lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1525_; 
v_ref_1478_ = lean_ctor_get(v___y_1475_, 2);
v___x_1479_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(v_msg_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1482_ = v___x_1479_;
v_isShared_1483_ = v_isSharedCheck_1525_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1479_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1525_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1484_; lean_object* v_traceState_1485_; lean_object* v_env_1486_; lean_object* v_nextMacroScope_1487_; lean_object* v_ngen_1488_; lean_object* v_auxDeclNGen_1489_; lean_object* v_cache_1490_; lean_object* v_recordedDeps_1491_; lean_object* v_messages_1492_; lean_object* v_infoState_1493_; lean_object* v_snapshotTasks_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1524_; 
v___x_1484_ = lean_st_ref_take(v___y_1476_);
v_traceState_1485_ = lean_ctor_get(v___x_1484_, 4);
v_env_1486_ = lean_ctor_get(v___x_1484_, 0);
v_nextMacroScope_1487_ = lean_ctor_get(v___x_1484_, 1);
v_ngen_1488_ = lean_ctor_get(v___x_1484_, 2);
v_auxDeclNGen_1489_ = lean_ctor_get(v___x_1484_, 3);
v_cache_1490_ = lean_ctor_get(v___x_1484_, 5);
v_recordedDeps_1491_ = lean_ctor_get(v___x_1484_, 6);
v_messages_1492_ = lean_ctor_get(v___x_1484_, 7);
v_infoState_1493_ = lean_ctor_get(v___x_1484_, 8);
v_snapshotTasks_1494_ = lean_ctor_get(v___x_1484_, 9);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1496_ = v___x_1484_;
v_isShared_1497_ = v_isSharedCheck_1524_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_snapshotTasks_1494_);
lean_inc(v_infoState_1493_);
lean_inc(v_messages_1492_);
lean_inc(v_recordedDeps_1491_);
lean_inc(v_cache_1490_);
lean_inc(v_traceState_1485_);
lean_inc(v_auxDeclNGen_1489_);
lean_inc(v_ngen_1488_);
lean_inc(v_nextMacroScope_1487_);
lean_inc(v_env_1486_);
lean_dec(v___x_1484_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1524_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
uint64_t v_tid_1498_; lean_object* v_traces_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1523_; 
v_tid_1498_ = lean_ctor_get_uint64(v_traceState_1485_, sizeof(void*)*1);
v_traces_1499_ = lean_ctor_get(v_traceState_1485_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v_traceState_1485_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1501_ = v_traceState_1485_;
v_isShared_1502_ = v_isSharedCheck_1523_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_traces_1499_);
lean_dec(v_traceState_1485_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1523_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; double v___x_1505_; uint8_t v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1514_; 
v___x_1503_ = lean_box(0);
v___x_1504_ = lean_box(0);
v___x_1505_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0);
v___x_1506_ = 0;
v___x_1507_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__1));
v___x_1508_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1508_, 0, v_cls_1471_);
lean_ctor_set(v___x_1508_, 1, v___x_1504_);
lean_ctor_set(v___x_1508_, 2, v___x_1507_);
lean_ctor_set_float(v___x_1508_, sizeof(void*)*3, v___x_1505_);
lean_ctor_set_float(v___x_1508_, sizeof(void*)*3 + 8, v___x_1505_);
lean_ctor_set_uint8(v___x_1508_, sizeof(void*)*3 + 16, v___x_1506_);
v___x_1509_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__2));
v___x_1510_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1508_);
lean_ctor_set(v___x_1510_, 1, v_a_1480_);
lean_ctor_set(v___x_1510_, 2, v___x_1509_);
lean_inc(v_ref_1478_);
v___x_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1511_, 0, v_ref_1478_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
v___x_1512_ = l_Lean_PersistentArray_push___redArg(v_traces_1499_, v___x_1511_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 0, v___x_1512_);
v___x_1514_ = v___x_1501_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1512_);
lean_ctor_set_uint64(v_reuseFailAlloc_1522_, sizeof(void*)*1, v_tid_1498_);
v___x_1514_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1516_; 
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 4, v___x_1514_);
v___x_1516_ = v___x_1496_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_env_1486_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v_nextMacroScope_1487_);
lean_ctor_set(v_reuseFailAlloc_1521_, 2, v_ngen_1488_);
lean_ctor_set(v_reuseFailAlloc_1521_, 3, v_auxDeclNGen_1489_);
lean_ctor_set(v_reuseFailAlloc_1521_, 4, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1521_, 5, v_cache_1490_);
lean_ctor_set(v_reuseFailAlloc_1521_, 6, v_recordedDeps_1491_);
lean_ctor_set(v_reuseFailAlloc_1521_, 7, v_messages_1492_);
lean_ctor_set(v_reuseFailAlloc_1521_, 8, v_infoState_1493_);
lean_ctor_set(v_reuseFailAlloc_1521_, 9, v_snapshotTasks_1494_);
v___x_1516_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
lean_object* v___x_1517_; lean_object* v___x_1519_; 
v___x_1517_ = lean_st_ref_put(v___y_1476_, v___x_1516_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 0, v___x_1503_);
v___x_1519_ = v___x_1482_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1503_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg___boxed(lean_object* v_cls_1526_, lean_object* v_msg_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v_cls_1526_, v_msg_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
return v_res_1533_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1540_ = lean_box(0);
v___x_1541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__3));
v___x_1542_ = l_Lean_mkConst(v___x_1541_, v___x_1540_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(lean_object* v_numIndices_1543_, lean_object* v_a_1544_, lean_object* v_as_1545_, lean_object* v_i_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v_zero_1552_; uint8_t v_isZero_1553_; 
v_zero_1552_ = lean_unsigned_to_nat(0u);
v_isZero_1553_ = lean_nat_dec_eq(v_i_1546_, v_zero_1552_);
if (v_isZero_1553_ == 1)
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
lean_dec(v_i_1546_);
lean_dec_ref(v_a_1544_);
v___x_1554_ = lean_box(0);
v___x_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
return v___x_1555_;
}
else
{
lean_object* v_one_1556_; lean_object* v_n_1557_; lean_object* v___x_1558_; 
v_one_1556_ = lean_unsigned_to_nat(1u);
v_n_1557_ = lean_nat_sub(v_i_1546_, v_one_1556_);
lean_dec(v_i_1546_);
v___x_1558_ = lean_array_fget(v_as_1545_, v_n_1557_);
if (lean_obj_tag(v___x_1558_) == 0)
{
v_i_1546_ = v_n_1557_;
goto _start;
}
else
{
lean_object* v_val_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1624_; 
v_val_1560_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1562_ = v___x_1558_;
v_isShared_1563_ = v_isSharedCheck_1624_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_val_1560_);
lean_dec(v___x_1558_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1624_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; uint8_t v___x_1565_; 
v___x_1564_ = l_Lean_LocalDecl_index(v_val_1560_);
v___x_1565_ = lean_nat_dec_le(v_numIndices_1543_, v___x_1564_);
lean_dec(v___x_1564_);
if (v___x_1565_ == 0)
{
uint8_t v___x_1566_; 
v___x_1566_ = l_Lean_LocalDecl_isAuxDecl(v_val_1560_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1567_ = l_Lean_LocalDecl_type(v_val_1560_);
lean_inc_ref(v___x_1567_);
lean_inc_ref(v_a_1544_);
v___x_1568_ = l_Lean_Meta_isExprDefEq(v_a_1544_, v___x_1567_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1613_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1571_ = v___x_1568_;
v_isShared_1572_ = v_isSharedCheck_1613_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1568_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1613_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
uint8_t v___x_1573_; 
v___x_1573_ = lean_unbox(v_a_1569_);
lean_dec(v_a_1569_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; uint8_t v___x_1575_; 
lean_del_object(v___x_1571_);
v___x_1574_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__1));
v___x_1575_ = l_Lean_Expr_isAppOfArity(v_a_1544_, v___x_1574_, v_one_1556_);
if (v___x_1575_ == 0)
{
lean_dec_ref(v___x_1567_);
lean_del_object(v___x_1562_);
lean_dec(v_val_1560_);
v_i_1546_ = v_n_1557_;
goto _start;
}
else
{
lean_object* v___x_1577_; uint8_t v___x_1578_; 
v___x_1577_ = l_Lean_Expr_appArg_x21(v_a_1544_);
v___x_1578_ = l_Lean_Expr_isAppOfArity(v___x_1577_, v___x_1574_, v_one_1556_);
if (v___x_1578_ == 0)
{
lean_dec_ref(v___x_1577_);
lean_dec_ref(v___x_1567_);
lean_del_object(v___x_1562_);
lean_dec(v_val_1560_);
v_i_1546_ = v_n_1557_;
goto _start;
}
else
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = l_Lean_Expr_appArg_x21(v___x_1577_);
lean_dec_ref(v___x_1577_);
lean_inc_ref(v___x_1580_);
v___x_1581_ = l_Lean_Meta_isExprDefEq(v___x_1580_, v___x_1567_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1597_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1584_ = v___x_1581_;
v_isShared_1585_ = v_isSharedCheck_1597_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1581_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1597_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
uint8_t v___x_1586_; 
v___x_1586_ = lean_unbox(v_a_1582_);
lean_dec(v_a_1582_);
if (v___x_1586_ == 0)
{
lean_del_object(v___x_1584_);
lean_dec_ref(v___x_1580_);
lean_del_object(v___x_1562_);
lean_dec(v_val_1560_);
v_i_1546_ = v_n_1557_;
goto _start;
}
else
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1592_; 
lean_dec(v_n_1557_);
lean_dec_ref(v_a_1544_);
v___x_1588_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4);
v___x_1589_ = l_Lean_LocalDecl_toExpr(v_val_1560_);
v___x_1590_ = l_Lean_mkAppB(v___x_1588_, v___x_1580_, v___x_1589_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1590_);
v___x_1592_ = v___x_1562_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1590_);
v___x_1592_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
lean_object* v___x_1594_; 
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 0, v___x_1592_);
v___x_1594_ = v___x_1584_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1592_);
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
}
else
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
lean_dec_ref(v___x_1580_);
lean_del_object(v___x_1562_);
lean_dec(v_val_1560_);
lean_dec(v_n_1557_);
lean_dec_ref(v_a_1544_);
v_a_1598_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1581_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1581_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
}
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1608_; 
lean_dec_ref(v___x_1567_);
lean_dec(v_n_1557_);
lean_dec_ref(v_a_1544_);
v___x_1606_ = l_Lean_LocalDecl_toExpr(v_val_1560_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1606_);
v___x_1608_ = v___x_1562_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1606_);
v___x_1608_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
lean_object* v___x_1610_; 
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 0, v___x_1608_);
v___x_1610_ = v___x_1571_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1608_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
lean_dec_ref(v___x_1567_);
lean_del_object(v___x_1562_);
lean_dec(v_val_1560_);
lean_dec(v_n_1557_);
lean_dec_ref(v_a_1544_);
v_a_1614_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1568_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1568_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1614_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
else
{
lean_del_object(v___x_1562_);
lean_dec(v_val_1560_);
v_i_1546_ = v_n_1557_;
goto _start;
}
}
else
{
lean_del_object(v___x_1562_);
lean_dec(v_val_1560_);
v_i_1546_ = v_n_1557_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_numIndices_1625_, lean_object* v_a_1626_, lean_object* v_as_1627_, lean_object* v_i_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_numIndices_1625_, v_a_1626_, v_as_1627_, v_i_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec_ref(v_as_1627_);
lean_dec(v_numIndices_1625_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(lean_object* v_numIndices_1635_, lean_object* v_a_1636_, lean_object* v_as_1637_, lean_object* v_i_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v_zero_1647_; uint8_t v_isZero_1648_; 
v_zero_1647_ = lean_unsigned_to_nat(0u);
v_isZero_1648_ = lean_nat_dec_eq(v_i_1638_, v_zero_1647_);
if (v_isZero_1648_ == 1)
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_dec(v_i_1638_);
lean_dec_ref(v_a_1636_);
v___x_1649_ = lean_box(0);
v___x_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1649_);
return v___x_1650_;
}
else
{
lean_object* v_one_1651_; lean_object* v_n_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v_one_1651_ = lean_unsigned_to_nat(1u);
v_n_1652_ = lean_nat_sub(v_i_1638_, v_one_1651_);
lean_dec(v_i_1638_);
v___x_1653_ = lean_array_fget_borrowed(v_as_1637_, v_n_1652_);
lean_inc_ref(v_a_1636_);
v___x_1654_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_numIndices_1635_, v_a_1636_, v___x_1653_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
if (lean_obj_tag(v_a_1655_) == 0)
{
lean_dec_ref_known(v___x_1654_, 1);
v_i_1638_ = v_n_1652_;
goto _start;
}
else
{
lean_dec(v_n_1652_);
lean_dec_ref(v_a_1636_);
return v___x_1654_;
}
}
else
{
lean_dec(v_n_1652_);
lean_dec_ref(v_a_1636_);
return v___x_1654_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(lean_object* v_numIndices_1657_, lean_object* v_a_1658_, lean_object* v_x_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
if (lean_obj_tag(v_x_1659_) == 0)
{
lean_object* v_cs_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v_cs_1668_ = lean_ctor_get(v_x_1659_, 0);
v___x_1669_ = lean_array_get_size(v_cs_1668_);
v___x_1670_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_numIndices_1657_, v_a_1658_, v_cs_1668_, v___x_1669_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
return v___x_1670_;
}
else
{
lean_object* v_vs_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v_vs_1671_ = lean_ctor_get(v_x_1659_, 0);
v___x_1672_ = lean_array_get_size(v_vs_1671_);
v___x_1673_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_numIndices_1657_, v_a_1658_, v_vs_1671_, v___x_1672_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
return v___x_1673_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3___boxed(lean_object* v_numIndices_1674_, lean_object* v_a_1675_, lean_object* v_x_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_numIndices_1674_, v_a_1675_, v_x_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec_ref(v_x_1676_);
lean_dec(v_numIndices_1674_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_numIndices_1686_, lean_object* v_a_1687_, lean_object* v_as_1688_, lean_object* v_i_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_numIndices_1686_, v_a_1687_, v_as_1688_, v_i_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v_as_1688_);
lean_dec(v_numIndices_1686_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(lean_object* v_numIndices_1699_, lean_object* v_a_1700_, lean_object* v_t_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v_root_1710_; lean_object* v_tail_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v_root_1710_ = lean_ctor_get(v_t_1701_, 0);
v_tail_1711_ = lean_ctor_get(v_t_1701_, 1);
v___x_1712_ = lean_array_get_size(v_tail_1711_);
lean_inc_ref(v_a_1700_);
v___x_1713_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_numIndices_1699_, v_a_1700_, v_tail_1711_, v___x_1712_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_a_1714_; 
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
if (lean_obj_tag(v_a_1714_) == 0)
{
lean_object* v___x_1715_; 
lean_dec_ref_known(v___x_1713_, 1);
v___x_1715_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_numIndices_1699_, v_a_1700_, v_root_1710_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
return v___x_1715_;
}
else
{
lean_dec_ref(v_a_1700_);
return v___x_1713_;
}
}
else
{
lean_dec_ref(v_a_1700_);
return v___x_1713_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1___boxed(lean_object* v_numIndices_1716_, lean_object* v_a_1717_, lean_object* v_t_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(v_numIndices_1716_, v_a_1717_, v_t_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v_t_1718_);
lean_dec(v_numIndices_1716_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(lean_object* v_numIndices_1728_, lean_object* v_a_1729_, lean_object* v_lctx_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_decls_1739_; lean_object* v___x_1740_; 
v_decls_1739_ = lean_ctor_get(v_lctx_1730_, 1);
v___x_1740_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(v_numIndices_1728_, v_a_1729_, v_decls_1739_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1___boxed(lean_object* v_numIndices_1741_, lean_object* v_a_1742_, lean_object* v_lctx_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(v_numIndices_1741_, v_a_1742_, v_lctx_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec(v___y_1744_);
lean_dec_ref(v_lctx_1743_);
lean_dec(v_numIndices_1741_);
return v_res_1752_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3(void){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1758_ = lean_box(0);
v___x_1759_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2));
v___x_1760_ = l_Lean_mkConst(v___x_1759_, v___x_1758_);
return v___x_1760_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6(void){
_start:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1764_ = lean_box(0);
v___x_1765_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__5));
v___x_1766_ = l_Lean_mkConst(v___x_1765_, v___x_1764_);
return v___x_1766_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10(void){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1773_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9));
v___x_1774_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4));
v___x_1775_ = l_Lean_Name_append(v___x_1774_, v___x_1773_);
return v___x_1775_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12(void){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11));
v___x_1778_ = l_Lean_stringToMessageData(v___x_1777_);
return v___x_1778_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14(void){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13));
v___x_1781_ = l_Lean_stringToMessageData(v___x_1780_);
return v___x_1781_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17(void){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__16));
v___x_1786_ = l_Lean_MessageData_ofFormat(v___x_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(lean_object* v_numIndices_1787_, uint8_t v_useDecide_1788_, lean_object* v_prop_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_){
_start:
{
lean_object* v___x_1798_; lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1933_; 
v___x_1798_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_prop_1789_, v_a_1794_);
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1801_ = v___x_1798_;
v_isShared_1802_ = v_isSharedCheck_1933_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1798_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1933_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v_toCold_1900_; lean_object* v_options_1901_; uint8_t v_hasTrace_1902_; 
v_toCold_1900_ = lean_ctor_get(v_a_1795_, 0);
v_options_1901_ = lean_ctor_get(v_toCold_1900_, 2);
v_hasTrace_1902_ = lean_ctor_get_uint8(v_options_1901_, sizeof(void*)*1);
if (v_hasTrace_1902_ == 0)
{
v___y_1860_ = v_a_1790_;
v___y_1861_ = v_a_1791_;
v___y_1862_ = v_a_1792_;
v___y_1863_ = v_a_1793_;
v___y_1864_ = v_a_1794_;
v___y_1865_ = v_a_1795_;
v___y_1866_ = v_a_1796_;
goto v___jp_1859_;
}
else
{
lean_object* v_inheritedTraceOptions_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; uint8_t v___x_1906_; 
v_inheritedTraceOptions_1903_ = lean_ctor_get(v_toCold_1900_, 11);
v___x_1904_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9));
v___x_1905_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10);
v___x_1906_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1903_, v_options_1901_, v___x_1905_);
if (v___x_1906_ == 0)
{
v___y_1860_ = v_a_1790_;
v___y_1861_ = v_a_1791_;
v___y_1862_ = v_a_1792_;
v___y_1863_ = v_a_1793_;
v___y_1864_ = v_a_1794_;
v___y_1865_ = v_a_1795_;
v___y_1866_ = v_a_1796_;
goto v___jp_1859_;
}
else
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___y_1913_; lean_object* v___x_1926_; lean_object* v___x_1927_; uint8_t v___x_1928_; 
v___x_1907_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12);
lean_inc(v_a_1799_);
v___x_1908_ = l_Lean_MessageData_ofExpr(v_a_1799_);
v___x_1909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1907_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
v___x_1910_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14);
v___x_1911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1909_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1926_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__1));
v___x_1927_ = lean_unsigned_to_nat(1u);
v___x_1928_ = l_Lean_Expr_isAppOfArity(v_a_1799_, v___x_1926_, v___x_1927_);
if (v___x_1928_ == 0)
{
goto v___jp_1924_;
}
else
{
lean_object* v___x_1929_; uint8_t v___x_1930_; 
v___x_1929_ = l_Lean_Expr_appArg_x21(v_a_1799_);
v___x_1930_ = l_Lean_Expr_isAppOfArity(v___x_1929_, v___x_1926_, v___x_1927_);
if (v___x_1930_ == 0)
{
lean_dec_ref(v___x_1929_);
goto v___jp_1924_;
}
else
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1931_ = l_Lean_Expr_appArg_x21(v___x_1929_);
lean_dec_ref(v___x_1929_);
v___x_1932_ = l_Lean_MessageData_ofExpr(v___x_1931_);
v___y_1913_ = v___x_1932_;
goto v___jp_1912_;
}
}
v___jp_1912_:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1911_);
lean_ctor_set(v___x_1914_, 1, v___y_1913_);
v___x_1915_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v___x_1904_, v___x_1914_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_dec_ref_known(v___x_1915_, 1);
v___y_1860_ = v_a_1790_;
v___y_1861_ = v_a_1791_;
v___y_1862_ = v_a_1792_;
v___y_1863_ = v_a_1793_;
v___y_1864_ = v_a_1794_;
v___y_1865_ = v_a_1795_;
v___y_1866_ = v_a_1796_;
goto v___jp_1859_;
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
lean_del_object(v___x_1801_);
lean_dec(v_a_1799_);
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1915_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1915_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
v___jp_1924_:
{
lean_object* v___x_1925_; 
v___x_1925_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17);
v___y_1913_ = v___x_1925_;
goto v___jp_1912_;
}
}
}
v___jp_1803_:
{
lean_object* v_lctx_1811_; lean_object* v___x_1812_; 
v_lctx_1811_ = lean_ctor_get(v___y_1807_, 2);
v___x_1812_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(v_numIndices_1787_, v_a_1799_, v_lctx_1811_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
return v___x_1812_;
}
v___jp_1813_:
{
if (lean_obj_tag(v___y_1823_) == 0)
{
lean_object* v_a_1824_; lean_object* v___x_1825_; uint8_t v___x_1826_; 
v_a_1824_ = lean_ctor_get(v___y_1823_, 0);
lean_inc(v_a_1824_);
lean_dec_ref_known(v___y_1823_, 1);
v___x_1825_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2));
v___x_1826_ = l_Lean_Expr_isConstOf(v_a_1824_, v___x_1825_);
lean_dec(v_a_1824_);
if (v___x_1826_ == 0)
{
lean_dec_ref(v___y_1817_);
lean_dec_ref(v___y_1814_);
lean_del_object(v___x_1801_);
v___y_1804_ = v___y_1815_;
v___y_1805_ = v___y_1820_;
v___y_1806_ = v___y_1819_;
v___y_1807_ = v___y_1816_;
v___y_1808_ = v___y_1818_;
v___y_1809_ = v___y_1822_;
v___y_1810_ = v___y_1821_;
goto v___jp_1803_;
}
else
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
lean_dec(v_a_1799_);
v___x_1827_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3);
v___x_1828_ = l_Lean_Meta_mkEqRefl(v___x_1827_, v___y_1816_, v___y_1818_, v___y_1822_, v___y_1821_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1842_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1831_ = v___x_1828_;
v_isShared_1832_ = v_isSharedCheck_1842_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1828_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1842_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1837_; 
v___x_1833_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6);
v___x_1834_ = l_Lean_Expr_appArg_x21(v___y_1817_);
lean_dec_ref(v___y_1817_);
v___x_1835_ = l_Lean_mkApp3(v___x_1833_, v___y_1814_, v___x_1834_, v_a_1829_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set_tag(v___x_1801_, 1);
lean_ctor_set(v___x_1801_, 0, v___x_1835_);
v___x_1837_ = v___x_1801_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1835_);
v___x_1837_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
lean_object* v___x_1839_; 
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1837_);
v___x_1839_ = v___x_1831_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
else
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
lean_dec_ref(v___y_1817_);
lean_dec_ref(v___y_1814_);
lean_del_object(v___x_1801_);
v_a_1843_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1828_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1828_);
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
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_dec_ref(v___y_1817_);
lean_dec_ref(v___y_1814_);
lean_del_object(v___x_1801_);
lean_dec(v_a_1799_);
v_a_1851_ = lean_ctor_get(v___y_1823_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___y_1823_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___y_1823_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___y_1823_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
v___jp_1859_:
{
if (v_useDecide_1788_ == 0)
{
lean_del_object(v___x_1801_);
v___y_1804_ = v___y_1860_;
v___y_1805_ = v___y_1861_;
v___y_1806_ = v___y_1862_;
v___y_1807_ = v___y_1863_;
v___y_1808_ = v___y_1864_;
v___y_1809_ = v___y_1865_;
v___y_1810_ = v___y_1866_;
goto v___jp_1803_;
}
else
{
lean_object* v___x_1867_; lean_object* v_a_1868_; uint8_t v___x_1869_; 
lean_inc(v_a_1799_);
v___x_1867_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_a_1799_, v___y_1864_);
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_a_1868_);
lean_dec_ref(v___x_1867_);
v___x_1869_ = l_Lean_Expr_hasFVar(v_a_1868_);
if (v___x_1869_ == 0)
{
uint8_t v___x_1870_; 
v___x_1870_ = l_Lean_Expr_hasMVar(v_a_1868_);
if (v___x_1870_ == 0)
{
lean_object* v___x_1871_; 
lean_inc(v_a_1868_);
v___x_1871_ = l_Lean_Meta_mkDecide(v_a_1868_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1873_; uint8_t v_transparency_1874_; uint8_t v___x_1875_; uint8_t v___x_1876_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc(v_a_1872_);
lean_dec_ref_known(v___x_1871_, 1);
v___x_1873_ = l_Lean_Meta_Context_config(v___y_1863_);
v_transparency_1874_ = lean_ctor_get_uint8(v___x_1873_, 9);
lean_dec_ref(v___x_1873_);
v___x_1875_ = 1;
v___x_1876_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1874_, v___x_1875_);
if (v___x_1876_ == 0)
{
lean_object* v_keyedConfig_1877_; uint8_t v_trackZetaDelta_1878_; lean_object* v_zetaDeltaSet_1879_; lean_object* v_lctx_1880_; lean_object* v_localInstances_1881_; lean_object* v_defEqCtx_x3f_1882_; lean_object* v_synthPendingDepth_1883_; lean_object* v_customCanUnfoldPredicate_x3f_1884_; uint8_t v_univApprox_1885_; uint8_t v_inTypeClassResolution_1886_; uint8_t v_cacheInferType_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v_keyedConfig_1877_ = lean_ctor_get(v___y_1863_, 0);
v_trackZetaDelta_1878_ = lean_ctor_get_uint8(v___y_1863_, sizeof(void*)*7);
v_zetaDeltaSet_1879_ = lean_ctor_get(v___y_1863_, 1);
v_lctx_1880_ = lean_ctor_get(v___y_1863_, 2);
v_localInstances_1881_ = lean_ctor_get(v___y_1863_, 3);
v_defEqCtx_x3f_1882_ = lean_ctor_get(v___y_1863_, 4);
v_synthPendingDepth_1883_ = lean_ctor_get(v___y_1863_, 5);
v_customCanUnfoldPredicate_x3f_1884_ = lean_ctor_get(v___y_1863_, 6);
v_univApprox_1885_ = lean_ctor_get_uint8(v___y_1863_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1886_ = lean_ctor_get_uint8(v___y_1863_, sizeof(void*)*7 + 2);
v_cacheInferType_1887_ = lean_ctor_get_uint8(v___y_1863_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1877_);
v___x_1888_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1875_, v_keyedConfig_1877_);
lean_inc(v_customCanUnfoldPredicate_x3f_1884_);
lean_inc(v_synthPendingDepth_1883_);
lean_inc(v_defEqCtx_x3f_1882_);
lean_inc_ref(v_localInstances_1881_);
lean_inc_ref(v_lctx_1880_);
lean_inc(v_zetaDeltaSet_1879_);
v___x_1889_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
lean_ctor_set(v___x_1889_, 1, v_zetaDeltaSet_1879_);
lean_ctor_set(v___x_1889_, 2, v_lctx_1880_);
lean_ctor_set(v___x_1889_, 3, v_localInstances_1881_);
lean_ctor_set(v___x_1889_, 4, v_defEqCtx_x3f_1882_);
lean_ctor_set(v___x_1889_, 5, v_synthPendingDepth_1883_);
lean_ctor_set(v___x_1889_, 6, v_customCanUnfoldPredicate_x3f_1884_);
lean_ctor_set_uint8(v___x_1889_, sizeof(void*)*7, v_trackZetaDelta_1878_);
lean_ctor_set_uint8(v___x_1889_, sizeof(void*)*7 + 1, v_univApprox_1885_);
lean_ctor_set_uint8(v___x_1889_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1886_);
lean_ctor_set_uint8(v___x_1889_, sizeof(void*)*7 + 3, v_cacheInferType_1887_);
lean_inc(v___y_1866_);
lean_inc_ref(v___y_1865_);
lean_inc(v___y_1864_);
lean_inc(v_a_1872_);
v___x_1890_ = lean_whnf(v_a_1872_, v___x_1889_, v___y_1864_, v___y_1865_, v___y_1866_);
v___y_1814_ = v_a_1868_;
v___y_1815_ = v___y_1860_;
v___y_1816_ = v___y_1863_;
v___y_1817_ = v_a_1872_;
v___y_1818_ = v___y_1864_;
v___y_1819_ = v___y_1862_;
v___y_1820_ = v___y_1861_;
v___y_1821_ = v___y_1866_;
v___y_1822_ = v___y_1865_;
v___y_1823_ = v___x_1890_;
goto v___jp_1813_;
}
else
{
lean_object* v___x_1891_; 
lean_inc(v___y_1866_);
lean_inc_ref(v___y_1865_);
lean_inc(v___y_1864_);
lean_inc_ref(v___y_1863_);
lean_inc(v_a_1872_);
v___x_1891_ = lean_whnf(v_a_1872_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
v___y_1814_ = v_a_1868_;
v___y_1815_ = v___y_1860_;
v___y_1816_ = v___y_1863_;
v___y_1817_ = v_a_1872_;
v___y_1818_ = v___y_1864_;
v___y_1819_ = v___y_1862_;
v___y_1820_ = v___y_1861_;
v___y_1821_ = v___y_1866_;
v___y_1822_ = v___y_1865_;
v___y_1823_ = v___x_1891_;
goto v___jp_1813_;
}
}
else
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1899_; 
lean_dec(v_a_1868_);
lean_del_object(v___x_1801_);
lean_dec(v_a_1799_);
v_a_1892_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1894_ = v___x_1871_;
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1871_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
if (v_isShared_1895_ == 0)
{
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1892_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
else
{
lean_dec(v_a_1868_);
lean_del_object(v___x_1801_);
v___y_1804_ = v___y_1860_;
v___y_1805_ = v___y_1861_;
v___y_1806_ = v___y_1862_;
v___y_1807_ = v___y_1863_;
v___y_1808_ = v___y_1864_;
v___y_1809_ = v___y_1865_;
v___y_1810_ = v___y_1866_;
goto v___jp_1803_;
}
}
else
{
lean_dec(v_a_1868_);
lean_del_object(v___x_1801_);
v___y_1804_ = v___y_1860_;
v___y_1805_ = v___y_1861_;
v___y_1806_ = v___y_1862_;
v___y_1807_ = v___y_1863_;
v___y_1808_ = v___y_1864_;
v___y_1809_ = v___y_1865_;
v___y_1810_ = v___y_1866_;
goto v___jp_1803_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___boxed(lean_object* v_numIndices_1934_, lean_object* v_useDecide_1935_, lean_object* v_prop_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_){
_start:
{
uint8_t v_useDecide_boxed_1945_; lean_object* v_res_1946_; 
v_useDecide_boxed_1945_ = lean_unbox(v_useDecide_1935_);
v_res_1946_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_1934_, v_useDecide_boxed_1945_, v_prop_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec(v_a_1941_);
lean_dec_ref(v_a_1940_);
lean_dec(v_a_1939_);
lean_dec_ref(v_a_1938_);
lean_dec(v_a_1937_);
lean_dec(v_numIndices_1934_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2(lean_object* v_cls_1947_, lean_object* v_msg_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v___x_1957_; 
v___x_1957_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v_cls_1947_, v_msg_1948_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___boxed(lean_object* v_cls_1958_, lean_object* v_msg_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2(v_cls_1958_, v_msg_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2(lean_object* v_numIndices_1969_, lean_object* v_a_1970_, lean_object* v_as_1971_, lean_object* v_i_1972_, lean_object* v_a_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v___x_1982_; 
v___x_1982_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_numIndices_1969_, v_a_1970_, v_as_1971_, v_i_1972_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_numIndices_1983_, lean_object* v_a_1984_, lean_object* v_as_1985_, lean_object* v_i_1986_, lean_object* v_a_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2(v_numIndices_1983_, v_a_1984_, v_as_1985_, v_i_1986_, v_a_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v_as_1985_);
lean_dec(v_numIndices_1983_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5(lean_object* v_numIndices_1997_, lean_object* v_a_1998_, lean_object* v_as_1999_, lean_object* v_i_2000_, lean_object* v_a_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v___x_2010_; 
v___x_2010_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_numIndices_1997_, v_a_1998_, v_as_1999_, v_i_2000_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_numIndices_2011_, lean_object* v_a_2012_, lean_object* v_as_2013_, lean_object* v_i_2014_, lean_object* v_a_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5(v_numIndices_2011_, v_a_2012_, v_as_2013_, v_i_2014_, v_a_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v_as_2013_);
lean_dec(v_numIndices_2011_);
return v_res_2024_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3(void){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2030_ = lean_box(0);
v___x_2031_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__2));
v___x_2032_ = l_Lean_mkConst(v___x_2031_, v___x_2030_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27(lean_object* v_numIndices_2036_, uint8_t v_useDecideBool_2037_, lean_object* v_e_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_){
_start:
{
lean_object* v___x_2050_; 
lean_inc_ref(v_e_2038_);
v___x_2050_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2038_, v_a_2043_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref_known(v___x_2050_, 1);
v___x_2052_ = l_Lean_Expr_cleanupAnnotations(v_a_2051_);
v___x_2053_ = l_Lean_Expr_isApp(v___x_2052_);
if (v___x_2053_ == 0)
{
lean_dec_ref(v___x_2052_);
lean_dec_ref(v_e_2038_);
goto v___jp_2047_;
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
lean_dec_ref(v_e_2038_);
goto v___jp_2047_;
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
lean_dec_ref(v_e_2038_);
goto v___jp_2047_;
}
else
{
lean_object* v_arg_2060_; lean_object* v___x_2061_; uint8_t v___x_2062_; 
v_arg_2060_ = lean_ctor_get(v___x_2058_, 1);
lean_inc_ref(v_arg_2060_);
v___x_2061_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2058_);
v___x_2062_ = l_Lean_Expr_isApp(v___x_2061_);
if (v___x_2062_ == 0)
{
lean_dec_ref(v___x_2061_);
lean_dec_ref(v_arg_2060_);
lean_dec_ref(v_arg_2057_);
lean_dec_ref(v_arg_2054_);
lean_dec_ref(v_e_2038_);
goto v___jp_2047_;
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
lean_dec_ref(v_arg_2060_);
lean_dec_ref(v_arg_2057_);
lean_dec_ref(v_arg_2054_);
lean_dec_ref(v_e_2038_);
goto v___jp_2047_;
}
else
{
lean_object* v_arg_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; 
v_arg_2066_ = lean_ctor_get(v___x_2064_, 1);
lean_inc_ref(v_arg_2066_);
v___x_2067_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2064_);
v___x_2068_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__2));
v___x_2069_ = l_Lean_Expr_isConstOf(v___x_2067_, v___x_2068_);
if (v___x_2069_ == 0)
{
lean_dec_ref(v___x_2067_);
lean_dec_ref(v_arg_2066_);
lean_dec_ref(v_arg_2063_);
lean_dec_ref(v_arg_2060_);
lean_dec_ref(v_arg_2057_);
lean_dec_ref(v_arg_2054_);
lean_dec_ref(v_e_2038_);
goto v___jp_2047_;
}
else
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2070_ = l_Lean_Expr_constLevels_x21(v___x_2067_);
lean_inc_ref(v_arg_2063_);
v___x_2071_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2036_, v_useDecideBool_2037_, v_arg_2063_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2214_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2074_ = v___x_2071_;
v_isShared_2075_ = v_isSharedCheck_2214_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2071_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2214_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
if (lean_obj_tag(v_a_2072_) == 1)
{
lean_object* v_val_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2091_; 
lean_dec_ref(v___x_2067_);
lean_dec_ref(v_e_2038_);
v_val_2076_ = lean_ctor_get(v_a_2072_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v_a_2072_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2078_ = v_a_2072_;
v_isShared_2079_ = v_isSharedCheck_2091_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_val_2076_);
lean_dec(v_a_2072_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2091_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2084_; 
v___x_2080_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__4));
v___x_2081_ = l_Lean_mkConst(v___x_2080_, v___x_2070_);
lean_inc_ref(v_arg_2057_);
v___x_2082_ = l_Lean_mkApp6(v___x_2081_, v_arg_2063_, v_arg_2060_, v_val_2076_, v_arg_2066_, v_arg_2057_, v_arg_2054_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 0, v___x_2082_);
v___x_2084_ = v___x_2078_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2082_);
v___x_2084_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2088_; 
v___x_2085_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2085_, 0, v_arg_2057_);
lean_ctor_set(v___x_2085_, 1, v___x_2084_);
lean_ctor_set_uint8(v___x_2085_, sizeof(void*)*2, v___x_2069_);
v___x_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 0, v___x_2086_);
v___x_2088_ = v___x_2074_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
else
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
lean_del_object(v___x_2074_);
lean_dec(v_a_2072_);
lean_inc_ref(v_arg_2063_);
v___x_2092_ = l_Lean_mkNot(v_arg_2063_);
v___x_2093_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2036_, v_useDecideBool_2037_, v___x_2092_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2205_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2096_ = v___x_2093_;
v_isShared_2097_ = v_isSharedCheck_2205_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2093_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2205_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
if (lean_obj_tag(v_a_2094_) == 1)
{
lean_object* v_val_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2113_; 
lean_dec_ref(v___x_2067_);
lean_dec_ref(v_e_2038_);
v_val_2098_ = lean_ctor_get(v_a_2094_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v_a_2094_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2100_ = v_a_2094_;
v_isShared_2101_ = v_isSharedCheck_2113_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_val_2098_);
lean_dec(v_a_2094_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2113_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2106_; 
v___x_2102_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__6));
v___x_2103_ = l_Lean_mkConst(v___x_2102_, v___x_2070_);
lean_inc_ref(v_arg_2054_);
v___x_2104_ = l_Lean_mkApp6(v___x_2103_, v_arg_2063_, v_arg_2060_, v_val_2098_, v_arg_2066_, v_arg_2057_, v_arg_2054_);
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 0, v___x_2104_);
v___x_2106_ = v___x_2100_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2110_; 
v___x_2107_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2107_, 0, v_arg_2054_);
lean_ctor_set(v___x_2107_, 1, v___x_2106_);
lean_ctor_set_uint8(v___x_2107_, sizeof(void*)*2, v___x_2069_);
v___x_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 0, v___x_2108_);
v___x_2110_ = v___x_2096_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2108_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
else
{
lean_object* v___x_2114_; 
lean_del_object(v___x_2096_);
lean_dec(v_a_2094_);
lean_inc(v_a_2045_);
lean_inc_ref(v_a_2044_);
lean_inc(v_a_2043_);
lean_inc_ref(v_a_2042_);
lean_inc(v_a_2041_);
lean_inc_ref(v_a_2040_);
lean_inc(v_a_2039_);
lean_inc_ref(v_arg_2063_);
v___x_2114_ = lean_simp(v_arg_2063_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2196_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2117_ = v___x_2114_;
v_isShared_2118_ = v_isSharedCheck_2196_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2114_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2196_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v_expr_2119_; uint8_t v___x_2120_; 
v_expr_2119_ = lean_ctor_get(v_a_2115_, 0);
v___x_2120_ = lean_expr_eqv(v_expr_2119_, v_arg_2063_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
lean_del_object(v___x_2117_);
v___x_2121_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3);
lean_inc_ref(v_expr_2119_);
v___x_2122_ = l_Lean_Expr_app___override(v___x_2121_, v_expr_2119_);
v___x_2123_ = lean_box(0);
v___x_2124_ = l_Lean_Meta_trySynthInstance(v___x_2122_, v___x_2123_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2173_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2127_ = v___x_2124_;
v_isShared_2128_ = v_isSharedCheck_2173_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2124_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2173_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
if (lean_obj_tag(v_a_2125_) == 1)
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2159_; 
lean_inc_ref(v_expr_2119_);
lean_del_object(v___x_2127_);
lean_dec_ref(v_e_2038_);
v_a_2129_ = lean_ctor_get(v_a_2125_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v_a_2125_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2131_ = v_a_2125_;
v_isShared_2132_ = v_isSharedCheck_2159_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v_a_2125_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2159_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2133_; 
v___x_2133_ = l_Lean_Meta_Simp_Result_getProof(v_a_2115_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2150_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2136_ = v___x_2133_;
v_isShared_2137_ = v_isSharedCheck_2150_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2150_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2143_; 
v___x_2138_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__5));
v___x_2139_ = l_Lean_mkConst(v___x_2138_, v___x_2070_);
lean_inc_ref(v_arg_2054_);
lean_inc_ref(v_arg_2057_);
lean_inc(v_a_2129_);
lean_inc_ref(v_expr_2119_);
lean_inc_ref(v_arg_2066_);
v___x_2140_ = l_Lean_mkApp8(v___x_2139_, v_arg_2066_, v_arg_2063_, v_expr_2119_, v_arg_2060_, v_a_2129_, v_arg_2057_, v_arg_2054_, v_a_2134_);
v___x_2141_ = l_Lean_mkApp5(v___x_2067_, v_arg_2066_, v_expr_2119_, v_a_2129_, v_arg_2057_, v_arg_2054_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 0, v___x_2140_);
v___x_2143_ = v___x_2131_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2140_);
v___x_2143_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2147_; 
v___x_2144_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2144_, 0, v___x_2141_);
lean_ctor_set(v___x_2144_, 1, v___x_2143_);
lean_ctor_set_uint8(v___x_2144_, sizeof(void*)*2, v___x_2069_);
v___x_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2144_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 0, v___x_2145_);
v___x_2147_ = v___x_2136_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2145_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_del_object(v___x_2131_);
lean_dec(v_a_2129_);
lean_dec_ref(v_expr_2119_);
lean_dec(v___x_2070_);
lean_dec_ref(v___x_2067_);
lean_dec_ref(v_arg_2066_);
lean_dec_ref(v_arg_2063_);
lean_dec_ref(v_arg_2060_);
lean_dec_ref(v_arg_2057_);
lean_dec_ref(v_arg_2054_);
v_a_2151_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2133_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2133_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
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
}
else
{
lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2170_; 
lean_dec(v_a_2125_);
lean_dec(v___x_2070_);
lean_dec_ref(v___x_2067_);
lean_dec_ref(v_arg_2066_);
lean_dec_ref(v_arg_2063_);
lean_dec_ref(v_arg_2060_);
lean_dec_ref(v_arg_2057_);
lean_dec_ref(v_arg_2054_);
v_isSharedCheck_2170_ = !lean_is_exclusive(v_a_2115_);
if (v_isSharedCheck_2170_ == 0)
{
lean_object* v_unused_2171_; lean_object* v_unused_2172_; 
v_unused_2171_ = lean_ctor_get(v_a_2115_, 1);
lean_dec(v_unused_2171_);
v_unused_2172_ = lean_ctor_get(v_a_2115_, 0);
lean_dec(v_unused_2172_);
v___x_2161_ = v_a_2115_;
v_isShared_2162_ = v_isSharedCheck_2170_;
goto v_resetjp_2160_;
}
else
{
lean_dec(v_a_2115_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2170_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 1, v___x_2123_);
lean_ctor_set(v___x_2161_, 0, v_e_2038_);
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_e_2038_);
lean_ctor_set(v_reuseFailAlloc_2169_, 1, v___x_2123_);
v___x_2164_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
lean_object* v___x_2165_; lean_object* v___x_2167_; 
lean_ctor_set_uint8(v___x_2164_, sizeof(void*)*2, v___x_2069_);
v___x_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 0, v___x_2165_);
v___x_2167_ = v___x_2127_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2165_);
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
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_dec(v_a_2115_);
lean_dec(v___x_2070_);
lean_dec_ref(v___x_2067_);
lean_dec_ref(v_arg_2066_);
lean_dec_ref(v_arg_2063_);
lean_dec_ref(v_arg_2060_);
lean_dec_ref(v_arg_2057_);
lean_dec_ref(v_arg_2054_);
lean_dec_ref(v_e_2038_);
v_a_2174_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2124_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2124_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
else
{
lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2193_; 
lean_dec(v___x_2070_);
lean_dec_ref(v___x_2067_);
lean_dec_ref(v_arg_2066_);
lean_dec_ref(v_arg_2063_);
lean_dec_ref(v_arg_2060_);
lean_dec_ref(v_arg_2057_);
lean_dec_ref(v_arg_2054_);
v_isSharedCheck_2193_ = !lean_is_exclusive(v_a_2115_);
if (v_isSharedCheck_2193_ == 0)
{
lean_object* v_unused_2194_; lean_object* v_unused_2195_; 
v_unused_2194_ = lean_ctor_get(v_a_2115_, 1);
lean_dec(v_unused_2194_);
v_unused_2195_ = lean_ctor_get(v_a_2115_, 0);
lean_dec(v_unused_2195_);
v___x_2183_ = v_a_2115_;
v_isShared_2184_ = v_isSharedCheck_2193_;
goto v_resetjp_2182_;
}
else
{
lean_dec(v_a_2115_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2193_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2185_; lean_object* v___x_2187_; 
v___x_2185_ = lean_box(0);
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 1, v___x_2185_);
lean_ctor_set(v___x_2183_, 0, v_e_2038_);
v___x_2187_ = v___x_2183_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_e_2038_);
lean_ctor_set(v_reuseFailAlloc_2192_, 1, v___x_2185_);
v___x_2187_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
lean_object* v___x_2188_; lean_object* v___x_2190_; 
lean_ctor_set_uint8(v___x_2187_, sizeof(void*)*2, v___x_2069_);
v___x_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2187_);
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 0, v___x_2188_);
v___x_2190_ = v___x_2117_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2188_);
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
}
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
lean_dec(v___x_2070_);
lean_dec_ref(v___x_2067_);
lean_dec_ref(v_arg_2066_);
lean_dec_ref(v_arg_2063_);
lean_dec_ref(v_arg_2060_);
lean_dec_ref(v_arg_2057_);
lean_dec_ref(v_arg_2054_);
lean_dec_ref(v_e_2038_);
v_a_2197_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2114_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2114_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2197_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
}
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_dec(v___x_2070_);
lean_dec_ref(v___x_2067_);
lean_dec_ref(v_arg_2066_);
lean_dec_ref(v_arg_2063_);
lean_dec_ref(v_arg_2060_);
lean_dec_ref(v_arg_2057_);
lean_dec_ref(v_arg_2054_);
lean_dec_ref(v_e_2038_);
v_a_2206_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2093_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2093_);
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
lean_dec(v___x_2070_);
lean_dec_ref(v___x_2067_);
lean_dec_ref(v_arg_2066_);
lean_dec_ref(v_arg_2063_);
lean_dec_ref(v_arg_2060_);
lean_dec_ref(v_arg_2057_);
lean_dec_ref(v_arg_2054_);
lean_dec_ref(v_e_2038_);
v_a_2215_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2071_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2071_);
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
}
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec_ref(v_e_2038_);
v_a_2223_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2050_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2050_);
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
v___jp_2047_:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__0));
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
return v___x_2049_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___boxed(lean_object* v_numIndices_2231_, lean_object* v_useDecideBool_2232_, lean_object* v_e_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_){
_start:
{
uint8_t v_useDecideBool_boxed_2242_; lean_object* v_res_2243_; 
v_useDecideBool_boxed_2242_ = lean_unbox(v_useDecideBool_2232_);
v_res_2243_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27(v_numIndices_2231_, v_useDecideBool_boxed_2242_, v_e_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
lean_dec(v_a_2240_);
lean_dec_ref(v_a_2239_);
lean_dec(v_a_2238_);
lean_dec_ref(v_a_2237_);
lean_dec(v_a_2236_);
lean_dec_ref(v_a_2235_);
lean_dec(v_a_2234_);
lean_dec(v_numIndices_2231_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(lean_object* v_e_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_){
_start:
{
if (lean_obj_tag(v_e_2247_) == 6)
{
lean_object* v_binderName_2251_; lean_object* v___x_2252_; 
v_binderName_2251_ = lean_ctor_get(v_e_2247_, 0);
lean_inc(v_binderName_2251_);
v___x_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2252_, 0, v_binderName_2251_);
return v___x_2252_;
}
else
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__1));
v___x_2254_ = l_Lean_Core_mkFreshUserName(v___x_2253_, v_a_2248_, v_a_2249_);
return v___x_2254_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___boxed(lean_object* v_e_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_e_2255_, v_a_2256_, v_a_2257_);
lean_dec(v_a_2257_);
lean_dec_ref(v_a_2256_);
lean_dec_ref(v_e_2255_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName(lean_object* v_e_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_e_2260_, v_a_2263_, v_a_2264_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___boxed(lean_object* v_e_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName(v_e_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_);
lean_dec(v_a_2271_);
lean_dec_ref(v_a_2270_);
lean_dec(v_a_2269_);
lean_dec_ref(v_a_2268_);
lean_dec_ref(v_e_2267_);
return v_res_2273_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2279_ = lean_box(0);
v___x_2280_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__2));
v___x_2281_ = l_Lean_mkConst(v___x_2280_, v___x_2279_);
return v___x_2281_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4(void){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = lean_unsigned_to_nat(0u);
v___x_2283_ = l_Lean_mkBVar(v___x_2282_);
return v___x_2283_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7(void){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2288_ = lean_box(0);
v___x_2289_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__6));
v___x_2290_ = l_Lean_mkConst(v___x_2289_, v___x_2288_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27(lean_object* v_numIndices_2294_, uint8_t v_useDecideBool_2295_, lean_object* v_e_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_){
_start:
{
lean_object* v___x_2308_; 
lean_inc_ref(v_e_2296_);
v___x_2308_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2296_, v_a_2301_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; lean_object* v___x_2310_; uint8_t v___x_2311_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2309_);
lean_dec_ref_known(v___x_2308_, 1);
v___x_2310_ = l_Lean_Expr_cleanupAnnotations(v_a_2309_);
v___x_2311_ = l_Lean_Expr_isApp(v___x_2310_);
if (v___x_2311_ == 0)
{
lean_dec_ref(v___x_2310_);
lean_dec_ref(v_e_2296_);
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
lean_dec_ref(v_e_2296_);
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
lean_dec_ref(v_e_2296_);
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
lean_dec_ref(v_e_2296_);
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
lean_dec_ref(v_e_2296_);
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
lean_dec_ref(v_e_2296_);
goto v___jp_2305_;
}
else
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2328_ = l_Lean_Expr_constLevels_x21(v___x_2325_);
lean_inc_ref(v_arg_2321_);
v___x_2329_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2294_, v_useDecideBool_2295_, v_arg_2321_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2501_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2332_ = v___x_2329_;
v_isShared_2333_ = v_isSharedCheck_2501_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2329_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2501_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
if (lean_obj_tag(v_a_2330_) == 1)
{
lean_object* v_val_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2351_; 
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_e_2296_);
v_val_2334_ = lean_ctor_get(v_a_2330_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v_a_2330_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2336_ = v_a_2330_;
v_isShared_2337_ = v_isSharedCheck_2351_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_val_2334_);
lean_dec(v_a_2330_);
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
v___x_2340_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__8));
v___x_2341_ = l_Lean_mkConst(v___x_2340_, v___x_2328_);
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
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v___x_2346_);
v___x_2348_ = v___x_2332_;
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
lean_del_object(v___x_2332_);
lean_dec(v_a_2330_);
lean_inc_ref(v_arg_2321_);
v___x_2352_ = l_Lean_mkNot(v_arg_2321_);
v___x_2353_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2294_, v_useDecideBool_2295_, v___x_2352_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_);
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
lean_dec_ref(v_e_2296_);
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
v___x_2364_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__10));
v___x_2365_ = l_Lean_mkConst(v___x_2364_, v___x_2328_);
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
lean_inc(v_a_2303_);
lean_inc_ref(v_a_2302_);
lean_inc(v_a_2301_);
lean_inc_ref(v_a_2300_);
lean_inc(v_a_2299_);
lean_inc_ref(v_a_2298_);
lean_inc(v_a_2297_);
lean_inc_ref(v_arg_2321_);
v___x_2376_ = lean_simp(v_arg_2321_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_);
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
v___x_2383_ = l_Lean_Meta_Simp_Result_getProof(v_a_2377_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_);
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
v___x_2388_ = l_Lean_Meta_trySynthInstance(v___x_2386_, v___x_2387_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_);
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
lean_dec_ref(v_e_2296_);
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
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2397_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3);
v___x_2398_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4);
lean_inc(v_a_2384_);
lean_inc_ref(v_expr_2381_);
lean_inc_ref(v_arg_2321_);
v___x_2399_ = l_Lean_mkApp4(v___x_2397_, v_arg_2321_, v_expr_2381_, v_a_2384_, v___x_2398_);
lean_inc_ref(v_arg_2315_);
v___x_2400_ = l_Lean_Expr_app___override(v_arg_2315_, v___x_2399_);
v___x_2401_ = l_Lean_Expr_headBeta(v___x_2400_);
v___x_2402_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_arg_2315_, v_a_2302_, v_a_2303_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; uint8_t v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_a_2403_);
lean_dec_ref_known(v___x_2402_, 1);
v___x_2404_ = 0;
lean_inc_ref_n(v_expr_2381_, 2);
v___x_2405_ = l_Lean_mkLambda(v_a_2403_, v___x_2404_, v_expr_2381_, v___x_2401_);
v___x_2406_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7);
lean_inc(v_a_2384_);
lean_inc_ref(v_arg_2321_);
v___x_2407_ = l_Lean_mkApp4(v___x_2406_, v_arg_2321_, v_expr_2381_, v_a_2384_, v___x_2398_);
lean_inc_ref(v_arg_2312_);
v___x_2408_ = l_Lean_Expr_app___override(v_arg_2312_, v___x_2407_);
v___x_2409_ = l_Lean_Expr_headBeta(v___x_2408_);
v___x_2410_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_arg_2312_, v_a_2302_, v_a_2303_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2429_; 
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2413_ = v___x_2410_;
v_isShared_2414_ = v_isSharedCheck_2429_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2410_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2429_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2422_; 
lean_inc_ref_n(v_expr_2381_, 2);
v___x_2415_ = l_Lean_mkNot(v_expr_2381_);
v___x_2416_ = l_Lean_mkLambda(v_a_2411_, v___x_2404_, v___x_2415_, v___x_2409_);
lean_inc(v_a_2393_);
lean_inc_ref(v_arg_2324_);
v___x_2417_ = l_Lean_mkApp5(v___x_2325_, v_arg_2324_, v_expr_2381_, v_a_2393_, v___x_2405_, v___x_2416_);
v___x_2418_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__9));
v___x_2419_ = l_Lean_mkConst(v___x_2418_, v___x_2328_);
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
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 0, v___x_2424_);
v___x_2426_ = v___x_2413_;
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
lean_dec_ref(v___x_2409_);
lean_dec_ref(v___x_2405_);
lean_del_object(v___x_2395_);
lean_dec(v_a_2393_);
lean_dec(v_a_2384_);
lean_dec_ref(v_expr_2381_);
lean_dec(v___x_2328_);
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_arg_2324_);
lean_dec_ref(v_arg_2321_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v_arg_2312_);
v_a_2430_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2410_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2410_);
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
lean_dec_ref(v___x_2401_);
lean_del_object(v___x_2395_);
lean_dec(v_a_2393_);
lean_dec(v_a_2384_);
lean_dec_ref(v_expr_2381_);
lean_dec(v___x_2328_);
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_arg_2324_);
lean_dec_ref(v_arg_2321_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v_arg_2312_);
v_a_2438_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2440_ = v___x_2402_;
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2402_);
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
lean_dec(v___x_2328_);
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_arg_2324_);
lean_dec_ref(v_arg_2321_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v_arg_2312_);
v___x_2447_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2447_, 0, v_e_2296_);
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
lean_dec(v___x_2328_);
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_arg_2324_);
lean_dec_ref(v_arg_2321_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v_arg_2312_);
lean_dec_ref(v_e_2296_);
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
lean_dec(v___x_2328_);
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_arg_2324_);
lean_dec_ref(v_arg_2321_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v_arg_2312_);
lean_dec_ref(v_e_2296_);
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
lean_dec(v___x_2328_);
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
lean_ctor_set(v___x_2470_, 0, v_e_2296_);
v___x_2474_ = v___x_2470_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_e_2296_);
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
lean_dec(v___x_2328_);
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_arg_2324_);
lean_dec_ref(v_arg_2321_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v_arg_2312_);
lean_dec_ref(v_e_2296_);
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
lean_dec(v___x_2328_);
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_arg_2324_);
lean_dec_ref(v_arg_2321_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v_arg_2312_);
lean_dec_ref(v_e_2296_);
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
lean_dec(v___x_2328_);
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_arg_2324_);
lean_dec_ref(v_arg_2321_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v_arg_2312_);
lean_dec_ref(v_e_2296_);
v_a_2502_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2504_ = v___x_2329_;
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___x_2329_);
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
}
else
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2517_; 
lean_dec_ref(v_e_2296_);
v_a_2510_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2512_ = v___x_2308_;
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2308_);
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
v___jp_2305_:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__0));
v___x_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
return v___x_2307_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___boxed(lean_object* v_numIndices_2518_, lean_object* v_useDecideBool_2519_, lean_object* v_e_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_){
_start:
{
uint8_t v_useDecideBool_boxed_2529_; lean_object* v_res_2530_; 
v_useDecideBool_boxed_2529_ = lean_unbox(v_useDecideBool_2519_);
v_res_2530_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27(v_numIndices_2518_, v_useDecideBool_boxed_2529_, v_e_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_);
lean_dec(v_a_2527_);
lean_dec_ref(v_a_2526_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
lean_dec(v_a_2523_);
lean_dec_ref(v_a_2522_);
lean_dec(v_a_2521_);
lean_dec(v_numIndices_2518_);
return v_res_2530_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0(void){
_start:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v_s_2533_; 
v___x_2531_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0);
v___x_2532_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__0, &l_Lean_Meta_SplitIf_getSimpContext___closed__0_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__0);
v_s_2533_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_s_2533_, 0, v___x_2532_);
lean_ctor_set(v_s_2533_, 1, v___x_2532_);
lean_ctor_set(v_s_2533_, 2, v___x_2531_);
lean_ctor_set(v_s_2533_, 3, v___x_2531_);
return v_s_2533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(lean_object* v_numIndices_2597_, uint8_t v_useDecide_2598_){
_start:
{
lean_object* v_s_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; uint8_t v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v_s_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v_s_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v_s_2600_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0);
v___x_2601_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__2));
v___x_2602_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__15));
v___x_2603_ = 0;
v___x_2604_ = lean_box(v_useDecide_2598_);
lean_inc(v_numIndices_2597_);
v___x_2605_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___boxed), 11, 2);
lean_closure_set(v___x_2605_, 0, v_numIndices_2597_);
lean_closure_set(v___x_2605_, 1, v___x_2604_);
v___x_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2605_);
v_s_2607_ = l_Lean_Meta_Simp_Simprocs_addCore(v_s_2600_, v___x_2601_, v___x_2602_, v___x_2603_, v___x_2606_);
v___x_2608_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__17));
v___x_2609_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__19));
v___x_2610_ = lean_box(v_useDecide_2598_);
v___x_2611_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___boxed), 11, 2);
lean_closure_set(v___x_2611_, 0, v_numIndices_2597_);
lean_closure_set(v___x_2611_, 1, v___x_2610_);
v___x_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
v_s_2613_ = l_Lean_Meta_Simp_Simprocs_addCore(v_s_2607_, v___x_2608_, v___x_2609_, v___x_2603_, v___x_2612_);
v___x_2614_ = lean_unsigned_to_nat(1u);
v___x_2615_ = lean_mk_empty_array_with_capacity(v___x_2614_);
v___x_2616_ = lean_array_push(v___x_2615_, v_s_2613_);
v___x_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2616_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___boxed(lean_object* v_numIndices_2618_, lean_object* v_useDecide_2619_, lean_object* v_a_2620_){
_start:
{
uint8_t v_useDecide_boxed_2621_; lean_object* v_res_2622_; 
v_useDecide_boxed_2621_ = lean_unbox(v_useDecide_2619_);
v_res_2622_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_numIndices_2618_, v_useDecide_boxed_2621_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs(lean_object* v_numIndices_2623_, uint8_t v_useDecide_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_){
_start:
{
lean_object* v___x_2630_; 
v___x_2630_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_numIndices_2623_, v_useDecide_2624_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___boxed(lean_object* v_numIndices_2631_, lean_object* v_useDecide_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_){
_start:
{
uint8_t v_useDecide_boxed_2638_; lean_object* v_res_2639_; 
v_useDecide_boxed_2638_ = lean_unbox(v_useDecide_2632_);
v_res_2639_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs(v_numIndices_2631_, v_useDecide_boxed_2638_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_);
lean_dec(v_a_2636_);
lean_dec_ref(v_a_2635_);
lean_dec(v_a_2634_);
lean_dec_ref(v_a_2633_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(uint8_t v_useDecide_2640_, lean_object* v_a_2641_){
_start:
{
lean_object* v_lctx_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v_lctx_2643_ = lean_ctor_get(v_a_2641_, 2);
lean_inc_ref(v_lctx_2643_);
v___x_2644_ = lean_local_ctx_num_indices(v_lctx_2643_);
v___x_2645_ = lean_box(v_useDecide_2640_);
v___x_2646_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___boxed), 11, 2);
lean_closure_set(v___x_2646_, 0, v___x_2644_);
lean_closure_set(v___x_2646_, 1, v___x_2645_);
v___x_2647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2646_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg___boxed(lean_object* v_useDecide_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_){
_start:
{
uint8_t v_useDecide_boxed_2651_; lean_object* v_res_2652_; 
v_useDecide_boxed_2651_ = lean_unbox(v_useDecide_2648_);
v_res_2652_ = l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(v_useDecide_boxed_2651_, v_a_2649_);
lean_dec_ref(v_a_2649_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f(uint8_t v_useDecide_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_){
_start:
{
lean_object* v___x_2659_; 
v___x_2659_ = l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(v_useDecide_2653_, v_a_2654_);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed(lean_object* v_useDecide_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_){
_start:
{
uint8_t v_useDecide_boxed_2666_; lean_object* v_res_2667_; 
v_useDecide_boxed_2666_ = lean_unbox(v_useDecide_2660_);
v_res_2667_ = l_Lean_Meta_SplitIf_mkDischarge_x3f(v_useDecide_boxed_2666_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_);
lean_dec(v_a_2664_);
lean_dec_ref(v_a_2663_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(lean_object* v_mvarId_2668_, lean_object* v_x_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v___x_2675_; 
v___x_2675_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2668_, v_x_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2675_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2675_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
v_a_2684_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2675_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2675_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_2692_, lean_object* v_x_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2692_, v_x_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0(lean_object* v_00_u03b1_2700_, lean_object* v_mvarId_2701_, lean_object* v_x_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v___x_2708_; 
v___x_2708_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2701_, v_x_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___boxed(lean_object* v_00_u03b1_2709_, lean_object* v_mvarId_2710_, lean_object* v_x_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0(v_00_u03b1_2709_, v_mvarId_2710_, v_x_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
return v_res_2717_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2719_ = ((lean_object*)(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__0));
v___x_2720_ = l_Lean_stringToMessageData(v___x_2719_);
return v___x_2720_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2722_ = ((lean_object*)(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__2));
v___x_2723_ = l_Lean_stringToMessageData(v___x_2722_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0(lean_object* v_e_2724_, lean_object* v_mvarId_2725_, lean_object* v_hName_x3f_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v___x_2735_; lean_object* v_a_2736_; lean_object* v___x_2737_; 
v___x_2735_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_2724_, v___y_2728_);
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc_n(v_a_2736_, 2);
lean_dec_ref(v___x_2735_);
v___x_2737_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(v_a_2736_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v_a_2738_; 
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
lean_inc(v_a_2738_);
lean_dec_ref_known(v___x_2737_, 1);
if (lean_obj_tag(v_a_2738_) == 1)
{
lean_object* v_val_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2814_; 
lean_dec(v_a_2736_);
v_val_2739_ = lean_ctor_get(v_a_2738_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v_a_2738_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2741_ = v_a_2738_;
v_isShared_2742_ = v_isSharedCheck_2814_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_val_2739_);
lean_dec(v_a_2738_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2814_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v_fst_2743_; lean_object* v_snd_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2813_; 
v_fst_2743_ = lean_ctor_get(v_val_2739_, 0);
v_snd_2744_ = lean_ctor_get(v_val_2739_, 1);
v_isSharedCheck_2813_ = !lean_is_exclusive(v_val_2739_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2746_ = v_val_2739_;
v_isShared_2747_ = v_isSharedCheck_2813_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_snd_2744_);
lean_inc(v_fst_2743_);
lean_dec(v_val_2739_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2813_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v_hName_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; 
if (lean_obj_tag(v_hName_x3f_2726_) == 0)
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2801_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__1));
v___x_2802_ = l_Lean_Core_mkFreshUserName(v___x_2801_, v___y_2729_, v___y_2730_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2803_);
lean_dec_ref_known(v___x_2802_, 1);
v_hName_2775_ = v_a_2803_;
v___y_2776_ = v___y_2727_;
v___y_2777_ = v___y_2728_;
v___y_2778_ = v___y_2729_;
v___y_2779_ = v___y_2730_;
goto v___jp_2774_;
}
else
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
lean_del_object(v___x_2746_);
lean_dec(v_snd_2744_);
lean_dec(v_fst_2743_);
lean_del_object(v___x_2741_);
lean_dec(v_mvarId_2725_);
v_a_2804_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2802_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2802_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2804_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
}
else
{
lean_object* v_val_2812_; 
v_val_2812_ = lean_ctor_get(v_hName_x3f_2726_, 0);
lean_inc(v_val_2812_);
lean_dec_ref_known(v_hName_x3f_2726_, 1);
v_hName_2775_ = v_val_2812_;
v___y_2776_ = v___y_2727_;
v___y_2777_ = v___y_2728_;
v___y_2778_ = v___y_2729_;
v___y_2779_ = v___y_2730_;
goto v___jp_2774_;
}
v___jp_2748_:
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Lean_MVarId_byCasesDec(v_mvarId_2725_, v_fst_2743_, v_snd_2744_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2765_; 
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2757_ = v___x_2754_;
v_isShared_2758_ = v_isSharedCheck_2765_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2754_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2765_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 0, v_a_2755_);
v___x_2760_ = v___x_2741_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
lean_object* v___x_2762_; 
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 0, v___x_2760_);
v___x_2762_ = v___x_2757_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v___x_2760_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
else
{
lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
lean_del_object(v___x_2741_);
v_a_2766_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2768_ = v___x_2754_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2754_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2766_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
v___jp_2774_:
{
lean_object* v_toCold_2780_; lean_object* v_options_2781_; uint8_t v_hasTrace_2782_; 
v_toCold_2780_ = lean_ctor_get(v___y_2778_, 0);
v_options_2781_ = lean_ctor_get(v_toCold_2780_, 2);
v_hasTrace_2782_ = lean_ctor_get_uint8(v_options_2781_, sizeof(void*)*1);
if (v_hasTrace_2782_ == 0)
{
lean_del_object(v___x_2746_);
v___y_2749_ = v_hName_2775_;
v___y_2750_ = v___y_2776_;
v___y_2751_ = v___y_2777_;
v___y_2752_ = v___y_2778_;
v___y_2753_ = v___y_2779_;
goto v___jp_2748_;
}
else
{
lean_object* v_inheritedTraceOptions_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; uint8_t v___x_2786_; 
v_inheritedTraceOptions_2783_ = lean_ctor_get(v_toCold_2780_, 11);
v___x_2784_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9));
v___x_2785_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10);
v___x_2786_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2783_, v_options_2781_, v___x_2785_);
if (v___x_2786_ == 0)
{
lean_del_object(v___x_2746_);
v___y_2749_ = v_hName_2775_;
v___y_2750_ = v___y_2776_;
v___y_2751_ = v___y_2777_;
v___y_2752_ = v___y_2778_;
v___y_2753_ = v___y_2779_;
goto v___jp_2748_;
}
else
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2790_; 
v___x_2787_ = lean_obj_once(&l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1, &l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1_once, _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1);
lean_inc(v_snd_2744_);
v___x_2788_ = l_Lean_MessageData_ofExpr(v_snd_2744_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set_tag(v___x_2746_, 7);
lean_ctor_set(v___x_2746_, 1, v___x_2788_);
lean_ctor_set(v___x_2746_, 0, v___x_2787_);
v___x_2790_ = v___x_2746_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v___x_2787_);
lean_ctor_set(v_reuseFailAlloc_2800_, 1, v___x_2788_);
v___x_2790_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
lean_object* v___x_2791_; 
v___x_2791_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_2784_, v___x_2790_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_dec_ref_known(v___x_2791_, 1);
v___y_2749_ = v_hName_2775_;
v___y_2750_ = v___y_2776_;
v___y_2751_ = v___y_2777_;
v___y_2752_ = v___y_2778_;
v___y_2753_ = v___y_2779_;
goto v___jp_2748_;
}
else
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
lean_dec(v_hName_2775_);
lean_dec(v_snd_2744_);
lean_dec(v_fst_2743_);
lean_del_object(v___x_2741_);
lean_dec(v_mvarId_2725_);
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2791_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2791_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2792_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
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
lean_object* v_toCold_2815_; lean_object* v_options_2816_; uint8_t v_hasTrace_2817_; 
lean_dec(v_a_2738_);
lean_dec(v_hName_x3f_2726_);
lean_dec(v_mvarId_2725_);
v_toCold_2815_ = lean_ctor_get(v___y_2729_, 0);
v_options_2816_ = lean_ctor_get(v_toCold_2815_, 2);
v_hasTrace_2817_ = lean_ctor_get_uint8(v_options_2816_, sizeof(void*)*1);
if (v_hasTrace_2817_ == 0)
{
lean_dec(v_a_2736_);
goto v___jp_2732_;
}
else
{
lean_object* v_inheritedTraceOptions_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; uint8_t v___x_2821_; 
v_inheritedTraceOptions_2818_ = lean_ctor_get(v_toCold_2815_, 11);
v___x_2819_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9));
v___x_2820_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10);
v___x_2821_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2818_, v_options_2816_, v___x_2820_);
if (v___x_2821_ == 0)
{
lean_dec(v_a_2736_);
goto v___jp_2732_;
}
else
{
lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2822_ = lean_obj_once(&l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3, &l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3_once, _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3);
v___x_2823_ = l_Lean_indentExpr(v_a_2736_);
v___x_2824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2822_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
v___x_2825_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_2819_, v___x_2824_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_dec_ref_known(v___x_2825_, 1);
goto v___jp_2732_;
}
else
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2825_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2825_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
if (v_isShared_2829_ == 0)
{
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2826_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_dec(v_a_2736_);
lean_dec(v_hName_x3f_2726_);
lean_dec(v_mvarId_2725_);
v_a_2834_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2737_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2737_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
v___jp_2732_:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2733_ = lean_box(0);
v___x_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2733_);
return v___x_2734_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___boxed(lean_object* v_e_2842_, lean_object* v_mvarId_2843_, lean_object* v_hName_x3f_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
lean_object* v_res_2850_; 
v_res_2850_ = l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0(v_e_2842_, v_mvarId_2843_, v_hName_x3f_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f(lean_object* v_mvarId_2851_, lean_object* v_e_2852_, lean_object* v_hName_x3f_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_){
_start:
{
lean_object* v___f_2859_; lean_object* v___x_2860_; 
lean_inc(v_mvarId_2851_);
v___f_2859_ = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2859_, 0, v_e_2852_);
lean_closure_set(v___f_2859_, 1, v_mvarId_2851_);
lean_closure_set(v___f_2859_, 2, v_hName_x3f_2853_);
v___x_2860_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2851_, v___f_2859_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___boxed(lean_object* v_mvarId_2861_, lean_object* v_e_2862_, lean_object* v_hName_x3f_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(v_mvarId_2861_, v_e_2862_, v_hName_x3f_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_);
lean_dec(v_a_2867_);
lean_dec_ref(v_a_2866_);
lean_dec(v_a_2865_);
lean_dec_ref(v_a_2864_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0(lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
lean_object* v_lctx_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v_lctx_2875_ = lean_ctor_get(v___y_2870_, 2);
lean_inc_ref(v_lctx_2875_);
lean_dec_ref(v___y_2870_);
v___x_2876_ = lean_local_ctx_num_indices(v_lctx_2875_);
v___x_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0___boxed(lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0(v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2879_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(lean_object* v_mvarId_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_){
_start:
{
lean_object* v___f_2891_; lean_object* v___x_2892_; 
v___f_2891_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___closed__0));
v___x_2892_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2885_, v___f_2891_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___boxed(lean_object* v_mvarId_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(v_mvarId_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
lean_dec(v_a_2897_);
lean_dec_ref(v_a_2896_);
lean_dec(v_a_2895_);
lean_dec_ref(v_a_2894_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_simpIfTarget_spec__0(lean_object* v_msg_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_){
_start:
{
lean_object* v___f_2907_; lean_object* v___x_1613__overap_2908_; lean_object* v___x_2909_; 
v___f_2907_ = ((lean_object*)(l_panic___at___00Lean_Meta_simpIfTarget_spec__0___closed__0));
v___x_1613__overap_2908_ = lean_panic_fn_borrowed(v___f_2907_, v_msg_2901_);
lean_inc(v___y_2905_);
lean_inc_ref(v___y_2904_);
lean_inc(v___y_2903_);
lean_inc_ref(v___y_2902_);
v___x_2909_ = lean_apply_5(v___x_1613__overap_2908_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, lean_box(0));
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_simpIfTarget_spec__0___boxed(lean_object* v_msg_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v_msg_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
return v_res_2916_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(lean_object* v_opts_2917_, lean_object* v_opt_2918_){
_start:
{
lean_object* v_name_2919_; lean_object* v_defValue_2920_; lean_object* v_map_2921_; lean_object* v___x_2922_; 
v_name_2919_ = lean_ctor_get(v_opt_2918_, 0);
v_defValue_2920_ = lean_ctor_get(v_opt_2918_, 1);
v_map_2921_ = lean_ctor_get(v_opts_2917_, 0);
v___x_2922_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2921_, v_name_2919_);
if (lean_obj_tag(v___x_2922_) == 0)
{
uint8_t v___x_2923_; 
v___x_2923_ = lean_unbox(v_defValue_2920_);
return v___x_2923_;
}
else
{
lean_object* v_val_2924_; 
v_val_2924_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_val_2924_);
lean_dec_ref_known(v___x_2922_, 1);
if (lean_obj_tag(v_val_2924_) == 1)
{
uint8_t v_v_2925_; 
v_v_2925_ = lean_ctor_get_uint8(v_val_2924_, 0);
lean_dec_ref_known(v_val_2924_, 0);
return v_v_2925_;
}
else
{
uint8_t v___x_2926_; 
lean_dec(v_val_2924_);
v___x_2926_ = lean_unbox(v_defValue_2920_);
return v___x_2926_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1___boxed(lean_object* v_opts_2927_, lean_object* v_opt_2928_){
_start:
{
uint8_t v_res_2929_; lean_object* v_r_2930_; 
v_res_2929_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v_opts_2927_, v_opt_2928_);
lean_dec_ref(v_opt_2928_);
lean_dec_ref(v_opts_2927_);
v_r_2930_ = lean_box(v_res_2929_);
return v_r_2930_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__0(void){
_start:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2931_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__0);
v___x_2932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2931_);
return v___x_2932_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__1(void){
_start:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2933_ = lean_unsigned_to_nat(0u);
v___x_2934_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__0, &l_Lean_Meta_simpIfTarget___closed__0_once, _init_l_Lean_Meta_simpIfTarget___closed__0);
v___x_2935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2934_);
lean_ctor_set(v___x_2935_, 1, v___x_2933_);
return v___x_2935_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__2(void){
_start:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2936_ = lean_unsigned_to_nat(32u);
v___x_2937_ = lean_mk_empty_array_with_capacity(v___x_2936_);
v___x_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
return v___x_2938_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__3(void){
_start:
{
size_t v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2939_ = ((size_t)5ULL);
v___x_2940_ = lean_unsigned_to_nat(0u);
v___x_2941_ = lean_unsigned_to_nat(32u);
v___x_2942_ = lean_mk_empty_array_with_capacity(v___x_2941_);
v___x_2943_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__2, &l_Lean_Meta_simpIfTarget___closed__2_once, _init_l_Lean_Meta_simpIfTarget___closed__2);
v___x_2944_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2944_, 0, v___x_2943_);
lean_ctor_set(v___x_2944_, 1, v___x_2942_);
lean_ctor_set(v___x_2944_, 2, v___x_2940_);
lean_ctor_set(v___x_2944_, 3, v___x_2940_);
lean_ctor_set_usize(v___x_2944_, 4, v___x_2939_);
return v___x_2944_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__4(void){
_start:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2945_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__3, &l_Lean_Meta_simpIfTarget___closed__3_once, _init_l_Lean_Meta_simpIfTarget___closed__3);
v___x_2946_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__0, &l_Lean_Meta_simpIfTarget___closed__0_once, _init_l_Lean_Meta_simpIfTarget___closed__0);
v___x_2947_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2946_);
lean_ctor_set(v___x_2947_, 1, v___x_2946_);
lean_ctor_set(v___x_2947_, 2, v___x_2946_);
lean_ctor_set(v___x_2947_, 3, v___x_2945_);
return v___x_2947_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__5(void){
_start:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2948_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__4, &l_Lean_Meta_simpIfTarget___closed__4_once, _init_l_Lean_Meta_simpIfTarget___closed__4);
v___x_2949_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__1, &l_Lean_Meta_simpIfTarget___closed__1_once, _init_l_Lean_Meta_simpIfTarget___closed__1);
v___x_2950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
lean_ctor_set(v___x_2950_, 1, v___x_2948_);
return v___x_2950_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__9(void){
_start:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2954_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__8));
v___x_2955_ = lean_unsigned_to_nat(78u);
v___x_2956_ = lean_unsigned_to_nat(289u);
v___x_2957_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_2958_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__6));
v___x_2959_ = l_mkPanicMessageWithDecl(v___x_2958_, v___x_2957_, v___x_2956_, v___x_2955_, v___x_2954_);
return v___x_2959_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__11(void){
_start:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2962_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__8));
v___x_2963_ = lean_unsigned_to_nat(128u);
v___x_2964_ = lean_unsigned_to_nat(293u);
v___x_2965_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_2966_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__6));
v___x_2967_ = l_mkPanicMessageWithDecl(v___x_2966_, v___x_2965_, v___x_2964_, v___x_2963_, v___x_2962_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfTarget(lean_object* v_mvarId_2968_, uint8_t v_useDecide_2969_, uint8_t v_useNewSemantics_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_){
_start:
{
if (v_useNewSemantics_2970_ == 0)
{
lean_object* v___x_3023_; lean_object* v___x_3024_; uint8_t v___x_3025_; 
v___x_3023_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2973_);
v___x_3024_ = l_Lean_Meta_backward_split;
v___x_3025_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v___x_3023_, v___x_3024_);
lean_dec_ref(v___x_3023_);
if (v___x_3025_ == 0)
{
goto v___jp_2976_;
}
else
{
lean_object* v___x_3026_; 
v___x_3026_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_object* v_a_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v_a_3027_ = lean_ctor_get(v___x_3026_, 0);
lean_inc(v_a_3027_);
lean_dec_ref_known(v___x_3026_, 1);
v___x_3028_ = lean_box(v_useDecide_2969_);
v___x_3029_ = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed), 6, 1);
lean_closure_set(v___x_3029_, 0, v___x_3028_);
lean_inc(v_mvarId_2968_);
v___x_3030_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2968_, v___x_3029_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3031_);
lean_dec_ref_known(v___x_3030_, 1);
v___x_3032_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__10));
v___x_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3033_, 0, v_a_3031_);
v___x_3034_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__5, &l_Lean_Meta_simpIfTarget___closed__5_once, _init_l_Lean_Meta_simpIfTarget___closed__5);
v___x_3035_ = l_Lean_Meta_simpTarget(v_mvarId_2968_, v_a_3027_, v___x_3032_, v___x_3033_, v_useNewSemantics_2970_, v___x_3034_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3047_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3038_ = v___x_3035_;
v_isShared_3039_ = v_isSharedCheck_3047_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3035_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3047_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v_fst_3040_; 
v_fst_3040_ = lean_ctor_get(v_a_3036_, 0);
lean_inc(v_fst_3040_);
lean_dec(v_a_3036_);
if (lean_obj_tag(v_fst_3040_) == 1)
{
lean_object* v_val_3041_; lean_object* v___x_3043_; 
v_val_3041_ = lean_ctor_get(v_fst_3040_, 0);
lean_inc(v_val_3041_);
lean_dec_ref_known(v_fst_3040_, 1);
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 0, v_val_3041_);
v___x_3043_ = v___x_3038_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_val_3041_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
else
{
lean_object* v___x_3045_; lean_object* v___x_3046_; 
lean_dec(v_fst_3040_);
lean_del_object(v___x_3038_);
v___x_3045_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__11, &l_Lean_Meta_simpIfTarget___closed__11_once, _init_l_Lean_Meta_simpIfTarget___closed__11);
v___x_3046_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3045_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
return v___x_3046_;
}
}
}
else
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3055_; 
v_a_3048_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3050_ = v___x_3035_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_3035_);
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
else
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_dec(v_a_3027_);
lean_dec(v_mvarId_2968_);
v_a_3056_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_3030_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3030_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
lean_dec(v_mvarId_2968_);
v_a_3064_ = lean_ctor_get(v___x_3026_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_3026_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_3026_);
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
}
else
{
goto v___jp_2976_;
}
v___jp_2976_:
{
lean_object* v___x_2977_; 
v___x_2977_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_2971_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; lean_object* v___x_2979_; 
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_a_2978_);
lean_dec_ref_known(v___x_2977_, 1);
lean_inc(v_mvarId_2968_);
v___x_2979_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(v_mvarId_2968_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2980_; lean_object* v___x_2981_; lean_object* v_a_2982_; lean_object* v___x_2983_; uint8_t v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_a_2980_);
lean_dec_ref_known(v___x_2979_, 1);
v___x_2981_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_a_2980_, v_useDecide_2969_);
v_a_2982_ = lean_ctor_get(v___x_2981_, 0);
lean_inc(v_a_2982_);
lean_dec_ref(v___x_2981_);
v___x_2983_ = lean_box(0);
v___x_2984_ = 0;
v___x_2985_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__5, &l_Lean_Meta_simpIfTarget___closed__5_once, _init_l_Lean_Meta_simpIfTarget___closed__5);
v___x_2986_ = l_Lean_Meta_simpTarget(v_mvarId_2968_, v_a_2978_, v_a_2982_, v___x_2983_, v___x_2984_, v___x_2985_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2998_; 
v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2989_ = v___x_2986_;
v_isShared_2990_ = v_isSharedCheck_2998_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v___x_2986_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2998_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v_fst_2991_; 
v_fst_2991_ = lean_ctor_get(v_a_2987_, 0);
lean_inc(v_fst_2991_);
lean_dec(v_a_2987_);
if (lean_obj_tag(v_fst_2991_) == 1)
{
lean_object* v_val_2992_; lean_object* v___x_2994_; 
v_val_2992_ = lean_ctor_get(v_fst_2991_, 0);
lean_inc(v_val_2992_);
lean_dec_ref_known(v_fst_2991_, 1);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 0, v_val_2992_);
v___x_2994_ = v___x_2989_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_val_2992_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
else
{
lean_object* v___x_2996_; lean_object* v___x_2997_; 
lean_dec(v_fst_2991_);
lean_del_object(v___x_2989_);
v___x_2996_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__9, &l_Lean_Meta_simpIfTarget___closed__9_once, _init_l_Lean_Meta_simpIfTarget___closed__9);
v___x_2997_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_2996_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
return v___x_2997_;
}
}
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
v_a_2999_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2986_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2986_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
lean_dec(v_a_2978_);
lean_dec(v_mvarId_2968_);
v_a_3007_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_2979_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_2979_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
lean_dec(v_mvarId_2968_);
v_a_3015_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_2977_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_2977_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfTarget___boxed(lean_object* v_mvarId_3072_, lean_object* v_useDecide_3073_, lean_object* v_useNewSemantics_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_){
_start:
{
uint8_t v_useDecide_boxed_3080_; uint8_t v_useNewSemantics_boxed_3081_; lean_object* v_res_3082_; 
v_useDecide_boxed_3080_ = lean_unbox(v_useDecide_3073_);
v_useNewSemantics_boxed_3081_ = lean_unbox(v_useNewSemantics_3074_);
v_res_3082_ = l_Lean_Meta_simpIfTarget(v_mvarId_3072_, v_useDecide_boxed_3080_, v_useNewSemantics_boxed_3081_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_);
lean_dec(v_a_3078_);
lean_dec_ref(v_a_3077_);
lean_dec(v_a_3076_);
lean_dec_ref(v_a_3075_);
return v_res_3082_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfLocalDecl___closed__1(void){
_start:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3084_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__8));
v___x_3085_ = lean_unsigned_to_nat(93u);
v___x_3086_ = lean_unsigned_to_nat(305u);
v___x_3087_ = ((lean_object*)(l_Lean_Meta_simpIfLocalDecl___closed__0));
v___x_3088_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__6));
v___x_3089_ = l_mkPanicMessageWithDecl(v___x_3088_, v___x_3087_, v___x_3086_, v___x_3085_, v___x_3084_);
return v___x_3089_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfLocalDecl___closed__2(void){
_start:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3090_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__8));
v___x_3091_ = lean_unsigned_to_nat(133u);
v___x_3092_ = lean_unsigned_to_nat(309u);
v___x_3093_ = ((lean_object*)(l_Lean_Meta_simpIfLocalDecl___closed__0));
v___x_3094_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__6));
v___x_3095_ = l_mkPanicMessageWithDecl(v___x_3094_, v___x_3093_, v___x_3092_, v___x_3091_, v___x_3090_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfLocalDecl(lean_object* v_mvarId_3096_, lean_object* v_fvarId_3097_, uint8_t v_useNewSemantics_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_){
_start:
{
if (v_useNewSemantics_3098_ == 0)
{
lean_object* v___x_3152_; lean_object* v___x_3153_; uint8_t v___x_3154_; 
v___x_3152_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_3101_);
v___x_3153_ = l_Lean_Meta_backward_split;
v___x_3154_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v___x_3152_, v___x_3153_);
lean_dec_ref(v___x_3152_);
if (v___x_3154_ == 0)
{
goto v___jp_3104_;
}
else
{
lean_object* v___x_3155_; 
v___x_3155_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
if (lean_obj_tag(v___x_3155_) == 0)
{
lean_object* v_a_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v_a_3156_ = lean_ctor_get(v___x_3155_, 0);
lean_inc(v_a_3156_);
lean_dec_ref_known(v___x_3155_, 1);
v___x_3157_ = lean_box(v_useNewSemantics_3098_);
v___x_3158_ = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed), 6, 1);
lean_closure_set(v___x_3158_, 0, v___x_3157_);
lean_inc(v_mvarId_3096_);
v___x_3159_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_3096_, v___x_3158_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_a_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_a_3160_);
lean_dec_ref_known(v___x_3159_, 1);
v___x_3161_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__10));
v___x_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3162_, 0, v_a_3160_);
v___x_3163_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__5, &l_Lean_Meta_simpIfTarget___closed__5_once, _init_l_Lean_Meta_simpIfTarget___closed__5);
v___x_3164_ = l_Lean_Meta_simpLocalDecl(v_mvarId_3096_, v_fvarId_3097_, v_a_3156_, v___x_3161_, v___x_3162_, v_useNewSemantics_3098_, v___x_3163_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3177_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3167_ = v___x_3164_;
v_isShared_3168_ = v_isSharedCheck_3177_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_dec(v___x_3164_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3177_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v_fst_3169_; 
v_fst_3169_ = lean_ctor_get(v_a_3165_, 0);
lean_inc(v_fst_3169_);
lean_dec(v_a_3165_);
if (lean_obj_tag(v_fst_3169_) == 1)
{
lean_object* v_val_3170_; lean_object* v_snd_3171_; lean_object* v___x_3173_; 
v_val_3170_ = lean_ctor_get(v_fst_3169_, 0);
lean_inc(v_val_3170_);
lean_dec_ref_known(v_fst_3169_, 1);
v_snd_3171_ = lean_ctor_get(v_val_3170_, 1);
lean_inc(v_snd_3171_);
lean_dec(v_val_3170_);
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 0, v_snd_3171_);
v___x_3173_ = v___x_3167_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_snd_3171_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
else
{
lean_object* v___x_3175_; lean_object* v___x_3176_; 
lean_dec(v_fst_3169_);
lean_del_object(v___x_3167_);
v___x_3175_ = lean_obj_once(&l_Lean_Meta_simpIfLocalDecl___closed__2, &l_Lean_Meta_simpIfLocalDecl___closed__2_once, _init_l_Lean_Meta_simpIfLocalDecl___closed__2);
v___x_3176_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3175_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
return v___x_3176_;
}
}
}
else
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3185_; 
v_a_3178_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3180_ = v___x_3164_;
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3164_);
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
else
{
lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3193_; 
lean_dec(v_a_3156_);
lean_dec(v_fvarId_3097_);
lean_dec(v_mvarId_3096_);
v_a_3186_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3188_ = v___x_3159_;
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v___x_3159_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3191_; 
if (v_isShared_3189_ == 0)
{
v___x_3191_ = v___x_3188_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3186_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
else
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3201_; 
lean_dec(v_fvarId_3097_);
lean_dec(v_mvarId_3096_);
v_a_3194_ = lean_ctor_get(v___x_3155_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3155_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3196_ = v___x_3155_;
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3155_);
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
}
else
{
goto v___jp_3104_;
}
v___jp_3104_:
{
lean_object* v___x_3105_; 
v___x_3105_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_3099_, v_a_3101_, v_a_3102_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v_a_3106_; lean_object* v___x_3107_; 
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
lean_inc(v_a_3106_);
lean_dec_ref_known(v___x_3105_, 1);
lean_inc(v_mvarId_3096_);
v___x_3107_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(v_mvarId_3096_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; uint8_t v___x_3109_; lean_object* v___x_3110_; lean_object* v_a_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
lean_inc(v_a_3108_);
lean_dec_ref_known(v___x_3107_, 1);
v___x_3109_ = 0;
v___x_3110_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_a_3108_, v___x_3109_);
v_a_3111_ = lean_ctor_get(v___x_3110_, 0);
lean_inc(v_a_3111_);
lean_dec_ref(v___x_3110_);
v___x_3112_ = lean_box(0);
v___x_3113_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__5, &l_Lean_Meta_simpIfTarget___closed__5_once, _init_l_Lean_Meta_simpIfTarget___closed__5);
v___x_3114_ = l_Lean_Meta_simpLocalDecl(v_mvarId_3096_, v_fvarId_3097_, v_a_3106_, v_a_3111_, v___x_3112_, v___x_3109_, v___x_3113_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3127_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3117_ = v___x_3114_;
v_isShared_3118_ = v_isSharedCheck_3127_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3114_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3127_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v_fst_3119_; 
v_fst_3119_ = lean_ctor_get(v_a_3115_, 0);
lean_inc(v_fst_3119_);
lean_dec(v_a_3115_);
if (lean_obj_tag(v_fst_3119_) == 1)
{
lean_object* v_val_3120_; lean_object* v_snd_3121_; lean_object* v___x_3123_; 
v_val_3120_ = lean_ctor_get(v_fst_3119_, 0);
lean_inc(v_val_3120_);
lean_dec_ref_known(v_fst_3119_, 1);
v_snd_3121_ = lean_ctor_get(v_val_3120_, 1);
lean_inc(v_snd_3121_);
lean_dec(v_val_3120_);
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 0, v_snd_3121_);
v___x_3123_ = v___x_3117_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_snd_3121_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
else
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
lean_dec(v_fst_3119_);
lean_del_object(v___x_3117_);
v___x_3125_ = lean_obj_once(&l_Lean_Meta_simpIfLocalDecl___closed__1, &l_Lean_Meta_simpIfLocalDecl___closed__1_once, _init_l_Lean_Meta_simpIfLocalDecl___closed__1);
v___x_3126_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3125_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
return v___x_3126_;
}
}
}
else
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3135_; 
v_a_3128_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3130_ = v___x_3114_;
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3114_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3133_; 
if (v_isShared_3131_ == 0)
{
v___x_3133_ = v___x_3130_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_a_3128_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
lean_dec(v_a_3106_);
lean_dec(v_fvarId_3097_);
lean_dec(v_mvarId_3096_);
v_a_3136_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3107_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3107_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
lean_dec(v_fvarId_3097_);
lean_dec(v_mvarId_3096_);
v_a_3144_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3105_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3105_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfLocalDecl___boxed(lean_object* v_mvarId_3202_, lean_object* v_fvarId_3203_, lean_object* v_useNewSemantics_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_){
_start:
{
uint8_t v_useNewSemantics_boxed_3210_; lean_object* v_res_3211_; 
v_useNewSemantics_boxed_3210_ = lean_unbox(v_useNewSemantics_3204_);
v_res_3211_ = l_Lean_Meta_simpIfLocalDecl(v_mvarId_3202_, v_fvarId_3203_, v_useNewSemantics_boxed_3210_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_);
lean_dec(v_a_3208_);
lean_dec_ref(v_a_3207_);
lean_dec(v_a_3206_);
lean_dec_ref(v_a_3205_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(lean_object* v_x_x3f_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_){
_start:
{
lean_object* v___x_3218_; 
v___x_3218_ = l_Lean_Meta_saveState___redArg(v___y_3214_, v___y_3216_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3263_; 
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3221_ = v___x_3218_;
v_isShared_3222_ = v_isSharedCheck_3263_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3218_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3263_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___y_3224_; uint8_t v___y_3225_; lean_object* v_a_3247_; lean_object* v___x_3250_; 
lean_inc(v___y_3216_);
lean_inc_ref(v___y_3215_);
lean_inc(v___y_3214_);
lean_inc_ref(v___y_3213_);
v___x_3250_ = lean_apply_5(v_x_x3f_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, lean_box(0));
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_a_3251_; 
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_a_3251_);
if (lean_obj_tag(v_a_3251_) == 0)
{
lean_object* v___x_3252_; 
lean_dec_ref_known(v___x_3250_, 1);
lean_inc(v_a_3219_);
v___x_3252_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3219_, v___y_3214_, v___y_3216_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
lean_del_object(v___x_3221_);
lean_dec(v_a_3219_);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3259_ == 0)
{
lean_object* v_unused_3260_; 
v_unused_3260_ = lean_ctor_get(v___x_3252_, 0);
lean_dec(v_unused_3260_);
v___x_3254_ = v___x_3252_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_dec(v___x_3252_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3257_; 
if (v_isShared_3255_ == 0)
{
lean_ctor_set(v___x_3254_, 0, v_a_3251_);
v___x_3257_ = v___x_3254_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_a_3251_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
else
{
lean_object* v_a_3261_; 
v_a_3261_ = lean_ctor_get(v___x_3252_, 0);
lean_inc(v_a_3261_);
lean_dec_ref_known(v___x_3252_, 1);
v_a_3247_ = v_a_3261_;
goto v___jp_3246_;
}
}
else
{
lean_dec_ref_known(v_a_3251_, 1);
lean_del_object(v___x_3221_);
lean_dec(v_a_3219_);
return v___x_3250_;
}
}
else
{
lean_object* v_a_3262_; 
v_a_3262_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_a_3262_);
lean_dec_ref_known(v___x_3250_, 1);
v_a_3247_ = v_a_3262_;
goto v___jp_3246_;
}
v___jp_3223_:
{
if (v___y_3225_ == 0)
{
lean_object* v___x_3226_; 
lean_del_object(v___x_3221_);
v___x_3226_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3219_, v___y_3214_, v___y_3216_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3233_ == 0)
{
lean_object* v_unused_3234_; 
v_unused_3234_ = lean_ctor_get(v___x_3226_, 0);
lean_dec(v_unused_3234_);
v___x_3228_ = v___x_3226_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_dec(v___x_3226_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3229_ == 0)
{
lean_ctor_set_tag(v___x_3228_, 1);
lean_ctor_set(v___x_3228_, 0, v___y_3224_);
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v___y_3224_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
else
{
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3242_; 
lean_dec_ref(v___y_3224_);
v_a_3235_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3237_ = v___x_3226_;
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3226_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3240_; 
if (v_isShared_3238_ == 0)
{
v___x_3240_ = v___x_3237_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3235_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
else
{
lean_object* v___x_3244_; 
lean_dec(v_a_3219_);
if (v_isShared_3222_ == 0)
{
lean_ctor_set_tag(v___x_3221_, 1);
lean_ctor_set(v___x_3221_, 0, v___y_3224_);
v___x_3244_ = v___x_3221_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___y_3224_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
v___jp_3246_:
{
uint8_t v___x_3248_; 
v___x_3248_ = l_Lean_Exception_isInterrupt(v_a_3247_);
if (v___x_3248_ == 0)
{
uint8_t v___x_3249_; 
lean_inc_ref(v_a_3247_);
v___x_3249_ = l_Lean_Exception_isRuntime(v_a_3247_);
v___y_3224_ = v_a_3247_;
v___y_3225_ = v___x_3249_;
goto v___jp_3223_;
}
else
{
v___y_3224_ = v_a_3247_;
v___y_3225_ = v___x_3248_;
goto v___jp_3223_;
}
}
}
}
else
{
lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3271_; 
lean_dec_ref(v_x_x3f_3212_);
v_a_3264_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3266_ = v___x_3218_;
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_dec(v___x_3218_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3269_; 
if (v_isShared_3267_ == 0)
{
v___x_3269_ = v___x_3266_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3264_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg___boxed(lean_object* v_x_x3f_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v_x_x3f_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0(lean_object* v_00_u03b1_3279_, lean_object* v_x_x3f_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_){
_start:
{
lean_object* v___x_3286_; 
v___x_3286_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v_x_x3f_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___boxed(lean_object* v_00_u03b1_3287_, lean_object* v_x_x3f_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
lean_object* v_res_3294_; 
v_res_3294_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0(v_00_u03b1_3287_, v_x_x3f_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec(v___y_3290_);
lean_dec_ref(v___y_3289_);
return v_res_3294_;
}
}
static lean_object* _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3299_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1));
v___x_3300_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4));
v___x_3301_ = l_Lean_Name_append(v___x_3300_, v___x_3299_);
return v___x_3301_;
}
}
static lean_object* _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3303_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__3));
v___x_3304_ = l_Lean_stringToMessageData(v___x_3303_);
return v___x_3304_;
}
}
static lean_object* _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3306_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__5));
v___x_3307_ = l_Lean_stringToMessageData(v___x_3306_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0(lean_object* v_mvarId_3308_, lean_object* v_hName_x3f_3309_, uint8_t v_useNewSemantics_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_){
_start:
{
lean_object* v___x_3319_; 
lean_inc(v_mvarId_3308_);
v___x_3319_ = l_Lean_MVarId_getType(v_mvarId_3308_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_a_3320_; lean_object* v___x_3321_; 
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
lean_inc(v_a_3320_);
lean_dec_ref_known(v___x_3319_, 1);
v___x_3321_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(v_mvarId_3308_, v_a_3320_, v_hName_x3f_3309_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3419_; 
v_a_3322_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3324_ = v___x_3321_;
v_isShared_3325_ = v_isSharedCheck_3419_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3321_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3419_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
if (lean_obj_tag(v_a_3322_) == 1)
{
lean_object* v_val_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3414_; 
lean_del_object(v___x_3324_);
v_val_3326_ = lean_ctor_get(v_a_3322_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v_a_3322_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3328_ = v_a_3322_;
v_isShared_3329_ = v_isSharedCheck_3414_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_val_3326_);
lean_dec(v_a_3322_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3414_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v_fst_3330_; lean_object* v_snd_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3413_; 
v_fst_3330_ = lean_ctor_get(v_val_3326_, 0);
v_snd_3331_ = lean_ctor_get(v_val_3326_, 1);
v_isSharedCheck_3413_ = !lean_is_exclusive(v_val_3326_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3333_ = v_val_3326_;
v_isShared_3334_ = v_isSharedCheck_3413_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_snd_3331_);
lean_inc(v_fst_3330_);
lean_dec(v_val_3326_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3413_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v_mvarId_3335_; lean_object* v_fvarId_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3412_; 
v_mvarId_3335_ = lean_ctor_get(v_fst_3330_, 0);
v_fvarId_3336_ = lean_ctor_get(v_fst_3330_, 1);
v_isSharedCheck_3412_ = !lean_is_exclusive(v_fst_3330_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3338_ = v_fst_3330_;
v_isShared_3339_ = v_isSharedCheck_3412_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_fvarId_3336_);
lean_inc(v_mvarId_3335_);
lean_dec(v_fst_3330_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3412_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
uint8_t v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = 0;
lean_inc(v_mvarId_3335_);
v___x_3341_ = l_Lean_Meta_simpIfTarget(v_mvarId_3335_, v___x_3340_, v_useNewSemantics_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3342_; lean_object* v_mvarId_3343_; lean_object* v_fvarId_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3403_; 
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_a_3342_);
lean_dec_ref_known(v___x_3341_, 1);
v_mvarId_3343_ = lean_ctor_get(v_snd_3331_, 0);
v_fvarId_3344_ = lean_ctor_get(v_snd_3331_, 1);
v_isSharedCheck_3403_ = !lean_is_exclusive(v_snd_3331_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3346_ = v_snd_3331_;
v_isShared_3347_ = v_isSharedCheck_3403_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_fvarId_3344_);
lean_inc(v_mvarId_3343_);
lean_dec(v_snd_3331_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3403_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3348_; 
lean_inc(v_mvarId_3343_);
v___x_3348_ = l_Lean_Meta_simpIfTarget(v_mvarId_3343_, v___x_3340_, v_useNewSemantics_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3394_; 
v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3351_ = v___x_3348_;
v_isShared_3352_ = v_isSharedCheck_3394_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3348_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3394_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
uint8_t v___x_3369_; 
v___x_3369_ = l_Lean_instBEqMVarId_beq(v_mvarId_3335_, v_a_3342_);
lean_dec(v_mvarId_3335_);
if (v___x_3369_ == 0)
{
lean_dec(v_mvarId_3343_);
goto v___jp_3353_;
}
else
{
uint8_t v___x_3370_; 
v___x_3370_ = l_Lean_instBEqMVarId_beq(v_mvarId_3343_, v_a_3349_);
lean_dec(v_mvarId_3343_);
if (v___x_3370_ == 0)
{
goto v___jp_3353_;
}
else
{
lean_object* v_toCold_3371_; lean_object* v_options_3372_; uint8_t v_hasTrace_3373_; 
lean_del_object(v___x_3351_);
lean_del_object(v___x_3346_);
lean_dec(v_fvarId_3344_);
lean_del_object(v___x_3338_);
lean_dec(v_fvarId_3336_);
lean_del_object(v___x_3333_);
lean_del_object(v___x_3328_);
v_toCold_3371_ = lean_ctor_get(v___y_3313_, 0);
v_options_3372_ = lean_ctor_get(v_toCold_3371_, 2);
v_hasTrace_3373_ = lean_ctor_get_uint8(v_options_3372_, sizeof(void*)*1);
if (v_hasTrace_3373_ == 0)
{
lean_dec(v_a_3349_);
lean_dec(v_a_3342_);
goto v___jp_3316_;
}
else
{
lean_object* v_inheritedTraceOptions_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; uint8_t v___x_3377_; 
v_inheritedTraceOptions_3374_ = lean_ctor_get(v_toCold_3371_, 11);
v___x_3375_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1));
v___x_3376_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2);
v___x_3377_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3374_, v_options_3372_, v___x_3376_);
if (v___x_3377_ == 0)
{
lean_dec(v_a_3349_);
lean_dec(v_a_3342_);
goto v___jp_3316_;
}
else
{
lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3378_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4);
v___x_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3379_, 0, v_a_3342_);
v___x_3380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3378_);
lean_ctor_set(v___x_3380_, 1, v___x_3379_);
v___x_3381_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6);
v___x_3382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3380_);
lean_ctor_set(v___x_3382_, 1, v___x_3381_);
v___x_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3383_, 0, v_a_3349_);
v___x_3384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3382_);
lean_ctor_set(v___x_3384_, 1, v___x_3383_);
v___x_3385_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_3375_, v___x_3384_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_dec_ref_known(v___x_3385_, 1);
goto v___jp_3316_;
}
else
{
lean_object* v_a_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3393_; 
v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3388_ = v___x_3385_;
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v___x_3385_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3391_; 
if (v_isShared_3389_ == 0)
{
v___x_3391_ = v___x_3388_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_a_3386_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
}
}
}
}
v___jp_3353_:
{
lean_object* v___x_3355_; 
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 1, v_fvarId_3336_);
lean_ctor_set(v___x_3346_, 0, v_a_3342_);
v___x_3355_ = v___x_3346_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_a_3342_);
lean_ctor_set(v_reuseFailAlloc_3368_, 1, v_fvarId_3336_);
v___x_3355_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
lean_object* v___x_3357_; 
if (v_isShared_3339_ == 0)
{
lean_ctor_set(v___x_3338_, 1, v_fvarId_3344_);
lean_ctor_set(v___x_3338_, 0, v_a_3349_);
v___x_3357_ = v___x_3338_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_a_3349_);
lean_ctor_set(v_reuseFailAlloc_3367_, 1, v_fvarId_3344_);
v___x_3357_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
lean_object* v___x_3359_; 
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 1, v___x_3357_);
lean_ctor_set(v___x_3333_, 0, v___x_3355_);
v___x_3359_ = v___x_3333_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v___x_3355_);
lean_ctor_set(v_reuseFailAlloc_3366_, 1, v___x_3357_);
v___x_3359_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
lean_object* v___x_3361_; 
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 0, v___x_3359_);
v___x_3361_ = v___x_3328_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v___x_3359_);
v___x_3361_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
lean_object* v___x_3363_; 
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 0, v___x_3361_);
v___x_3363_ = v___x_3351_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v___x_3361_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
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
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3402_; 
lean_del_object(v___x_3346_);
lean_dec(v_fvarId_3344_);
lean_dec(v_mvarId_3343_);
lean_dec(v_a_3342_);
lean_del_object(v___x_3338_);
lean_dec(v_fvarId_3336_);
lean_dec(v_mvarId_3335_);
lean_del_object(v___x_3333_);
lean_del_object(v___x_3328_);
v_a_3395_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3397_ = v___x_3348_;
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v___x_3348_);
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
}
else
{
lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3411_; 
lean_del_object(v___x_3338_);
lean_dec(v_fvarId_3336_);
lean_dec(v_mvarId_3335_);
lean_del_object(v___x_3333_);
lean_dec(v_snd_3331_);
lean_del_object(v___x_3328_);
v_a_3404_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3406_ = v___x_3341_;
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_a_3404_);
lean_dec(v___x_3341_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3409_; 
if (v_isShared_3407_ == 0)
{
v___x_3409_ = v___x_3406_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_a_3404_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3415_; lean_object* v___x_3417_; 
lean_dec(v_a_3322_);
v___x_3415_ = lean_box(0);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 0, v___x_3415_);
v___x_3417_ = v___x_3324_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v___x_3415_);
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
else
{
return v___x_3321_;
}
}
else
{
lean_object* v_a_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3427_; 
lean_dec(v_hName_x3f_3309_);
lean_dec(v_mvarId_3308_);
v_a_3420_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3422_ = v___x_3319_;
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_a_3420_);
lean_dec(v___x_3319_);
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
v___jp_3316_:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3317_ = lean_box(0);
v___x_3318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3317_);
return v___x_3318_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0___boxed(lean_object* v_mvarId_3428_, lean_object* v_hName_x3f_3429_, lean_object* v_useNewSemantics_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
uint8_t v_useNewSemantics_boxed_3436_; lean_object* v_res_3437_; 
v_useNewSemantics_boxed_3436_ = lean_unbox(v_useNewSemantics_3430_);
v_res_3437_ = l_Lean_Meta_splitIfTarget_x3f___lam__0(v_mvarId_3428_, v_hName_x3f_3429_, v_useNewSemantics_boxed_3436_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f(lean_object* v_mvarId_3438_, lean_object* v_hName_x3f_3439_, uint8_t v_useNewSemantics_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_){
_start:
{
lean_object* v___x_3446_; lean_object* v___f_3447_; lean_object* v___x_3448_; 
v___x_3446_ = lean_box(v_useNewSemantics_3440_);
v___f_3447_ = lean_alloc_closure((void*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3447_, 0, v_mvarId_3438_);
lean_closure_set(v___f_3447_, 1, v_hName_x3f_3439_);
lean_closure_set(v___f_3447_, 2, v___x_3446_);
v___x_3448_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v___f_3447_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
return v___x_3448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___boxed(lean_object* v_mvarId_3449_, lean_object* v_hName_x3f_3450_, lean_object* v_useNewSemantics_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_){
_start:
{
uint8_t v_useNewSemantics_boxed_3457_; lean_object* v_res_3458_; 
v_useNewSemantics_boxed_3457_ = lean_unbox(v_useNewSemantics_3451_);
v_res_3458_ = l_Lean_Meta_splitIfTarget_x3f(v_mvarId_3449_, v_hName_x3f_3450_, v_useNewSemantics_boxed_3457_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_);
lean_dec(v_a_3455_);
lean_dec_ref(v_a_3454_);
lean_dec(v_a_3453_);
lean_dec_ref(v_a_3452_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___lam__0(lean_object* v___x_3459_, lean_object* v_mvarId_3460_, lean_object* v_hName_x3f_3461_, lean_object* v_fvarId_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
lean_object* v___x_3471_; 
lean_inc(v___y_3466_);
lean_inc_ref(v___y_3465_);
lean_inc(v___y_3464_);
lean_inc_ref(v___y_3463_);
v___x_3471_ = lean_infer_type(v___x_3459_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v_a_3472_; lean_object* v___x_3473_; 
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_a_3472_);
lean_dec_ref_known(v___x_3471_, 1);
v___x_3473_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(v_mvarId_3460_, v_a_3472_, v_hName_x3f_3461_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3569_; 
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3476_ = v___x_3473_;
v_isShared_3477_ = v_isSharedCheck_3569_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3473_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3569_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
if (lean_obj_tag(v_a_3474_) == 1)
{
lean_object* v_val_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3564_; 
lean_del_object(v___x_3476_);
v_val_3478_ = lean_ctor_get(v_a_3474_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v_a_3474_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3480_ = v_a_3474_;
v_isShared_3481_ = v_isSharedCheck_3564_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_val_3478_);
lean_dec(v_a_3474_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3564_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v_fst_3482_; lean_object* v_snd_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3563_; 
v_fst_3482_ = lean_ctor_get(v_val_3478_, 0);
v_snd_3483_ = lean_ctor_get(v_val_3478_, 1);
v_isSharedCheck_3563_ = !lean_is_exclusive(v_val_3478_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3485_ = v_val_3478_;
v_isShared_3486_ = v_isSharedCheck_3563_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_snd_3483_);
lean_inc(v_fst_3482_);
lean_dec(v_val_3478_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3563_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v_mvarId_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3561_; 
v_mvarId_3487_ = lean_ctor_get(v_fst_3482_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v_fst_3482_);
if (v_isSharedCheck_3561_ == 0)
{
lean_object* v_unused_3562_; 
v_unused_3562_ = lean_ctor_get(v_fst_3482_, 1);
lean_dec(v_unused_3562_);
v___x_3489_ = v_fst_3482_;
v_isShared_3490_ = v_isSharedCheck_3561_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_mvarId_3487_);
lean_dec(v_fst_3482_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3561_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
uint8_t v___x_3491_; lean_object* v___x_3492_; 
v___x_3491_ = 0;
lean_inc(v_fvarId_3462_);
lean_inc(v_mvarId_3487_);
v___x_3492_ = l_Lean_Meta_simpIfLocalDecl(v_mvarId_3487_, v_fvarId_3462_, v___x_3491_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; lean_object* v_mvarId_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3551_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
lean_inc(v_a_3493_);
lean_dec_ref_known(v___x_3492_, 1);
v_mvarId_3494_ = lean_ctor_get(v_snd_3483_, 0);
v_isSharedCheck_3551_ = !lean_is_exclusive(v_snd_3483_);
if (v_isSharedCheck_3551_ == 0)
{
lean_object* v_unused_3552_; 
v_unused_3552_ = lean_ctor_get(v_snd_3483_, 1);
lean_dec(v_unused_3552_);
v___x_3496_ = v_snd_3483_;
v_isShared_3497_ = v_isSharedCheck_3551_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_mvarId_3494_);
lean_dec(v_snd_3483_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3551_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3498_; 
lean_inc(v_mvarId_3494_);
v___x_3498_ = l_Lean_Meta_simpIfLocalDecl(v_mvarId_3494_, v_fvarId_3462_, v___x_3491_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_a_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3542_; 
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3501_ = v___x_3498_;
v_isShared_3502_ = v_isSharedCheck_3542_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_a_3499_);
lean_dec(v___x_3498_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3542_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
uint8_t v___x_3513_; 
v___x_3513_ = l_Lean_instBEqMVarId_beq(v_mvarId_3487_, v_a_3493_);
lean_dec(v_mvarId_3487_);
if (v___x_3513_ == 0)
{
lean_del_object(v___x_3496_);
lean_dec(v_mvarId_3494_);
lean_del_object(v___x_3489_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
goto v___jp_3503_;
}
else
{
uint8_t v___x_3514_; 
v___x_3514_ = l_Lean_instBEqMVarId_beq(v_mvarId_3494_, v_a_3499_);
lean_dec(v_mvarId_3494_);
if (v___x_3514_ == 0)
{
lean_del_object(v___x_3496_);
lean_del_object(v___x_3489_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
goto v___jp_3503_;
}
else
{
lean_object* v_toCold_3515_; lean_object* v_options_3516_; uint8_t v_hasTrace_3517_; 
lean_del_object(v___x_3501_);
lean_del_object(v___x_3485_);
lean_del_object(v___x_3480_);
v_toCold_3515_ = lean_ctor_get(v___y_3465_, 0);
v_options_3516_ = lean_ctor_get(v_toCold_3515_, 2);
v_hasTrace_3517_ = lean_ctor_get_uint8(v_options_3516_, sizeof(void*)*1);
if (v_hasTrace_3517_ == 0)
{
lean_dec(v_a_3499_);
lean_del_object(v___x_3496_);
lean_dec(v_a_3493_);
lean_del_object(v___x_3489_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
goto v___jp_3468_;
}
else
{
lean_object* v_inheritedTraceOptions_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; uint8_t v___x_3521_; 
v_inheritedTraceOptions_3518_ = lean_ctor_get(v_toCold_3515_, 11);
v___x_3519_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1));
v___x_3520_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2);
v___x_3521_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3518_, v_options_3516_, v___x_3520_);
if (v___x_3521_ == 0)
{
lean_dec(v_a_3499_);
lean_del_object(v___x_3496_);
lean_dec(v_a_3493_);
lean_del_object(v___x_3489_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
goto v___jp_3468_;
}
else
{
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3525_; 
v___x_3522_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4);
v___x_3523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3523_, 0, v_a_3493_);
if (v_isShared_3497_ == 0)
{
lean_ctor_set_tag(v___x_3496_, 7);
lean_ctor_set(v___x_3496_, 1, v___x_3523_);
lean_ctor_set(v___x_3496_, 0, v___x_3522_);
v___x_3525_ = v___x_3496_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3522_);
lean_ctor_set(v_reuseFailAlloc_3541_, 1, v___x_3523_);
v___x_3525_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
lean_object* v___x_3526_; lean_object* v___x_3528_; 
v___x_3526_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6);
if (v_isShared_3490_ == 0)
{
lean_ctor_set_tag(v___x_3489_, 7);
lean_ctor_set(v___x_3489_, 1, v___x_3526_);
lean_ctor_set(v___x_3489_, 0, v___x_3525_);
v___x_3528_ = v___x_3489_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v___x_3525_);
lean_ctor_set(v_reuseFailAlloc_3540_, 1, v___x_3526_);
v___x_3528_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3529_, 0, v_a_3499_);
v___x_3530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3528_);
lean_ctor_set(v___x_3530_, 1, v___x_3529_);
v___x_3531_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_3519_, v___x_3530_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_dec_ref_known(v___x_3531_, 1);
goto v___jp_3468_;
}
else
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3534_ = v___x_3531_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3531_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3537_; 
if (v_isShared_3535_ == 0)
{
v___x_3537_ = v___x_3534_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3532_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
}
}
}
}
}
v___jp_3503_:
{
lean_object* v___x_3505_; 
if (v_isShared_3486_ == 0)
{
lean_ctor_set(v___x_3485_, 1, v_a_3499_);
lean_ctor_set(v___x_3485_, 0, v_a_3493_);
v___x_3505_ = v___x_3485_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v_a_3493_);
lean_ctor_set(v_reuseFailAlloc_3512_, 1, v_a_3499_);
v___x_3505_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
lean_object* v___x_3507_; 
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 0, v___x_3505_);
v___x_3507_ = v___x_3480_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v___x_3505_);
v___x_3507_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
lean_object* v___x_3509_; 
if (v_isShared_3502_ == 0)
{
lean_ctor_set(v___x_3501_, 0, v___x_3507_);
v___x_3509_ = v___x_3501_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v___x_3507_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
}
}
}
else
{
lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3550_; 
lean_del_object(v___x_3496_);
lean_dec(v_mvarId_3494_);
lean_dec(v_a_3493_);
lean_del_object(v___x_3489_);
lean_dec(v_mvarId_3487_);
lean_del_object(v___x_3485_);
lean_del_object(v___x_3480_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
v_a_3543_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3545_ = v___x_3498_;
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3498_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3548_; 
if (v_isShared_3546_ == 0)
{
v___x_3548_ = v___x_3545_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_a_3543_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
}
}
else
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
lean_del_object(v___x_3489_);
lean_dec(v_mvarId_3487_);
lean_del_object(v___x_3485_);
lean_dec(v_snd_3483_);
lean_del_object(v___x_3480_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec(v_fvarId_3462_);
v_a_3553_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3555_ = v___x_3492_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3492_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3565_; lean_object* v___x_3567_; 
lean_dec(v_a_3474_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec(v_fvarId_3462_);
v___x_3565_ = lean_box(0);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 0, v___x_3565_);
v___x_3567_ = v___x_3476_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v___x_3565_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
else
{
lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3577_; 
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec(v_fvarId_3462_);
v_a_3570_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3572_ = v___x_3473_;
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_a_3570_);
lean_dec(v___x_3473_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3575_; 
if (v_isShared_3573_ == 0)
{
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3570_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
}
else
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3585_; 
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec(v_fvarId_3462_);
lean_dec(v_hName_x3f_3461_);
lean_dec(v_mvarId_3460_);
v_a_3578_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3580_ = v___x_3471_;
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v___x_3471_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3583_; 
if (v_isShared_3581_ == 0)
{
v___x_3583_ = v___x_3580_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_a_3578_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
v___jp_3468_:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3469_ = lean_box(0);
v___x_3470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3469_);
return v___x_3470_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___lam__0___boxed(lean_object* v___x_3586_, lean_object* v_mvarId_3587_, lean_object* v_hName_x3f_3588_, lean_object* v_fvarId_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
lean_object* v_res_3595_; 
v_res_3595_ = l_Lean_Meta_splitIfLocalDecl_x3f___lam__0(v___x_3586_, v_mvarId_3587_, v_hName_x3f_3588_, v_fvarId_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f(lean_object* v_mvarId_3596_, lean_object* v_fvarId_3597_, lean_object* v_hName_x3f_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_){
_start:
{
lean_object* v___x_3604_; lean_object* v___f_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; 
lean_inc(v_fvarId_3597_);
v___x_3604_ = l_Lean_mkFVar(v_fvarId_3597_);
lean_inc(v_mvarId_3596_);
v___f_3605_ = lean_alloc_closure((void*)(l_Lean_Meta_splitIfLocalDecl_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3605_, 0, v___x_3604_);
lean_closure_set(v___f_3605_, 1, v_mvarId_3596_);
lean_closure_set(v___f_3605_, 2, v_hName_x3f_3598_);
lean_closure_set(v___f_3605_, 3, v_fvarId_3597_);
v___x_3606_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3606_, 0, lean_box(0));
lean_closure_set(v___x_3606_, 1, v_mvarId_3596_);
lean_closure_set(v___x_3606_, 2, v___f_3605_);
v___x_3607_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v___x_3606_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___boxed(lean_object* v_mvarId_3608_, lean_object* v_fvarId_3609_, lean_object* v_hName_x3f_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_){
_start:
{
lean_object* v_res_3616_; 
v_res_3616_ = l_Lean_Meta_splitIfLocalDecl_x3f(v_mvarId_3608_, v_fvarId_3609_, v_hName_x3f_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_);
lean_dec(v_a_3614_);
lean_dec_ref(v_a_3613_);
lean_dec(v_a_3612_);
lean_dec_ref(v_a_3611_);
return v_res_3616_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3637_ = lean_unsigned_to_nat(3526097586u);
v___x_3638_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_));
v___x_3639_ = l_Lean_Name_num___override(v___x_3638_, v___x_3637_);
return v___x_3639_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3641_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_));
v___x_3642_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3643_ = l_Lean_Name_str___override(v___x_3642_, v___x_3641_);
return v___x_3643_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3645_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_));
v___x_3646_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3647_ = l_Lean_Name_str___override(v___x_3646_, v___x_3645_);
return v___x_3647_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3648_ = lean_unsigned_to_nat(2u);
v___x_3649_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3650_ = l_Lean_Name_num___override(v___x_3649_, v___x_3648_);
return v___x_3650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3652_; uint8_t v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3652_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9));
v___x_3653_ = 0;
v___x_3654_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3655_ = l_Lean_registerTraceClass(v___x_3652_, v___x_3653_, v___x_3654_);
return v___x_3655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2____boxed(lean_object* v_a_3656_){
_start:
{
lean_object* v_res_3657_; 
v_res_3657_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_();
return v_res_3657_;
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
